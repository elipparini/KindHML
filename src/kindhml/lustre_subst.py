"""Substitution, simplification, and inlining on the Lustre AST.

Used to write the transition relation inside properties as scalar equations, without calls
to Lustre functions (see `encode_formula.py`, mode "levels").

Simplifications: projections of record literals and of if-then-else, equalities between enum
constants (names starting with `A_` or `P_`), equalities between record literals (expanded
field by field), and constant conditions.
"""

from __future__ import annotations

import time
from typing import Dict, Optional

from . import lustre as L
from .errors import KindHMLError

# The time limit of the check being encoded (`verify` sets it): the encoders (`Inliner.run`,
# `encode_formula.FormulaEncoder.phi`) raise EncodingTimeout past it, so that a check stops at
# its time limit during an encoding too (the time limit is otherwise only checked between the
# steps of the check).
DEADLINE: Optional[float] = None
_calls = 0


class EncodingTimeout(KindHMLError):
    pass


def tick() -> None:
    """Raises EncodingTimeout past DEADLINE (checked every 256 calls)."""
    global _calls
    _calls += 1
    if DEADLINE is not None and _calls % 256 == 0 and time.time() > DEADLINE:
        raise EncodingTimeout("the encoding of the formula did not end within the time limit")


def free_vars(e: L.LExpr, memo: Optional[dict] = None) -> set:
    """Names of the variables occurring free in e (enum constants excluded). With `memo` (a
    dict, kept by the caller while the nodes live), the results are kept by node identity:
    the terms of nested modalities share subterms, and a traversal as a tree is exponential in
    the depth (the hash of a node also traverses the whole tree, so not by value)."""
    if memo is None:
        return _free_vars(e, None)
    hit = memo.get(id(e))
    if hit is not None and hit[0] is e:
        return hit[1]
    out = _free_vars(e, memo)
    memo[id(e)] = (e, out)
    return out


def _free_vars(e: L.LExpr, memo: Optional[dict]) -> set:
    free_vars = lambda x: globals()["free_vars"](x, memo)
    if isinstance(e, L.Var):
        return set() if is_const(e) else {e.name}
    if isinstance(e, (L.Int, L.Real, L.Bool)):
        return set()
    if isinstance(e, L.Op):
        return set().union(*(free_vars(a) for a in e.args))
    if isinstance(e, L.Ite):
        return free_vars(e.cond) | free_vars(e.then) | free_vars(e.orelse)
    if isinstance(e, L.Call):
        return set().union(set(), *(free_vars(a) for a in e.args))
    if isinstance(e, L.Proj):
        return free_vars(e.record)
    if isinstance(e, L.Record):
        return set().union(set(), *(free_vars(v) for _, v in e.fields))
    if isinstance(e, L.Quant):
        return free_vars(e.body) - {n for n, _ in e.vars}
    if isinstance(e, (L.Arrow,)):
        return free_vars(e.init) | free_vars(e.then)
    if isinstance(e, L.Pre):
        return free_vars(e.arg)
    raise TypeError(f"unknown Lustre expression {e!r}")


def is_const(e: L.LExpr) -> bool:
    return isinstance(e, L.Var) and (e.name.startswith("A_") or e.name.startswith("P_"))


def eq(a: L.LExpr, b: L.LExpr) -> L.LExpr:
    if isinstance(a, L.Record) and isinstance(b, L.Record):
        fb = dict(b.fields)
        return L.conj([eq(v, fb[n]) for n, v in a.fields])
    if isinstance(a, L.Record) or isinstance(b, L.Record):
        rec, other = (a, b) if isinstance(a, L.Record) else (b, a)
        return L.conj([eq(v, proj(other, n)) for n, v in rec.fields])
    if a == b:
        return L.TRUE
    if is_const(a) and is_const(b):
        return L.FALSE
    if isinstance(a, L.Bool) and isinstance(b, L.Bool):
        return L.Bool(a.value == b.value)
    if isinstance(a, (L.Int, L.Real)) and type(a) is type(b):
        return L.Bool(a.value == b.value)
    return L.Op("=", (a, b))


def proj(r: L.LExpr, f: str) -> L.LExpr:
    if isinstance(r, L.Record):
        return dict(r.fields)[f]
    if isinstance(r, L.Ite):
        return ite(r.cond, proj(r.then, f), proj(r.orelse, f))
    return L.Proj(r, f)


def ite(c: L.LExpr, t: L.LExpr, e: L.LExpr) -> L.LExpr:
    if isinstance(t, L.Record) and isinstance(e, L.Record) and c not in (L.TRUE, L.FALSE):
        fe = dict(e.fields)
        return L.Record(t.type, tuple((n, ite(c, v, fe[n])) for n, v in t.fields))
    if t == L.TRUE and e == L.FALSE:
        return c
    return L.ite(c, t, e)


def op(o: str, args) -> L.LExpr:
    if o == "=":
        return eq(*args)
    if o == "<>":
        return L.neg(eq(*args))
    if o == "and":
        return L.conj(list(args))
    if o == "or":
        return L.disj(list(args))
    if o == "not":
        return L.neg(args[0])
    if o == "=>":
        a, b = args
        if a == L.TRUE:
            return b
        if a == L.FALSE or b == L.TRUE:
            return L.TRUE
    return L.Op(o, tuple(args))


class Inliner:
    """Substitutes variables and inlines calls to the given Lustre functions."""

    def __init__(self, functions: Dict[str, L.Function]):
        self.functions = functions

    def run(self, e: L.LExpr, env: Dict[str, L.LExpr]) -> L.LExpr:
        tick()
        r = lambda x: self.run(x, env)
        if isinstance(e, L.Var):
            return env.get(e.name, e)
        if isinstance(e, (L.Int, L.Real, L.Bool)):
            return e
        if isinstance(e, L.Op):
            return op(e.op, [r(a) for a in e.args])
        if isinstance(e, L.Ite):
            c = r(e.cond)
            if c == L.TRUE:
                return r(e.then)
            if c == L.FALSE:
                return r(e.orelse)
            return ite(c, r(e.then), r(e.orelse))
        if isinstance(e, L.Proj):
            return proj(r(e.record), e.field)
        if isinstance(e, L.Record):
            return L.Record(e.type, tuple((n, r(v)) for n, v in e.fields))
        if isinstance(e, L.Call):
            args = [r(a) for a in e.args]
            f = self.functions.get(e.fn)
            if f is None:
                return L.Call(e.fn, tuple(args))
            local = {n: a for (n, _), a in zip(f.inputs, args)}
            for n, body in f.equations:
                local[n] = self.run(body, local)
            return local[f.outputs[0][0]]
        if isinstance(e, L.Quant):
            return L.Quant(e.kind, e.vars, r(e.body))
        raise NotImplementedError(f"cannot inline {e!r}")
