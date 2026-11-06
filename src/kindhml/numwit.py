"""Numeric witnesses of existentials (DESIGN.md, Sect. 7.8, "Numeric witnesses", 2026-11-07).

A property `forall x1..xm . exists y1..yk . psi`, with numbers y, holds if its instance
`forall x1..xm . psi[y := t]` does, for terms t (introduction of the existentials). The
instance has no existential, so it may have a cutoff where the property has none (additivity
P1_true: `forall c1 c2 . exists c3 v12 v3 . forall a . ...`, an address universal under the
existentials); a proof of it for every n then proves the property for every n, as for the
instances of an existential over a method (`witness.py`). The terms are over the universal
numbers x and the numeric fields, evaluated at the state of the existentials: a y under d
modalities in psi is replaced by old^d(t).

The terms come from samples: reachable states of the fuzzer, with random values for x. A
storage variable (y with an equality y == e in psi, e without the y's, under calls with
arguments over x and the other y's) takes at a sample the value of e after those calls, run
by the reference interpreter; the other y's (e.g. the argument of a call) get candidate
terms, tried in turn, and an assignment is kept if psi holds at every sample (bounded
evaluation). For each storage variable, the simplest term with its values at every sample is
taken. The choice is a heuristic: the instance is proved or refuted by its own check.
"""

from __future__ import annotations

import itertools
import random
from dataclasses import replace
from typing import Dict, List, Optional, Tuple

from . import pretty
from . import syntax as S
from .reference import FormulaEvaluator, Revert, Tx

SAMPLES = 6                 # the samples (states and values of the universal numbers)
STATES = 40                 # the states drawn, of which the SAMPLES most informative are kept
MAX_FREE = 2                # the existentials without an equality that get candidate terms
# the values of the universal numbers at the samples: not -1, 0, 1, with which many terms
# agree (division: with v == 0, every c3 is a witness)
NUMBERS = [-4, -3, -2, 2, 3, 4, 5, 6, 7]


def site(formula: S.Expr) -> Optional[Tuple[List[S.Quant], List[S.Quant], S.Expr]]:
    """The universal quantifiers of the prefix of `formula`, the block of existentials over
    numbers that follows them, and the rest (psi); None without such a block."""
    univ: List[S.Quant] = []
    e = formula
    while isinstance(e, S.Quant) and e.kind == "forall":
        univ.append(e)
        e = e.body
    block: List[S.Quant] = []
    while isinstance(e, S.Quant) and e.kind == "exists" and S.is_num(e.type):
        block.append(e)
        e = e.body
    return (univ, block, e) if block else None


def _uses(e, names: set) -> bool:
    """Whether e has a quantified variable of `names`."""
    if isinstance(e, S.QVar):
        return e.name in names
    for n in getattr(e, "__dataclass_fields__", ()):
        v = getattr(e, n)
        for x in (v if isinstance(v, tuple) else (v,)):
            if isinstance(x, S.Expr) and _uses(x, names):
                return True
    return False


def _definitions(psi: S.Expr, ys: set) -> Dict[str, Tuple[List[object], S.Expr]]:
    """For each y with an equality y == e (e without the y's): the path to it (the modalities
    and the address quantifiers around it, outermost first) and e."""
    out: Dict[str, Tuple[List[object], S.Expr]] = {}

    def walk(e, path):
        if isinstance(e, S.BinOp) and e.op == "==":
            for y, other in ((e.left, e.right), (e.right, e.left)):
                if isinstance(y, S.QVar) and y.name in ys and y.name not in out \
                        and not _uses(other, ys):
                    out[y.name] = (list(path), other)
        if isinstance(e, S.Modal):
            walk(e.body, path + [e])
            return
        if isinstance(e, S.Quant):
            walk(e.body, path + [e])
            return
        for n in getattr(e, "__dataclass_fields__", ()):
            v = getattr(e, n)
            for x in (v if isinstance(v, tuple) else (v,)):
                if isinstance(x, S.Expr):
                    walk(x, path)
    walk(psi, [])
    return out


def _value_after(ev: FormulaEvaluator, path: list, e: S.Expr, st, env: dict):
    """The value of e after the calls of `path` from st (an address quantifier of the path
    takes the first user); None if a call has a method variable, or the evaluation fails."""
    seq, env = [st], dict(env)
    try:
        for m in path:
            if isinstance(m, S.Quant):
                if m.type != S.ADDRESS:
                    return None
                env[m.var] = ev.system.users[0]
                continue
            if not isinstance(m.proc, S.ProcConst):
                return None
            method = ev.eval(m.proc, seq, env)
            params = ev.system.params_of(*method)
            args = {v.name: ev.eval(a, seq, env) for v, a in zip(params, m.args)}
            tx = Tx(ev.eval(m.sender, seq, env), m.contract, method, args,
                    ev.eval(m.value, seq, env), ev.eval(m.blocks, seq, env))
            seq = [ev.interp.step(seq[0], tx)] + seq
        return ev.eval(e, seq, env)
    except (Revert, KeyError, ZeroDivisionError, TypeError, ValueError, IndexError):
        return None


def _terms(items: List[S.Expr]) -> List[S.Expr]:
    """Candidate terms over `items`, the simplest first: the items, 0 and 1, then sums,
    differences and products of two, then sums and products of three."""
    out: List[S.Expr] = list(items) + [S.IntLit(0), S.IntLit(1)]
    for a, b in itertools.combinations_with_replacement(items, 2):
        out += [S.BinOp("+", a, b), S.BinOp("*", a, b)]
    for a, b in itertools.permutations(items, 2):
        out.append(S.BinOp("-", a, b))
    for a, b, c in itertools.combinations(items, 3):
        out += [S.BinOp("+", S.BinOp("+", a, b), c), S.BinOp("*", S.BinOp("*", a, b), c)]
    return out


def _old(e: S.Expr, d: int) -> S.Expr:
    for _ in range(d):
        e = S.Old(e)
    return e


def _substitute(e, terms: Dict[str, S.Expr], depth: int = 0):
    """e with each y of `terms` replaced by old^d(its term), d the modalities above it."""
    if isinstance(e, S.QVar) and e.name in terms:
        return _old(terms[e.name], depth)
    if not hasattr(e, "__dataclass_fields__") or isinstance(e, (S.Type, S.MapType)):
        return e
    changes = {}
    for name in e.__dataclass_fields__:
        v = getattr(e, name)
        deeper = depth + (1 if isinstance(e, S.Modal) and name == "body" else 0)
        if isinstance(v, tuple):
            new = tuple(_substitute(x, terms, deeper) if isinstance(x, S.Expr) else x
                        for x in v)
            if any(a is not b for a, b in zip(new, v)):
                changes[name] = new
        elif isinstance(v, S.Expr):
            new = _substitute(v, terms, deeper)
            if new is not v:
                changes[name] = new
    return replace(e, **changes) if changes else e


def _close(e: S.Expr, terms: Dict[str, S.Expr]) -> S.Expr:
    """A term with the y's in it replaced by their terms (all at the same state)."""
    return _substitute(e, terms) if _uses(e, set(terms)) else e


def instances(program: S.Program, prop: S.Property, fuzzer,
              limit: int = 4) -> List[Tuple[str, S.Property]]:
    """The instances of the first block of existentials over numbers of `prop` (module
    docstring), at most `limit`, each with a description; [] if none is found."""
    found = site(prop.formula)
    if found is None:
        return []
    univ, block, psi = found
    ys = [q.var for q in block]
    nums = [q for q in univ if S.is_num(q.type)]
    if any(not S.is_num(q.type) for q in univ):
        return []                       # an address universal before the existentials
    defs = _definitions(psi, set(ys))
    free = [y for y in ys if y not in defs]
    if len(free) > MAX_FREE:
        return []
    system = fuzzer.system
    ev = FormulaEvaluator(system, range(-1, 4))
    rnd = random.Random(f"numwit:{prop.name}")
    fields = [S.Field(c.name, f.name) for c in program.contracts for f in c.fields
              if S.is_num(f.type)]
    # the most informative states: the most numeric fields outside -1, 0, 1, all different
    states = {}
    for _ in range(STATES):
        st = None
        for _, st in fuzzer.traces(f"numwit:{prop.name}"):
            pass
        if st is not None and all(st.constructed.values()):
            key = tuple(st.fields[(f.contract, f.name)] for f in fields)
            states.setdefault(key, st)
    ranked = sorted(states.items(), key=lambda kv: -sum(1 for v in kv[0]
                                                         if v not in (-1, 0, 1)))
    points = [(st, {q.var: rnd.choice(NUMBERS) for q in nums})
              for _, st in ranked[:SAMPLES]]
    if len(points) < 2:
        return []
    base = [S.QVar(q.var, q.type) for q in nums] + fields
    block_type = {q.var: q.type for q in block}

    def values(term, env_of) -> Optional[tuple]:
        try:
            return tuple(ev.eval(term, [st], env_of(i)) for i, (st, _) in enumerate(points))
        except (KeyError, ZeroDivisionError, TypeError, ValueError, IndexError):
            return None

    out: List[Tuple[str, S.Property]] = []
    free_terms = _terms(base)
    seen_free: set = set()
    for choice in itertools.product(free_terms, repeat=len(free)):
        assign = dict(zip(free, choice))
        vec = tuple(values(t, lambda i: points[i][1]) for t in choice)
        if None in vec or vec in seen_free:
            continue
        seen_free.add(vec)
        envs = [dict(env, **{y: vec[j][i] for j, y in enumerate(free)})
                for i, (_, env) in enumerate(points)]
        # the storage variables, in the order of the block (one may use another's value)
        ok = True
        for y in ys:
            if y in assign:
                continue
            path, e = defs[y]
            vals = []
            for i, (st, _) in enumerate(points):
                v = _value_after(ev, path, e, st, envs[i])
                if v is None:
                    ok = False
                    break
                vals.append(v)
            if not ok:
                break
            for i, v in enumerate(vals):
                envs[i][y] = v
        if not ok:
            continue
        try:
            if not all(ev.eval(psi, [st], envs[i]) for i, (st, _) in enumerate(points)):
                continue
        except (KeyError, ZeroDivisionError, TypeError, ValueError, IndexError):
            continue
        # the simplest term of each storage variable with its values at every sample
        items = base + [S.QVar(y, block_type[y]) for y in free]
        terms = dict(assign)
        for y in ys:
            if y in terms:
                continue
            want = tuple(envs[i][y] for i in range(len(points)))
            match = next((t for t in _terms(items)
                          if values(t, lambda i: envs[i]) == want), None)
            if match is None:
                ok = False
                break
            terms[y] = match
        if not ok:
            continue
        closed = {y: _close(t, {x: terms[x] for x in free}) for y, t in terms.items()}
        body = _substitute(psi, closed)
        for q in reversed(univ):
            body = replace(q, body=body)
        text = ", ".join(f"{y} := {pretty.expr(closed[y])}" for y in ys)
        out.append((text, S.Property(f"{prop.name}__n{len(out)}", body, None, prop.pos)))
        if len(out) >= limit:
            break
    return out
