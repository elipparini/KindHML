"""Evaluation of closed Lustre expressions of the fragment produced by the encoder
(records, enums, if-then-else, calls to functions). Quantifiers and temporal operators are
not supported. Used by the tests to run `trans` on concrete values without Kind 2.

Enum constants evaluate to their names, records to dicts; `div` and `mod` follow SMT-LIB.
"""

from __future__ import annotations

from typing import Dict

from . import lustre as L
from .reference import smt_div, smt_mod

_OPS = {
    "and": lambda a, b: a and b, "or": lambda a, b: a or b, "=>": lambda a, b: (not a) or b,
    "=": lambda a, b: a == b, "<>": lambda a, b: a != b, "<": lambda a, b: a < b,
    "<=": lambda a, b: a <= b, ">": lambda a, b: a > b, ">=": lambda a, b: a >= b,
    "+": lambda a, b: a + b, "-": lambda a, b: a - b, "*": lambda a, b: a * b,
    "div": smt_div, "mod": smt_mod,
}


class Evaluator:
    def __init__(self, program: L.Program):
        self.functions: Dict[str, L.Function] = {
            d.name: d for d in program.decls if isinstance(d, L.Function) and not d.node}

    def call(self, name: str, args: list):
        f = self.functions[name]
        env = {n: v for (n, _), v in zip(f.inputs, args)}
        for n, e in f.equations:          # equations are emitted in dependency order
            env[n] = self.eval(e, env)
        return env[f.outputs[0][0]]

    def eval(self, e: L.LExpr, env: dict):
        if isinstance(e, L.Var):
            return env.get(e.name, e.name)
        if isinstance(e, (L.Int, L.Bool)):
            return e.value
        if isinstance(e, L.Op):
            args = [self.eval(a, env) for a in e.args]
            if len(args) == 1:
                return (not args[0]) if e.op == "not" else -args[0]
            if e.op in ("div", "mod") and args[1] == 0:
                return 0              # unspecified in SMT-LIB; the encoding never relies on it
            return _OPS[e.op](*args)
        if isinstance(e, L.Ite):
            return self.eval(e.then if self.eval(e.cond, env) else e.orelse, env)
        if isinstance(e, L.Call):
            return self.call(e.fn, [self.eval(a, env) for a in e.args])
        if isinstance(e, L.Proj):
            return self.eval(e.record, env)[e.field]
        if isinstance(e, L.Record):
            return {n: self.eval(v, env) for n, v in e.fields}
        raise NotImplementedError(f"cannot evaluate {e!r}")
