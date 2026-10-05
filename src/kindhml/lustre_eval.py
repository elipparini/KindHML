"""Evaluation of closed Lustre expressions of the fragment produced by the encoder
(records, enums, if-then-else, calls to functions). Quantifiers and temporal operators are
not supported. Used by the tests to run `trans` on concrete values without Kind 2.

Enum constants evaluate to their names, records to dicts, reals to Fractions; `div` and
`mod` follow SMT-LIB.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Dict

from . import lustre as L
from .reference import real_domain, smt_div, smt_mod

_OPS = {
    "and": lambda a, b: a and b, "or": lambda a, b: a or b, "=>": lambda a, b: (not a) or b,
    "=": lambda a, b: a == b, "<>": lambda a, b: a != b, "<": lambda a, b: a < b,
    "<=": lambda a, b: a <= b, ">": lambda a, b: a > b, ">=": lambda a, b: a >= b,
    "+": lambda a, b: a + b, "-": lambda a, b: a - b, "*": lambda a, b: a * b,
    "div": smt_div, "mod": smt_mod, "/": lambda a, b: Fraction(a) / b,
}


class Evaluator:
    def __init__(self, program: L.Program, int_domain=None):
        """`int_domain`: if given, quantifiers over int range over it, and over real over
        `real_domain(int_domain)` (bounded evaluation, for tests); quantifiers over enums and
        bool range over all their values."""
        self.functions: Dict[str, L.Function] = {
            d.name: d for d in program.decls if isinstance(d, L.Function) and not d.node}
        self.domains = {"bool": [False, True]}
        for d in program.decls:
            if isinstance(d, L.EnumType):
                self.domains[d.name] = list(d.constants)
        if int_domain is not None:
            self.domains["int"] = list(int_domain)
            self.domains["real"] = real_domain(int_domain)

    def call(self, name: str, args: list):
        f = self.functions[name]
        env = {n: v for (n, _), v in zip(f.inputs, args)}
        for n, e in f.equations:          # equations are emitted in dependency order
            env[n] = self.eval(e, env)
        return env[f.outputs[0][0]]

    def eval(self, e: L.LExpr, env: dict):
        if isinstance(e, L.Var):
            return env.get(e.name, e.name)
        if isinstance(e, (L.Int, L.Real, L.Bool)):
            return e.value
        if isinstance(e, L.Op):
            args = [self.eval(a, env) for a in e.args]
            if len(args) == 1:
                return (not args[0]) if e.op == "not" else -args[0]
            if e.op in ("div", "mod", "/") and args[1] == 0:
                return 0              # unspecified in SMT-LIB; the encoding never relies on it
            return _OPS[e.op](*args)
        if isinstance(e, L.Ite):
            return self.eval(e.then if self.eval(e.cond, env) else e.orelse, env)
        if isinstance(e, L.Call):
            if e.fn == "real":        # conversion int -> real
                return Fraction(self.eval(e.args[0], env))
            return self.call(e.fn, [self.eval(a, env) for a in e.args])
        if isinstance(e, L.Proj):
            return self.eval(e.record, env)[e.field]
        if isinstance(e, L.Record):
            return {n: self.eval(v, env) for n, v in e.fields}
        if isinstance(e, L.Quant):
            return self._quant(e, list(e.vars), env)
        raise NotImplementedError(f"cannot evaluate {e!r}")

    def _quant(self, e: L.Quant, vars_, env) -> bool:
        if not vars_:
            return self.eval(e.body, env)
        (name, typ), rest = vars_[0], vars_[1:]
        results = (self._quant(e, rest, {**env, name: v}) for v in self.domains[typ])
        return all(results) if e.kind == "forall" else any(results)
