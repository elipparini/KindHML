"""Invariant-assisted checking (DESIGN.md, "Invariants").

Kind 2 checks a rule on the reachable states of (Init, Trans), by BMC and k-induction through
Trans. When Trans is nonlinear and the rule holds only because of facts about the reachable
states (e.g. nonnegative reserves), this often fails. The checks below avoid the transition
system: each is one Kind 2 run on free values (a node without `pre`), i.e. one SMT query.

* An invariant I is proved inductive by two checks: Init ⇒ I, for any initial balances and
  block number; and C(s) ⇒ I(Trans(s, t)) for every state s and transaction t, where C is
  the conjunction of the candidate invariants. Candidates refuted by a check are dropped
  until the remaining set is inductive (Houdini). The built-in lemma (balances are
  nonnegative) is a candidate too.
* A rule φ is checked on a free state s: C(s) ⇒ ((∧_C constructed_C) → Φ(φ))(s), with C the
  proved invariants. If it holds, φ holds in every reachable state (they all satisfy C).
  If it fails, the counterexample s* may be unreachable; `reach_check(s*)` asks BMC
  whether s* is reachable, which gives a counterexample of φ.

An invariant itself is required in every reachable state, including those before the
construction of the contracts, so its formula has no guard on construction.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Callable, Dict, List, Sequence, Tuple

from . import lustre as L
from . import syntax as S
from .encode_formula import FormulaEncoder
from .encode_trans import ST, TX, Encoder
from .lustre_subst import eq
from .model import System

StateFormula = Callable[[L.LExpr], L.LExpr]


class Checks:
    def __init__(self, program: S.Program, n_users: int, mode: str, expand: Sequence[str]):
        self.program = program
        self.enc = Encoder(System.make(program, n_users))
        self.fenc = FormulaEncoder(self.enc, mode, tuple(expand))
        lemmas = [(n, (lambda st, e=e: self.fenc.inliner.run(e, {"s": st})))
                  for n, e in self.enc.lemmas()]
        mine = [(r.name, (lambda st, r=r: self.fenc.state_formula(r.formula, st)))
                for r in program.rules if r.invariant]
        # the built-in lemmas hold in every system (DESIGN.md, "Lemmas"): assumed, not checked
        self.axioms: List[str] = [n for n, _ in lemmas]
        self.candidates: Dict[str, StateFormula] = dict(lemmas + mine)

    def _program(self) -> L.Program:
        """Types and functions of the encoding, without the main node."""
        prog, main = self.enc.program()
        prog.decls.remove(main)
        return prog

    @staticmethod
    def _render(prog: L.Program, node: L.Function) -> str:
        node.node = True
        prog.decls.append(node)
        return prog.render()

    def init_check(self, names: List[str]) -> str:
        """Properties `init_<I>`: I holds in the initial state."""
        prog, inputs = self._program(), self.enc.init_inputs()
        s = L.Var("s")
        node = L.Function(
            "main", inputs, [], locals=[("s", ST)], asserts=self._init_assumptions(),
            equations=[("s", L.call("init", *[L.Var(n) for n, _ in inputs]))],
            properties=[(f"init_{n}", self.candidates[n](s)) for n in names],
            comment="Init => I, for every candidate invariant I")
        return self._render(prog, node)

    def _init_assumptions(self) -> List[L.LExpr]:
        _, main = self.enc.program()
        return list(main.asserts)

    def step_check(self, names: List[str]) -> str:
        """Properties `step_<I>`: C(s) ⇒ I(Trans(s, t)), with C the conjunction of `names`
        and of the axioms."""
        prog, s, s1 = self._program(), L.Var("s"), L.Var("s1")
        assumption = self._conj(self.axioms + names, s)
        node = L.Function(
            "main", [("s", ST), ("t", TX)], [], locals=[("s1", ST)],
            equations=[("s1", L.call("trans", s, L.Var("t")))],
            properties=[(f"step_{n}", L.op("=>", assumption, self.candidates[n](s1)))
                        for n in names],
            comment="C(s) => I(Trans(s, t)), for every candidate invariant I")
        return self._render(prog, node)

    def rule_check(self, rule: S.Rule, invariants: List[str]) -> str:
        """The rule on a free state satisfying the proved invariants that concern it.

        The invariants are the premise of the property, not Lustre assertions (with
        assertions, Kind 2 did not prove Swap_reversibility of the swap pool in 30 s; as a
        premise, in 1 s). Only the invariants that share state variables with the rule,
        transitively, are included: an irrelevant one can change the logic of the query
        (the balance lemma over int, in a query over nonlinear reals, made z3 time out)."""
        prog, s = self._program(), L.Var("s")
        prop = (self.fenc.state_formula(rule.formula, s) if rule.invariant
                else self.fenc.rule(rule, s))
        relevant = self.relevant(prop, invariants)
        node = L.Function(
            "main", [("s", ST)], [],
            properties=[(rule.name, L.op("=>", self._conj(relevant, s), prop))],
            comment=f"{rule.name} on every state satisfying the invariants"
                    f" {', '.join(relevant) or '(none)'}")
        return self._render(prog, node)

    def relevant(self, prop: L.LExpr, invariants: List[str]) -> List[str]:
        """The invariants connected to `prop` by shared fields of the state s."""
        s = L.Var("s")
        fields = {n: state_fields(self.candidates[n](s)) for n in invariants}
        used, chosen, changed = state_fields(prop), [], True
        while changed:
            changed = False
            for n in invariants:
                if n not in chosen and fields[n] & used:
                    chosen.append(n)
                    used |= fields[n]
                    changed = True
        return [n for n in invariants if n in chosen]

    def _conj(self, names: List[str], state: L.LExpr) -> L.LExpr:
        return L.conj([self.candidates[n](state) for n in names])

    def reach_check(self, state: Dict[str, L.LExpr]) -> str:
        """Property `unreachable`: the state s of the transition system never equals the
        given values (a map from paths `s.f` or `s.f.k_a` to constants)."""
        prog, main = self.enc.program()
        main.properties = [("unreachable", L.neg(L.conj(
            [eq(_path(p), v) for p, v in sorted(state.items())])))]
        return prog.render()


def state_fields(e: L.LExpr, var: str = "s") -> set:
    """The fields f of `var` read in e (as var.f or var.f.k)."""
    if isinstance(e, L.Proj) and isinstance(e.record, L.Var) and e.record.name == var:
        return {e.field}
    out: set = set()
    for name in getattr(e, "__dataclass_fields__", ()):
        v = getattr(e, name)
        for x in (v if isinstance(v, tuple) else (v,)):
            if isinstance(x, tuple):
                x = x[-1]                     # (name, value) of a record literal
            if isinstance(x, L.LExpr):
                out |= state_fields(x, var)
    return out


def _path(name: str) -> L.LExpr:
    """`s.f.k` as nested projections."""
    parts = name.split(".")
    e: L.LExpr = L.Var(parts[0])
    for p in parts[1:]:
        e = L.Proj(e, p)
    return e


def state_values(counterexample: list, var: str = "s") -> Dict[str, L.LExpr]:
    """The values of the input record `var` at step 0 of a Kind 2 counterexample (JSON),
    by path. Reals are {"num": n, "den": d}; enum constants are strings."""
    out: Dict[str, L.LExpr] = {}
    for block in counterexample or []:
        for stream in block.get("streams", []):
            name = stream["name"]
            if not (name == var or name.startswith(var + ".")):
                continue
            values = dict((int(k), v) for k, v in stream.get("instantValues", []))
            if 0 in values:
                out[name] = constant(values[0])
    return out


def constant(v) -> L.LExpr:
    if isinstance(v, bool):
        return L.Bool(v)
    if isinstance(v, int):
        return L.Int(v)
    if isinstance(v, dict) and set(v) == {"num", "den"}:
        return L.Real(Fraction(v["num"], v["den"]))
    if isinstance(v, str):
        return L.Var(v)
    raise ValueError(f"unexpected value {v!r} in a counterexample")


def describe_state(state: Dict[str, L.LExpr]) -> str:
    return ", ".join(f"{p[2:]} = {L.render(v)}" for p, v in sorted(state.items()))


def names_of(results) -> Tuple[set, set]:
    """(valid, invalid) property names of a Kind 2 output."""
    valid = {p.name for p in results if p.status == "valid"}
    invalid = {p.name for p in results if p.status == "invalid"}
    return valid, invalid
