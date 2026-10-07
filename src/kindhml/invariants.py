"""Invariant-assisted checking (DESIGN.md, "Invariants").

Kind 2 checks a rule on the reachable states of (Init, Trans), by BMC and k-induction through
Trans. When Trans is nonlinear and the rule holds only because of facts about the reachable
states (e.g. nonnegative reserves), this often fails. The checks below avoid the transition
system: each is one Kind 2 run on free values (a node without `pre`), i.e. one SMT query.

* Invariants, like rules, are required in the states where all contracts are constructed:
  (∧_C constructed_C) → I. So they hold trivially in the initial states, and a set C of
  candidates is inductive if, for every procedure f (constructors included),
  C(s) ⇒ C(Trans(s, t)) for every state s and call t of f (`step_conj_checks`;
  `step_check` with one property per candidate). Candidates refuted are dropped until the
  remaining set is inductive (Houdini, `verify._Invariants`). The built-in facts
  (balances are nonnegative; an unconstructed contract has default fields) are assumed.
* A rule φ is checked on a free state s: C(s) ⇒ ((∧_C constructed_C) → Φ(φ))(s), with C the
  proved invariants. If it holds, φ holds in every reachable state (they all satisfy C).
  If it fails, the counterexample s* may be unreachable; `reach_check(s*)` asks BMC
  whether s* is reachable, which gives a counterexample of φ.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Callable, Dict, List, Optional, Sequence, Tuple

from . import lustre as L
from . import syntax as S
from .concrete import python_value, state_from_values
from .encode_formula import FormulaEncoder
from .encode_trans import ST, TX, Encoder, constructed_var, default_value, field_var
from .lustre_subst import eq
from .model import System
from .reference import FormulaEvaluator, Interpreter, Tx

StateFormula = Callable[[L.LExpr], L.LExpr]


class Checks:
    def __init__(self, program: S.Program, n_users: int, mode: str, expand: Sequence[str]):
        self.program = program
        self.enc = Encoder(System.make(program, n_users))
        self.fenc = FormulaEncoder(self.enc, mode, tuple(expand))
        lemmas = [(n, (lambda st, e=e: self.fenc.inliner.run(e, {"s": st})))
                  for n, e in self.enc.lemmas()]
        # an invariant, like a rule, is required in the states where all contracts are
        # constructed: (∧_C constructed_C) → Φ(I)
        mine = [(r.name, (lambda st, r=r: self.fenc.rule(r, st)))
                for r in program.rules if r.invariant]
        # the built-in lemmas hold in every system (DESIGN.md, "Lemmas"): assumed, not checked
        self.axioms: List[str] = [n for n, _ in lemmas]
        self.candidates: Dict[str, StateFormula] = dict(lemmas + mine)

    def defaults(self, st: L.LExpr) -> L.LExpr:
        """Before C is constructed, the fields of C have their default values: they are
        assigned only by the procedures of C, which require constructed_C, except the
        constructor. Holds in every system; assumed in the step of the invariants, where it
        gives the state from which the constructor starts."""
        system = self.enc.system
        return L.conj([L.op("=>", L.neg(L.proj(st, constructed_var(c.name))),
                            L.conj([eq(L.proj(st, field_var(c.name, f.name)),
                                       default_value(f.type, system)) for f in c.fields]))
                       for c in system.contracts if c.fields])

    def _program(self) -> L.Program:
        """Types and functions of the encoding, without the main node."""
        prog, main = self.enc.program()
        prog.decls.remove(main)
        return prog

    @staticmethod
    def _render(prog: L.Program, node: L.Function) -> str:
        """The program with the check node, whose properties have their universal
        quantifiers in positive position replaced by inputs (`hoist`)."""
        inputs: List[Tuple[str, str]] = []
        node.properties = [(n, hoist(p, inputs)) for n, p in node.properties]
        names = {n for n, _ in node.inputs}
        node.inputs = node.inputs + [v for v in inputs if v[0] not in names]
        node.node = True
        prog.decls.append(node)
        return prog.render()

    def step_conj_checks(self, names: List[str]) -> List[Tuple[str, S.Contract, S.Procedure]]:
        """The step of Houdini, one program per procedure f, with one property: all the
        candidates in `names` hold after any call of f from a state satisfying them,
        C(s) ⇒ Φ(∀a, x̄, v[, δ]. ⟨a : C.f(x̄) $ v @ δ⟩ (constructed → ∧ names))(s). If it is
        refuted, its counterexample identifies the candidates that do not hold after the
        call (`refuted_after`). With one property per candidate, the inlined call is copied
        into every property: on the lending protocol, 71 candidates were not decided in
        64 s; as one conjunction, each procedure takes 1-6 s."""
        conj: S.Expr = S.BoolLit(True)
        for n in names:
            conj = S.BinOp("&&", conj, self.program.rule(n).formula)
        s = L.Var("s")
        premise = L.conj([self._conj(self.axioms + names, s), self.defaults(s)])
        out = []
        for c, p in self.enc.system.methods:
            after = self.fenc.state_formula(self._after(c, p, self._guard(conj)), s)
            node = L.Function("main", [("s", ST)], [],
                              properties=[("step", L.op("=>", premise, after))],
                              comment=f"the candidate invariants after a call of {p.name}")
            out.append((self._render(self._program(), node), c, p))
        return out

    def refuted_after(self, counterexample: list, names: List[str], c: S.Contract,
                      p: S.Procedure) -> set:
        """The candidates false after the call of `p` given by a counterexample of its
        conjunction step: its free state s satisfies all the candidates (the premise), and
        the reference interpreter runs the call, with the arguments of the counterexample
        (inputs after `hoist`), for every sender (the sender is expanded, not an input)."""
        values: Dict[str, object] = {}
        for block in counterexample or []:
            for stream in block.get("streams", []):
                vals = dict((int(k), v) for k, v in stream.get("instantValues", []))
                if 0 in vals:
                    values[stream["name"]] = vals[0]
        system = self.enc.system
        st = state_from_values(values, system, self.enc)
        inputs = {}
        for name, v in values.items():
            if name.startswith("q___") and "_" in name[4:]:
                inputs[name[4:].rsplit("_", 1)[0]] = python_value(v)
        args = {x.name: inputs.get(f"arg_{x.name}", 0) for x in p.params}
        tx = dict(value=inputs.get("value", 0), blocks=inputs.get("blocks", 0))
        interp = Interpreter(system)
        ev = FormulaEvaluator(system, range(-1, 4))
        out = set()
        for sender in system.addresses:
            post = interp.step(st, Tx(sender, c.name, (c.name, p.name), args, **tx))
            if not all(post.constructed.values()):
                continue
            for n in names:
                try:
                    if not ev.holds(self.program.rule(n).formula, [post]):
                        out.add(n)
                except (ZeroDivisionError, KeyError, TypeError):
                    pass
        return out

    def _guard(self, formula: S.Expr) -> S.Expr:
        constructed: S.Expr = S.BoolLit(True)
        for c in self.enc.system.contracts:
            constructed = S.BinOp("&&", constructed, S.Constructed(c.name))
        return S.BinOp("->", constructed, formula)

    def step_check(self, names: List[str],
                   only: Optional[Tuple[S.Contract, S.Procedure]] = None
                   ) -> Tuple[str, Dict[str, str]]:
        """C(s) ⇒ I(Trans(s, t)) for every candidate I in `names`, with C the conjunction of
        `names` and of the axioms: one property per I and per procedure C.f (constructors
        included; only `only` if given), C(s) ⇒ Φ(∀a, x̄, v[, δ]. ⟨a : C.f(x̄) $ v @ δ⟩ I)(s),
        encoded like a modality, so that only f is unfolded (passing the whole Trans and
        fixing t.fx made each query much slower). A sender that is not a user makes the
        transaction revert, which leaves the state unchanged, so `a` ranges over the address
        domain. Returns the program and, for each property, the candidate it is about. Used
        when the conjunction of `step_conj_checks` is not decided, or its counterexample does
        not identify a candidate."""
        prog, s = self._program(), L.Var("s")
        premise = L.conj([self._conj(self.axioms + names, s), self.defaults(s)])
        props, about = [], {}
        for c, p in self.enc.system.methods:
            if only is not None and (c.name, p.name) != (only[0].name, only[1].name):
                continue
            for n in names:
                prop = f"step_{n}__{c.name}_{p.name}"
                guarded = self._guard(self.program.rule(n).formula)
                after = self.fenc.state_formula(self._after(c, p, guarded), s)
                props.append((prop, L.op("=>", premise, after)))
                about[prop] = n
        node = L.Function("main", [("s", ST)], [], properties=props,
                          comment="C(s) => I after any transaction, for every candidate I")
        return self._render(prog, node), about

    def _after(self, c: S.Contract, p: S.Procedure, formula: S.Expr) -> S.Expr:
        """∀a, x̄, v[, δ]. ⟨a : C.p(x̄) $ v @ δ⟩ formula, as a resolved formula."""
        sender = S.QVar("__sender", S.ADDRESS)
        args = tuple(S.QVar(f"__arg_{x.name}", x.type) for x in p.params)
        value = S.QVar("__value", self.program.balance_type)
        blocks = (S.QVar("__blocks", S.INT) if self.enc.system.uses_block_num
                  else S.IntLit(0))
        body: S.Expr = S.Modal(sender, c.name, S.ProcConst(c.name, p.name), args, value,
                               blocks, formula)
        for v in ([sender, value] + list(args) + ([blocks] if isinstance(blocks, S.QVar)
                                                   else [])):
            body = S.Quant("forall", v.name, v.type, body)
        return body

    def premises(self, rule: S.Rule, invariants: List[str]) -> List[List[str]]:
        """The sets of invariants to assume when checking `rule`, to be tried in turn: those
        that share state variables with the rule, then also those connected to them
        (transitively), if different. Irrelevant invariants can make the query much harder:
        the balance lemma over int, in a query over nonlinear reals, made z3 time out (the
        mix of int and real keeps it from using nlsat); in the AMM, the invariant on the
        liquidity shares, connected to the swap only through `supply`, turned a 1 s proof
        of Swap_reversibility into a timeout. Fewer premises are always sound."""
        prop = self._property(rule, L.Var("s"))
        direct = self.relevant(prop, invariants, transitive=False)
        closure = self.relevant(prop, invariants, transitive=True)
        return [direct] + ([closure] if closure != direct else [])

    def rule_check(self, rule: S.Rule, invariants: List[str],
                   split: bool = False) -> Tuple[str, List[str]]:
        """The rule on a free state satisfying the given invariants, as one property or, with
        `split`, as one property per case. Returns the program and the property names.

        The invariants are the premise of the property, not Lustre assertions: with
        assertions, Kind 2 did not prove Swap_reversibility of the swap pool in 30 s; as a
        premise, in 1 s. The cases are the conjuncts of the property, through implications
        (`A ⇒ (B ∧ C)` gives `A ⇒ B` and `A ⇒ C`); the expansion of the quantifiers over
        addresses and methods produces them. Neither form is always better: AMM Slippage
        (any transaction of an adversary before a swap) is unknown after 60 s as one
        property, and its 54 cases are proved in 3 s in one run; the swap-pool round trip is
        proved in 1 s as one property, and its 2 cases are unknown after 20 s in one run
        (0.6 s each in separate runs)."""
        prog, s = self._program(), L.Var("s")
        prop = L.op("=>", self._conj(invariants, s), self._property(rule, s))
        parts = cases(prop) if split else [prop]
        names = [rule.name] if len(parts) == 1 else [f"{rule.name}__{i}"
                                                      for i in range(len(parts))]
        node = L.Function(
            "main", [("s", ST)], [], properties=list(zip(names, parts)),
            comment=f"{rule.name} on every state satisfying the invariants"
                    f" {', '.join(invariants) or '(none)'}")
        return self._render(prog, node), names

    def concrete_check(self, rule: S.Rule, state: L.LExpr) -> str:
        """The rule at a concrete state (a record literal): exact, unlike the bounded
        evaluation of `fuzz.py`. A Kind 2 counterexample means that the rule is false there."""
        prog = self._program()
        node = L.Function("main", [("dummy", "bool")], [],
                          properties=[(rule.name, self._property(rule, state))],
                          comment=f"{rule.name} at a concrete state")
        return self._render(prog, node)

    def _property(self, rule: S.Rule, s: L.LExpr) -> L.LExpr:
        return self.fenc.rule(rule, s)

    def relevant(self, prop: L.LExpr, invariants: List[str],
                 transitive: bool = True) -> List[str]:
        """The invariants sharing fields of the state s with `prop` (transitively, through
        the fields of the invariants chosen, if `transitive`). The construction flags do not
        count: every rule and every invariant reads them."""
        s = L.Var("s")
        flags = {constructed_var(c.name) for c in self.enc.system.contracts}
        fields = {n: state_fields(self.candidates[n](s)) - flags for n in invariants}
        used, chosen, changed = state_fields(prop) - flags, [], True
        while changed:
            changed = False
            for n in invariants:
                if n not in chosen and fields[n] & used:
                    chosen.append(n)
                    if transitive:
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


def hoist(e: L.LExpr, inputs: List[Tuple[str, str]]) -> L.LExpr:
    """e without its universal quantifiers in positive position (under conjunctions,
    disjunctions and the conclusions of implications), whose variables are added to `inputs`:
    a node property is valid iff it holds for all values of the inputs, so `∀x. φ` and `φ`
    with input x are equivalent. Quantified names are fresh, so hoisting through a
    disjunction is sound. Kind 2 passes quantifiers to the solver, which then cannot use
    nlsat: the swap round trip of the AMM with a fee, at a concrete state, was unknown after
    20 s with `∀x`; with x an input, it is refuted at once."""
    if isinstance(e, L.Quant) and e.kind == "forall":
        inputs.extend(v for v in e.vars if v not in inputs)
        return hoist(e.body, inputs)
    if isinstance(e, L.Op) and e.op in ("and", "or"):
        return L.Op(e.op, tuple(hoist(a, inputs) for a in e.args))
    if isinstance(e, L.Op) and e.op == "=>":
        return L.Op("=>", (e.args[0], hoist(e.args[1], inputs)))
    return e


def cases(e: L.LExpr) -> List[L.LExpr]:
    """Formulas whose conjunction is equivalent to e: its conjuncts, through implications."""
    if isinstance(e, L.Op) and e.op == "and":
        return [c for a in e.args for c in cases(a)]
    if isinstance(e, L.Op) and e.op == "=>":
        return [L.op("=>", e.args[0], c) for c in cases(e.args[1])]
    return [e]


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
