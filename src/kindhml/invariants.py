"""Invariant-assisted checking (DESIGN.md, "Invariants").

Kind 2 checks a property on the reachable states of (Init, Trans), by BMC and k-induction through
Trans. When Trans is nonlinear and the property holds only because of facts about the reachable
states (e.g. nonnegative reserves), this often fails. The checks below avoid the transition
system: each is one Kind 2 run on free values (a node without `pre`), i.e. one SMT query.

* Invariants, like properties, are required in the states where all contracts are constructed:
  (∧_C constructed_C) → I. So they hold trivially in the initial states, and a set C of
  candidates is inductive if, for every procedure f (constructors included),
  C(s) ⇒ C(Trans(s, t)) for every state s and call t of f (`step_conj_checks`;
  `step_check` with one property per candidate). Candidates refuted are dropped until the
  remaining set is inductive (Houdini, `verify._Invariants`). The built-in facts
  (balances are nonnegative; an unconstructed contract has default fields) are assumed.
* A property φ is checked on a free state s: C(s) ⇒ ((∧_C constructed_C) → Φ(φ))(s), with C the
  proved invariants. If it holds, φ holds in every reachable state (they all satisfy C).
  If it fails, the counterexample s* may be unreachable; `reach_check(s*)` asks BMC
  whether s* is reachable, which gives a counterexample of φ.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Callable, Dict, List, Optional, Sequence, Tuple

from . import lustre as L
from . import syntax as S
from .concrete import python_value, state_from_values
from .cutoff import Cutoff, OutOfFragment, Scanner, check_program, nonnegative_maps
from .encode_formula import FormulaEncoder
from .encode_trans import (BALANCE, ST, TX, Encoder, constructed_var, default_value, field_var,
                           ghost_var, key_field, summed_maps, zero)
from .lustre_subst import eq
from .model import NULL, System
from .reference import FormulaEvaluator, Interpreter, Tx, default

StateFormula = Callable[[L.LExpr], L.LExpr]


class Checks:
    def __init__(self, program: S.Program, n_users: int, mode: str, expand: Sequence[str],
                 ghost_sums: bool = False):
        self.program = program
        self.mode, self.expand = mode, tuple(expand)
        self.enc = Encoder(System.make(program, n_users, ghost_sums))
        self.fenc = FormulaEncoder(self.enc, mode, tuple(expand))
        lemmas = [(n, (lambda st, e=e: self.fenc.inliner.run(e, {"s": st})))
                  for n, e in self.enc.lemmas()]
        # an invariant, like a property, is required in the states where all contracts are
        # constructed: (∧_C constructed_C) → Φ(I)
        mine = [(r.name, (lambda st, r=r: self.fenc.prop(r, st)))
                for r in program.properties if r.invariant]
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
                                       default_value(f.type, system)) for f in c.fields]
                                   + [eq(L.proj(st, ghost_var(k)), zero(t))
                                      for k, t in self.enc.ghosts.items()
                                      if k != BALANCE and k[0] == c.name]))
                       for c in system.contracts if c.fields])

    def sum_axioms(self, names: List[str], st: L.LExpr) -> L.LExpr:
        """Parameterized mode, where sum(m) is a free state variable σ in a free state: for
        each map m whose entries are all nonnegative by the premises `names`, the sum of the
        entries at all the addresses of the system is at most σ (when all contracts are
        constructed, as the candidates; for balance, always). It holds in every state that
        satisfies `names` and where σ is the sum, so assuming it is sound. It stands for the
        universal formulas ∀ distinct a_1..a_k. m[a_1] + ... + m[a_k] <= σ (k >= 1), which
        are equivalent to it, with nonnegative entries, on the addresses of the system; so it
        does not change the cutoff (DESIGN.md, Sect. 7.3). The bounds on single entries and
        on pairs of entries are too weak: with 3 users, the step of `redeem` of the AMM
        refuted `minted[u] + minted[v] <= supply` from a state whose 3 entries summed to
        more than σ."""
        if not self.enc.ghosts:
            return L.TRUE
        formulas = [self.program.prop(n).formula for n in names if n not in self.axioms]
        nonneg = nonnegative_maps(formulas)
        constructed = L.conj([L.proj(st, constructed_var(c.name))
                              for c in self.enc.system.contracts])
        addrs = self.enc.system.addresses
        out = []
        for key in self.enc.ghosts:
            if key == BALANCE:
                if "_lemma_balances_nonnegative" not in names:
                    continue
                m, guard = L.proj(st, BALANCE), L.TRUE
            elif key in nonneg:
                m, guard = L.proj(st, field_var(*key)), constructed
            else:
                continue
            total = None
            for a in addrs:
                x = L.proj(m, key_field(a))
                total = x if total is None else L.op("+", total, x)
            out.append(L.op("=>", guard, L.op("<=", total, L.proj(st, ghost_var(key)))))
        return L.conj(out)

    def witness_maps(self, names: List[str], prop: S.Property) -> List:
        """The maps of the witness premises of the check of `prop` with the premises `names`
        (`witness_axioms`): those whose sum occurs in the contracts, in the property or in the
        premises. For another map, they would add nothing: in a counterexample, σ can be
        replaced by the sum of the entries at the addresses of the system, which satisfies
        them and the bounds of `sum_axioms`, and changes nothing else."""
        formulas = (prop,) + tuple(self.program.prop(n) for n in names if n not in self.axioms)
        occurring = summed_maps(S.Program(self.program.contracts, formulas,
                                          self.program.balance_type))
        return [key for key in self.enc.ghosts if key in occurring]

    def witness_axioms(self, keys: List, st: L.LExpr) -> L.LExpr:
        """Parameterized mode: for each map m of `keys`, if the entries at null and at the
        contracts do not add up to σ, a user has a nonzero entry. It holds in every state where
        σ is the sum (with the entries 0 at the users, the sum is that of the other
        addresses), so assuming it is sound; each adds an address existential to the check,
        one user to its cutoff (DESIGN.md, Sect. 7.3). Without it, the check of
        `total == 0 || exists a . deposit[a] > 0`, with `sum(deposit) == total`, has the
        counterexample to induction where every entry of the system is 0 and σ = total = 1:
        the depositor is a user outside the system."""
        system = self.enc.system
        fixed = [NULL] + [c.name for c in system.contracts]
        out = []
        for key in keys:
            m = L.proj(st, BALANCE if key == BALANCE else field_var(*key))
            total = None
            for a in fixed:
                x = L.proj(m, key_field(a))
                total = x if total is None else L.op("+", total, x)
            out.append(L.op("=>", L.neg(eq(L.proj(st, ghost_var(key)), total)),
                            L.disj([L.neg(eq(L.proj(m, key_field(u)), zero(self.enc.ghosts[key])))
                                    for u in system.users])))
        return L.conj(out)

    def _premise_count(self, names: List[str]) -> int:
        """The address constants of the free state and of the premises `names` in the
        negation of a check (`cutoff.py`). Raises OutOfFragment."""
        scan = Scanner(self.enc.system)
        return check_program(self.enc.system) + sum(
            scan.skolems(self.program.prop(n).formula, positive=False)
            for n in names if n not in self.axioms)

    def step_count(self, names: List[str], c: S.Contract, p: S.Procedure) -> int:
        """k of the step of Houdini for procedure p with the candidates `names`
        (`step_conj_checks`): its cutoff is max(1, k). Raises OutOfFragment."""
        conj: S.Expr = S.BoolLit(True)
        for n in names:
            if n not in self.axioms:
                conj = S.BinOp("&&", conj, self.program.prop(n).formula)
        after = self._after(c, p, self._guard(conj))
        return self._premise_count(names) + Scanner(self.enc.system).skolems(after, True)

    def property_count(self, premises: List[str], prop: S.Property,
                       witnesses: Sequence = ()) -> int:
        """k of the check of `prop` on a free state with the premises `premises` and the
        witness premises of the maps `witnesses` (`property_check`): its cutoff is max(1, k).
        Raises OutOfFragment."""
        return (self._premise_count(premises) + len(witnesses)
                + Scanner(self.enc.system).skolems(prop.formula, True))

    def cutoff(self, properties: List[S.Property]) -> Cutoff:
        """The counts of the checks (`cutoff.py`) with all the candidates as premises: the
        step of each procedure, and each property on a free state. They bound those with fewer
        premises or candidates: premises add their counts, and the candidates after a call
        count for the largest one. The checks themselves use the counts of their actual
        premises and candidates (`step_count`, `property_count`)."""
        names = [n for n in self.candidates if n not in self.axioms]
        checks: Dict[str, int] = {}
        try:
            for c, p in self.enc.system.methods:
                checks[f"step of {c.name}.{p.name}"] = self.step_count(names, c, p)
        except OutOfFragment as e:
            return Cutoff(None, str(e))
        outside: Dict[str, str] = {}
        for r in properties:
            try:
                checks[f"property {r.name}"] = self.property_count(names, r)
            except OutOfFragment as e:
                outside[r.name] = str(e)
        steps = max([1] + [v for k, v in checks.items() if k.startswith("step ")])
        return Cutoff(steps, "", checks, outside)

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

    def step_conj_checks(self, names: List[str],
                         only: Optional[Tuple[S.Contract, S.Procedure]] = None
                         ) -> List[Tuple[str, S.Contract, S.Procedure]]:
        """The step of Houdini, one program per procedure f, with one property: all the
        candidates in `names` hold after any call of f from a state satisfying them,
        C(s) ⇒ Φ(∀a, x̄, v[, δ]. ⟨a : C.f(x̄) $ v @ δ⟩ (constructed → ∧ names))(s). If it is
        refuted, its counterexample identifies the candidates that do not hold after the
        call (`refuted_after`). With one property per candidate, the inlined call is copied
        into every property: on the lending protocol, 71 candidates were not decided in
        64 s; as one conjunction, each procedure takes 1-6 s. With `only`, for that
        procedure only."""
        conj: S.Expr = S.BoolLit(True)
        for n in names:
            conj = S.BinOp("&&", conj, self.program.prop(n).formula)
        s = L.Var("s")
        premise = L.conj([self._conj(self.axioms + names, s), self.defaults(s),
                          self.sum_axioms(self.axioms + names, s)])
        out = []
        for c, p in self.enc.system.methods:
            if only is not None and (c.name, p.name) != (only[0].name, only[1].name):
                continue
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
        (inputs after `hoist`), for every sender (the sender is expanded, not an input). An
        address argument that is not an input (expanded, A1) takes every address in turn;
        any other argument missing from the counterexample takes the default of its type.
        Every choice is sound: a candidate false after a concrete call from s is refuted.
        In parameterized mode, each sum(m) of s is the state variable σ_m, which also counts
        users outside the system: the interpreter keeps σ_m minus the sum of the entries
        (a call changes both by the same amount), as the encoding does."""
        values: Dict[str, object] = {}
        for block in counterexample or []:
            for stream in block.get("streams", []):
                vals = dict((int(k), v) for k, v in stream.get("instantValues", []))
                if 0 in vals:
                    values[stream["name"]] = vals[0]
        system = self.enc.system
        st = state_from_values(values, system, self.enc, free_sums=True)
        inputs = {}
        for name, v in values.items():
            if name.startswith("q___") and "_" in name[4:]:
                inputs[name[4:].rsplit("_", 1)[0]] = python_value(v)
        choices = []
        for x in p.params:
            if f"arg_{x.name}" in inputs:
                choices.append([inputs[f"arg_{x.name}"]])
            elif x.type == S.ADDRESS:
                choices.append([a for a in system.addresses if a != NULL])
            else:
                choices.append([default(x.type, system)])
        tx = dict(value=inputs.get("value", 0), blocks=inputs.get("blocks", 0))
        interp = Interpreter(system)
        ev = FormulaEvaluator(system, range(-1, 4))
        out = set()
        for sender, values in product(system.addresses, product(*choices)):
            args = {x.name: v for x, v in zip(p.params, values)}
            post = interp.step(st, Tx(sender, c.name, (c.name, p.name), args, **tx))
            if not all(post.constructed.values()):
                continue
            for n in names:
                try:
                    if not ev.holds(self.program.prop(n).formula, [post]):
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
        premise = L.conj([self._conj(self.axioms + names, s), self.defaults(s),
                          self.sum_axioms(self.axioms + names, s)])
        props, about = [], {}
        for c, p in self.enc.system.methods:
            if only is not None and (c.name, p.name) != (only[0].name, only[1].name):
                continue
            for n in names:
                prop = f"step_{n}__{c.name}_{p.name}"
                guarded = self._guard(self.program.prop(n).formula)
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

    def premises(self, prop: S.Property, invariants: List[str]) -> List[List[str]]:
        """The sets of invariants to assume when checking `prop`, to be tried in turn: those
        that share state variables with the property, then also those connected to them
        (transitively), if different. Irrelevant invariants can make the query much harder:
        the balance lemma over int, in a query over nonlinear reals, made z3 time out (the
        mix of int and real keeps it from using nlsat); in the AMM, the invariant on the
        liquidity shares, connected to the swap only through `supply`, turned a 1 s proof
        of Swap_reversibility into a timeout. Fewer premises are always sound."""
        goal = self._property(prop, L.Var("s"))
        direct = self.relevant(goal, invariants, transitive=False)
        closure = self.relevant(goal, invariants, transitive=True)
        return [direct] + ([closure] if closure != direct else [])

    def property_check(self, prop: S.Property, invariants: List[str],
                   split: bool = False, witnesses: Sequence = ()) -> Tuple[str, List[str]]:
        """The property on a free state satisfying the given invariants (and the witness
        premises of the maps `witnesses`), as one Kind 2 property or, with `split`, as one
        property per case. Returns the program and the property names.

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
        goal = L.op("=>", L.conj([self._conj(invariants, s), self.sum_axioms(invariants, s),
                                  self.witness_axioms(list(witnesses), s)]),
                    self._property(prop, s))
        parts = cases(goal) if split else [goal]
        names = [prop.name] if len(parts) == 1 else [f"{prop.name}__{i}"
                                                      for i in range(len(parts))]
        node = L.Function(
            "main", [("s", ST)], [], properties=list(zip(names, parts)),
            comment=f"{prop.name} on every state satisfying the invariants"
                    f" {', '.join(invariants) or '(none)'}")
        return self._render(prog, node), names

    def concrete_check(self, prop: S.Property, state: L.LExpr) -> str:
        """The property at a concrete state (a record literal): exact, unlike the bounded
        evaluation of `fuzz.py`. A Kind 2 counterexample means that the property is false there."""
        prog = self._program()
        node = L.Function("main", [("dummy", "bool")], [],
                          properties=[(prop.name, self._property(prop, state))],
                          comment=f"{prop.name} at a concrete state")
        return self._render(prog, node)

    def _property(self, prop: S.Property, s: L.LExpr) -> L.LExpr:
        return self.fenc.prop(prop, s)

    def relevant(self, prop: L.LExpr, invariants: List[str],
                 transitive: bool = True) -> List[str]:
        """The invariants sharing fields of the state s with `prop` (transitively, through
        the fields of the invariants chosen, if `transitive`). The construction flags do not
        count: every property and every invariant reads them."""
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


def final_values(counterexample: list, var: str = "s") -> Dict[str, object]:
    """The values of the stream record `var` at the last step of a Kind 2 counterexample
    (JSON) of the transition system, by path, as values of the reference interpreter."""
    out: Dict[str, object] = {}
    for block in counterexample or []:
        for stream in block.get("streams", []):
            name = stream["name"]
            if not (name == var or name.startswith(var + ".")):
                continue
            values = dict((int(k), v) for k, v in stream.get("instantValues", []))
            if values:
                out[name] = python_value(values[max(values)])
    return out


def python_constant(c: L.LExpr):
    """A constant of `state_values` as a value of the reference interpreter."""
    if isinstance(c, (L.Int, L.Real, L.Bool)):
        return c.value
    if isinstance(c, L.Var):
        return python_value(c.name)
    raise ValueError(f"not a constant: {c!r}")


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
