"""Encoding of formulae: Φ^{V,E}(φ) (Sect. `sec:encoding:property`).

The modal tree is built during the recursion: a `Node` is a state term (the copy SVars^V)
together with its parent, so that `old(e)` at V is encoded at the parent of V.

The modality  Φ^{V,E}(⟨e_s : C.e_f(ē) $ e_v⟩ψ)  is encoded in one of two ways.

* mode "exists" (the paper): ∃SVars^{V'}. SVars^{V'} = trans(SVars^V, TVars^E) ∧ Φ^{V',E}(ψ),
  where SVars^{V'} is a record of fresh scalar variables (Kind 2 does not support quantifiers
  over records) and trans is called once per modality.
* mode "subst": Φ^{V',E}(ψ) with SVars^{V'} := trans(SVars^V, TVars^E), which is equivalent
  since Trans is a function (Lemma `lem:transition`).

In both modes the transition variables are those fixed by the modality (sender, cx, fx, value,
EqParams, and the increase `blocks` of the block number, 0 when omitted); the ones that are
not fixed (parameters of other procedures) take an arbitrary value, since Trans does not
depend on them. The parameters of `h()` with h a method variable are existentially
quantified (extension, see DESIGN.md).
"""

from __future__ import annotations

import os
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from . import desugar
from . import lustre as L
from . import syntax as S
from .encode_trans import (BLOCKS, REVERT, TX, Encoder, addr_const, base_type, constructed_var,
                           default_value, key_field, param_var, proc_const)
from .errors import KindHMLError
from .lustre_subst import EncodingTimeout, Inliner, eq, free_vars, ite, tick
from .model import NULL

MODES = ("levels", "exists", "inline", "subst")
# mode inline: the largest next state of a modality, as a tree (nodes of the Lustre text), that
# is substituted into its body; a larger one gets fresh state variables (`modal`). INLINE_BOUND
# for a next state that a nested modality whose method is a variable takes as input (its
# transition is a case split over all procedures, which copies the input once per procedure),
# LAST_BOUND for the others. On a copy of lending-simple-real Liquidation_attack_any (three
# modalities whose methods are variables, 2 users), the next states have 4,200, 375,000 and 31
# million nodes: with 20,000 or 100,000 as INLINE_BOUND, a state of 11,800 nodes was still
# substituted, and the encoding took 150 s and 10 million nodes; with 5,000, 12 s and 0.8
# million (without the bound: > 600 s). With INLINE_BOUND for every nested modality, the AMM
# Sandwich properties (methods given, inputs of 2,900-7,300 nodes) were bound too, and their
# refutations became slower (amm_real_v4 Sandwich: 238 s, then unknown at 600 s).
INLINE_BOUND = int(os.environ.get("KINDHML_INLINE_BOUND", "5000"))
LAST_BOUND = int(os.environ.get("KINDHML_LAST_BOUND", "1000000"))


def _has_method_variable(e) -> bool:
    """Whether the formula e (source syntax) contains a modality whose method is a variable."""
    if isinstance(e, S.Modal) and not isinstance(e.proc, S.ProcConst):
        return True
    for name in getattr(e, "__dataclass_fields__", ()):
        v = getattr(e, name)
        for x in (v if isinstance(v, tuple) else (v,)):
            if isinstance(x, S.Expr) and _has_method_variable(x):
                return True
    return False


def tree_size(e: L.LExpr, memo: Optional[dict] = None) -> int:
    """The number of nodes of e as a tree (as printed), computed on the shared nodes once."""
    memo = {} if memo is None else memo
    k = id(e)
    if k not in memo:
        n = 1
        for name in getattr(e, "__dataclass_fields__", ()):
            v = getattr(e, name)
            for x in (v if isinstance(v, tuple) else (v,)):
                if isinstance(x, tuple):
                    x = x[-1]                     # (name, value) of a record literal
                if isinstance(x, L.LExpr):
                    n += tree_size(x, memo)
        memo[k] = n
    return memo[k]
METHOD_COPIES = 32      # default bound on the copies of the expanded method quantifiers


def parse_expand(expand) -> Tuple[set, int]:
    """The types of `expand` (e.g. `address`, `method:100`) and the bound on the copies of
    the method quantifiers."""
    types, copies = set(), METHOD_COPIES
    for x in expand:
        name, _, bound = x.partition(":")
        if bound and name != "method":
            raise ValueError(f"only method takes a bound: {x}")
        if bound:
            if not bound.isdigit():
                raise ValueError(f"the bound of method must be a natural number: {x}")
            copies = int(bound)
        types.add(name)
    return types, copies


@dataclass(frozen=True)
class Node:
    state: L.LExpr
    parent: Optional["Node"] = None


class FormulaEncoder:
    def __init__(self, enc: Encoder, mode: str = "exists", expand: Tuple[str, ...] = ()):
        """`expand` lists the finite types (`address`, `method`) whose quantifiers are
        expanded into finite conjunctions/disjunctions (A1). `method:N` bounds the copies
        of the method quantifiers (`method` alone: METHOD_COPIES, see `quant`)."""
        if mode not in MODES:
            raise ValueError(f"unknown mode {mode}")
        self.enc = enc
        self.system = enc.system
        self.mode = mode
        self.expand, self.method_copies = parse_expand(expand)
        self.inliner = Inliner({f.name: f for f in enc.helpers()})
        self._fresh = 0
        self._copies = 1          # copies made by the expanded method quantifiers around
        # reduction by symmetry (`symmetric` of `prop`): the users bound by the reduced
        # address quantifiers around, or None where there is no reduction
        self._sym: Optional[List[str]] = None
        # free variables of the nodes of the formula being encoded, by identity (`quantify`)
        self._fv: Dict[int, tuple] = {}

    def fresh(self, base: str) -> str:
        self._fresh += 1
        return f"{base}_{self._fresh}"

    # ------------------------------------------------------------ properties

    def prop(self, r: S.Property, state: L.LExpr = L.Var("s"),
             symmetric: bool = False) -> L.LExpr:
        """(∧_C constructed_C) → Φ(φ): φ is required in the states where all contracts are
        constructed (DESIGN.md, Sect. 4). With `symmetric`, reduced by symmetry (`_reduced`):
        only for the conclusion of a check on free states whose premises name no user."""
        self._fresh = 0
        constructed = L.conj([L.proj(state, constructed_var(c.name)) for c in self.system.contracts])
        prop = L.op("=>", constructed, self._top(r.formula, Node(state), symmetric))
        if self.mode in ("levels", "inline"):
            prop = self.inliner.run(prop, {})     # inline helpers and simplify
        return prop

    def state_formula(self, e: S.Expr, state: L.LExpr, symmetric: bool = False) -> L.LExpr:
        """Φ(φ) at `state` for a formula without modalities (an invariant): required in
        every reachable state, so without the guard on construction. `symmetric` as for
        `prop`."""
        f = self._top(e, Node(state), symmetric)
        return self.inliner.run(f, {}) if self.mode in ("levels", "inline") else f

    def _top(self, e: S.Expr, node: Node, symmetric: bool) -> L.LExpr:
        saved, self._sym = self._sym, ([] if symmetric else None)
        try:
            return self.phi(e, node, {})
        finally:
            self._sym = saved
            self._fv = {}

    # ------------------------------------------------------------ reduction by symmetry
    #
    # In a check on free states, ∀s. P(s) → Φ(s), where the premises P name no user (they are
    # invariant under the permutations of the users), a universal address quantifier of Φ in
    # positive position, outside existentials and disjunctions, needs only one value per
    # pattern of equalities with the users bound by such quantifiers around it: the contracts,
    # these users, and one more (DESIGN.md, Sect. 7.7). `_sym` holds these users along the
    # current path; None where the reduction stops.

    def _with(self, sym: Optional[List[str]], f):
        saved, self._sym = self._sym, sym
        try:
            return f()
        finally:
            self._sym = saved

    def _reduced(self) -> List[Tuple[L.LExpr, Optional[List[str]]]]:
        """The values of a reduced universal address quantifier, each with the users bound
        in its body: the contracts, the users bound around, and the first other user."""
        bound = self._sym
        out = [(L.Var(addr_const(c.name)), bound) for c in self.system.contracts]
        out += [(L.Var(addr_const(u)), bound) for u in bound]
        rest = [u for u in self.system.users if u not in bound]
        if rest:
            out.append((L.Var(addr_const(rest[0])), bound + [rest[0]]))
        return out

    # ------------------------------------------------------------ formulae

    def phi(self, e: S.Expr, node: Node, env: Dict[str, object]) -> L.LExpr:
        tick()                          # the time limit (`lustre_subst.DEADLINE`)
        if isinstance(e, S.Quant):
            return self.quant(e, node, env)
        if isinstance(e, S.Modal):
            return self.modal(e, node, env)
        if isinstance(e, S.Old):
            if node.parent is None:
                raise KindHMLError("old(...) outside the scope of a modality", e.pos)
            return self.phi(e.arg, node.parent, env)
        if isinstance(e, S.QVar):
            if e.type == S.ARGS:
                raise KindHMLError("a variable of type calldataargs can only be the argument"
                                   " of a modality", e.pos)
            return env[e.name]
        if self._sym is not None and isinstance(e, S.BinOp) and e.op in ("&&", "->"):
            # the reduction goes on in both conjuncts and in the conclusion of an implication
            # (A → ∀a.B ⟺ ∀a.(A → B)); not in a premise, nor in a disjunction, where the
            # quantifiers of the two disjuncts would need their patterns together
            left = (self.phi(e.left, node, env) if e.op == "&&"
                    else self._with(None, lambda: self.phi(e.left, node, env)))
            return L.op("and" if e.op == "&&" else "=>", left, self.phi(e.right, node, env))
        return self._with(None, lambda: self.enc.expr(
            e, node.state, None, other=lambda x: self.phi(x, node, env)))

    def quant(self, e: S.Quant, node: Node, env) -> L.LExpr:
        """∀x:T.ψ and ∃x:T.ψ. Addresses range over all addresses but null (DESIGN.md);
        uint over the naturals; args over records of ParamVars (one scalar per ParamVar)."""
        if e.type == S.ARGS:
            comps = {}
            decls, guards = [], []
            for v in self.system.param_vars:
                name = self.fresh(f"q_{e.var}_{v.contract}_{v.proc}_{v.name}")
                comps[param_var(v.contract, v.proc, v.name)] = L.Var(name)
                decls.append((name, base_type(v.type)))
                guards += self.domain(L.Var(name), v.type, address_quantifier=False)
            body = self._with(self._sym if e.kind == "forall" else None,
                              lambda: self.phi(e.body, node, {**env, e.var: comps}))
        elif e.type.name in self.expand and self._expands(e.type):
            values = self.finite_domain(e.type)
            outer = self._copies
            if e.type == S.METHOD:
                self._copies = outer * len(values)
            if e.kind == "forall" and e.type == S.ADDRESS and self._sym is not None:
                scoped = self._reduced()
            else:
                # a method quantifier keeps the reduction around it if universal
                keep = self._sym if e.kind == "forall" else None
                scoped = [(v, keep) for v in values]
            try:
                parts = [self._with(sym, lambda v=v: self.phi(e.body, node, {**env, e.var: v}))
                         for v, sym in scoped]
            finally:
                self._copies = outer
            return L.conj(parts) if e.kind == "forall" else L.disj(parts)
        elif e.kind == "exists":
            name = self.fresh(f"q_{e.var}")
            decls = [(name, base_type(e.type))]
            guards = self.domain(L.Var(name), e.type, address_quantifier=True)
            body = self._with(None, lambda: self.phi(e.body, node, {**env, e.var: L.Var(name)}))
        else:
            name = self.fresh(f"q_{e.var}")
            decls = [(name, base_type(e.type))]
            guards = self.domain(L.Var(name), e.type, address_quantifier=True)
            body = self.phi(e.body, node, {**env, e.var: L.Var(name)})
        return self.quantify(e.kind, decls, guards, body)

    def _expands(self, t: S.Type) -> bool:
        """Expanding nested method quantifiers multiplies the copies of their bodies (each
        with the transitions of its modalities): 1000 for three calls of 10 methods, which
        neither the encoder nor Kind 2 managed. A method quantifier is expanded only if the
        product of the domains of the expanded method quantifiers around it, and of its own,
        is at most `method_copies`; so the outer ones are expanded first."""
        if t != S.METHOD:
            return True
        return self._copies * len(self.finite_domain(t)) <= self.method_copies

    def finite_domain(self, t: S.Type) -> List[L.LExpr]:
        """Addresses: all but null. Methods: all procedures but the constructors, which cannot
        be called after deployment (DESIGN.md, Sect. 4)."""
        if t == S.ADDRESS:
            return [L.Var(addr_const(a)) for a in self.system.addresses if a != NULL]
        if t == S.METHOD:
            return [L.Var(proc_const(c.name, p.name)) for c, p in self.system.methods
                    if p.name != S.CONSTRUCTOR]
        raise ValueError(f"type {t} is not finite")

    def domain(self, v: L.LExpr, t: S.Type, address_quantifier: bool) -> List[L.LExpr]:
        """Guards restricting a (non-expanded) quantified variable to its domain."""
        if t == S.ADDRESS and address_quantifier:
            return [L.op("<>", v, L.Var(addr_const(NULL)))]
        if t == S.METHOD:
            return [L.op("<>", v, L.Var(proc_const(c.name, S.CONSTRUCTOR)))
                    for c in self.system.contracts]
        if t == S.UINT:
            return [L.op(">=", v, L.Int(0))]
        return []

    def quantify(self, kind: str, decls, guards: List[L.LExpr], body: L.LExpr) -> L.LExpr:
        """Q decls. (guards ∧/→ body). A guard mentioning a single declared variable is a
        domain restriction, satisfiable for every value of the other variables; a variable
        used only in such guards is dropped together with them."""
        fv = lambda x: free_vars(x, self._fv)
        names = {n for n, _ in decls}
        used = fv(body) & names
        for g in guards:
            if len(fv(g) & names) > 1:     # e.g. the transition relation
                used |= fv(g) & names
        decls = [(n, t) for n, t in decls if n in used]
        guards = [g for g in guards if not (fv(g) & names - used)]
        if not decls:
            return body
        if kind == "forall":
            inner = L.op("=>", L.conj(guards), body) if guards else body
        else:
            inner = L.conj(guards + [body])
        return L.Quant(kind, tuple(decls), inner)

    def modal(self, e: S.Modal, node: Node, env) -> L.LExpr:
        # the sender, value and arguments are terms, not formulas in positive position: a
        # quantified boolean argument must not be reduced by symmetry (an audit found a false
        # property proved that way, tests/test_symmetry.py)
        here = lambda x: self._with(None, lambda: self.phi(x, node, env))
        decls: List[Tuple[str, str]] = []
        bound_state = False             # mode inline: the next state got variables (universal)
        guards: List[L.LExpr] = []
        fields = {"sender": here(e.sender), "cx": L.Var(addr_const(e.contract)),
                  "fx": here(e.proc), "value": here(e.value)}
        # EqParams
        params: Dict[str, L.LExpr] = {}
        if isinstance(e.proc, S.ProcConst):
            for v, a in zip(self.system.params_of(e.proc.contract, e.proc.proc), e.args):
                params[param_var(v.contract, v.proc, v.name)] = here(a)
        elif e.args:                                    # h(x) with x : calldataargs
            params = dict(env[e.args[0].name])
        else:                                           # h(): parameters existentially quantified
            for v in self.system.param_vars:
                name = self.fresh(f"p_{v.contract}_{v.proc}_{v.name}")
                params[param_var(v.contract, v.proc, v.name)] = L.Var(name)
                decls.append((name, base_type(v.type)))
                guards += self.domain(L.Var(name), v.type, address_quantifier=False)
        for v in self.system.param_vars:
            pv = param_var(v.contract, v.proc, v.name)
            fields[pv] = params.get(pv, default_value(v.type, self.system))
        if self.system.uses_block_num:
            fields[BLOCKS] = here(e.blocks)
        tx = L.record(TX, [(n, fields[n]) for n, _ in self.enc.tx_fields()])
        if self.mode == "subst":
            child = Node(L.call("trans", node.state, tx), node)
        elif self.mode == "inline":
            nxt_term = self.trans_term(e, node.state, tx)
            bound = INLINE_BOUND if _has_method_variable(e.body) else LAST_BOUND
            if tree_size(nxt_term) > bound:
                # a large next state gets fresh variables s' with s' = next state: equivalent
                # since Trans is a function; the nested modalities and old(...) then use s'. A
                # next state that a nested modality takes as input multiplies its size (as a
                # tree): by 70-80 per modality whose method is a variable on
                # lending-simple-real; the last one, or one with a given method, only adds
                # to it. Without parameters to
                # quantify, s' is universal (∀s'. s' = t → body, equivalent to ∃s'. s' = t ∧
                # body since s' is determined), so that in positive position it becomes an
                # input of the check (`invariants.hoist`), and the query has no quantifier:
                # with ∃, the refutation of amm_real_v4 Sandwich took 308 s instead of 238
                bound_state = not decls
                nxt, nxt_decls = self.state_vars()
                decls += nxt_decls
                guards.append(eq(nxt, nxt_term))
                child = Node(nxt, node)
            else:
                child = Node(nxt_term, node)
        elif self.mode == "exists":
            nxt, nxt_decls = self.state_vars()
            decls += nxt_decls
            guards.append(L.op("=", nxt, L.call("trans", node.state, tx)))
            child = Node(nxt, node)
        else:
            nxt, nxt_decls = self.state_vars()
            decls += nxt_decls
            relation, level_decls = self.trans_relation(e, node.state, tx, nxt)
            decls += level_decls
            guards.append(relation)
            child = Node(nxt, node)
        # the reduction by symmetry goes on in the body only if the next state is a term (the
        # transition is a function: ⟨t⟩∀a.ψ ⟺ ∀a.⟨t⟩ψ), not under existential variables
        keep = self._sym if self.mode == "inline" and not decls else None
        body = self._with(keep, lambda: self.phi(e.body, child, env))
        return self.quantify("forall" if bound_state else "exists", decls, guards, body)

    def trans_relation(self, e: S.Modal, state: L.LExpr, tx: L.LExpr, nxt: L.LExpr):
        """Trans(SVars^V, TVars^E, SVars^1..m, SVars^{V'}) written as scalar equations
        (mode "levels"): the temporary levels are fresh existentially quantified copies
        SVars^j, shared by the procedures (Sect. `sec:encoding:contract`). Since the called
        contract is a constant, only its procedures are considered, and only one if the
        procedure is a constant. Returns the formula and the declarations of the levels."""
        contract = self.system.program.contract(e.contract)
        if isinstance(e.proc, S.ProcConst):
            procs = [contract.proc(e.proc.proc)] if e.proc.contract == contract.name else []
        else:
            procs = list(contract.procs)
        t = L.Var("t")
        bodies = [(p, desugar.procedure(self.system, contract, p)) for p in procs]
        depth = max((Encoder.length(b) for _, b in bodies), default=0)
        levels, decls = [], []
        for _ in range(depth):
            lv, d = self.state_vars("l")
            levels.append(lv)
            decls += d
        env = {"s": state, "t": tx, **{f"l{k + 1}": lv for k, lv in enumerate(levels)}}
        run = lambda x: self.inliner.run(x, env)
        revert = run(L.call("revert_state", L.Var("s")))
        relation = eq(nxt, revert)                     # default: Revert
        for p, body in reversed(bodies):
            m = Encoder.length(body)
            terms = self.enc.levels(body, 0, t)
            steps = [eq(levels[k - 1], run(terms[k])) for k in range(1, m + 1)]
            reverted = L.disj([L.proj(levels[k - 1], REVERT) for k in range(1, m + 1)])
            result = ite(reverted, revert, levels[m - 1])
            branch = L.conj(steps + [eq(nxt, result)])
            relation = ite(eq(L.proj(tx, "fx"), L.Var(proc_const(contract.name, p.name))),
                           branch, relation)
        return relation, decls

    def trans_term(self, e: S.Modal, state: L.LExpr, tx: L.LExpr) -> L.LExpr:
        """χ(SVars^V, TVars^E): the next state as a term, obtained by substituting the levels
        (mode "inline"; see the end of Sect. `sec:encoding:contract`)."""
        contract = self.system.program.contract(e.contract)
        if isinstance(e.proc, S.ProcConst):
            procs = [contract.proc(e.proc.proc)] if e.proc.contract == contract.name else []
        else:
            procs = list(contract.procs)
        revert = self.inliner.run(L.call("revert_state", L.Var("s")), {"s": state})
        result = revert
        for p in reversed(procs):
            body = desugar.procedure(self.system, contract, p)
            m = Encoder.length(body)
            terms = self.enc.levels(body, 0, L.Var("t"))
            env = {"s": state, "t": tx}
            for k in range(1, m + 1):
                env[f"l{k}"] = self.inliner.run(terms[k], env)
            reverted = L.disj([L.proj(env[f"l{k}"], REVERT) for k in range(1, m + 1)])
            result = ite(eq(L.proj(tx, "fx"), L.Var(proc_const(contract.name, p.name))),
                         ite(reverted, revert, env[f"l{m}"]), result)
        return result

    def state_vars(self, prefix: str = "n") -> Tuple[L.LExpr, List[Tuple[str, str]]]:
        """A record literal of fresh scalar variables: a copy of SVars."""
        k = self.fresh(prefix)
        decls, values = [], []
        for n, t in self.enc.state_fields():
            if t.startswith("Map_"):
                vt = t[len("Map_"):]
                comps = []
                for a in self.system.addresses:
                    name = f"{k}_{n}_{a}"
                    decls.append((name, vt))
                    comps.append((key_field(a), L.Var(name)))
                values.append((n, L.record(t, comps)))
            else:
                name = f"{k}_{n}"
                decls.append((name, t))
                values.append((n, L.Var(name)))
        return L.record("St", values), decls
