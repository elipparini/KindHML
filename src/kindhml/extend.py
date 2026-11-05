"""Completion of the states of the fuzzer by the solver (DESIGN.md, Sect. 6, "Completion").

Random transactions reach deep states cheaply, but miss narrow ones: on lending_int_v4,
Health_non_interference fails only from a borrower exactly at the health threshold, and no
state among 427,000 random ones was such. From a reachable state s of the fuzzer, the solver
looks for one more transaction after which the property phi is false. For each procedure g,
sender u (a user) and choice of the address arguments of g, the query is

    s2 = trans(s, tx(u, g, x))  and  not s2.revert  and  not phi(s2)

over the next state s2 and the other arguments x of g (numbers, booleans); phi(s2) is the
property on a free state (`FormulaEncoder.prop`), encoded and translated once, and trans is
the transition term of g (`FormulaEncoder.trans_term`). For each state of the fuzzer, its
values are substituted for s and the formula is simplified: with s concrete, the fields that
make the arithmetic nonlinear (an interest index, a price) are numbers. The queries go to z3
through its Python API, in this process: through Kind 2, each took 2-3 s, of which z3 used
0.15-0.5 s; here 14-50 ms (2026-11-05).

The translation is not exact: addresses and methods are integers, and division follows
SMT-LIB. It need not be: a model only proposes a transaction; the reference interpreter runs
it from s, and the caller checks phi exactly at the new state (the exact check of the
fuzzer); only a confirmed state is a counterexample, reached by the transactions of s and
the proposed one.

The states (`Completion.candidates`): those of random traces whose abstract key is new. The
key of a state has, for each entry of the fields (and balances) read by phi, its sign (its
value, for addresses and booleans) and whether it differs from its value just after the
constructors: on lending_int_v4, states with a debt, collateral and an accrued index come
early, without naming these fields."""
from __future__ import annotations

import time
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from typing import Deque, Dict, Iterator, List, Optional, Tuple

import z3

from . import direct as D
from . import lustre as L
from . import syntax as S
from .concrete import state_literal
from .encode_trans import (BLOCKS, REVERT, ST, TX, addr_const, base_type, default_value,
                           param_var, proc_const)
from .lustre_subst import eq
from .model import System
from .reference import State, Tx

# z3's limit per query: they took 14-50 ms on the lending families (2026-11-05); 11 of about
# 60,000 were undecided within 2 s
QUERY_SECONDS = 2.0
# the time of a batch of random traces from which the states with new keys are taken: the
# fuzzer makes thousands of states per second, and a state costs about 0.5 s of queries
SELECT_SECONDS = 2.0


def applicable(e: S.Expr) -> bool:
    """Whether phi can be checked after one more transaction: no `old`, `lastReverted` or
    `block.number` outside its modalities (they would denote the added transaction)."""
    def visit(x, top: bool) -> bool:
        if top and isinstance(x, (S.Old, S.Reverted, S.BlockNum)):
            return False
        if isinstance(x, S.Modal):
            return all(visit(y, top) for y in (x.sender, x.proc, x.value, x.blocks) + x.args)
        for name in getattr(x, "__dataclass_fields__", ()):
            v = getattr(x, name)
            for y in (v if isinstance(v, tuple) else (v,)):
                if isinstance(y, S.Expr) and not visit(y, top):
                    return False
        return True
    return visit(e, True)


def _reads(e: S.Expr) -> Tuple[List[Tuple[str, str]], bool]:
    """The fields (contract, name) read by e, and whether it reads balances."""
    fields, balance = set(), [False]

    def visit(x):
        if isinstance(x, S.Field):
            fields.add((x.contract, x.name))
        if isinstance(x, S.Balance):
            balance[0] = True
        for name in getattr(x, "__dataclass_fields__", ()):
            v = getattr(x, name)
            for y in (v if isinstance(v, tuple) else (v,)):
                if isinstance(y, S.Expr):
                    visit(y)
    visit(e)
    return sorted(fields), balance[0]


class _Translator(D._Translator):
    """`direct._Translator` with the values of enumerated types (addresses, methods) as
    integers, so that a formula with address fields is in its fragment (inexact: see the
    module docstring)."""

    def __init__(self, decls: D.Declarations):
        super().__init__(decls)
        self.ids: Dict[str, int] = {}
        for constants in decls.enums.values():
            for c in constants:
                self.ids.setdefault(c, len(self.ids))

    def constant(self, name: str, typ: str):
        if typ in self.decls.enums:
            if name not in self.free:
                self.free[name] = z3.Int(name)
            return self.free[name]
        return super().constant(name, typ)

    def _run(self, e: L.LExpr, env):
        if isinstance(e, L.Var) and e.name not in env.values and e.name.startswith(("A_", "P_")):
            return z3.IntVal(self.ids[e.name])
        if isinstance(e, L.Quant) and any(t in self.decls.enums for _, t in e.vars):
            bound = {n: (z3.Int(f"{n}__{next(self.fresh)}") if t in self.decls.enums
                         else D._scalar(f"{n}__{next(self.fresh)}", t, self.decls))
                     for n, t in e.vars}
            body = self.run(e.body, D._Env({**env.values, **bound}))
            q = z3.ForAll if e.kind == "forall" else z3.Exists
            return q(list(bound.values()), body)
        return super()._run(e, env)


@dataclass
class _Query:
    contract: str
    proc: str
    sender: str
    addresses: Dict[str, str]           # the address arguments, fixed
    variables: Dict[str, z3.ExprRef]    # the other arguments, value, blocks: by name
    formula: z3.BoolRef


def _python(v: z3.ExprRef):
    if z3.is_true(v) or z3.is_false(v):
        return z3.is_true(v)
    if z3.is_int_value(v):
        return v.as_long()
    if z3.is_rational_value(v):
        return Fraction(v.numerator_as_long(), v.denominator_as_long())
    raise ValueError(f"no value for {v}")


class Completion:
    """The completion queries of a property with the users of `checks` (see the module
    docstring), and the states of the fuzzer still to complete."""

    def __init__(self, checks, prop: S.Property):
        self.checks, self.prop = checks, prop
        self.system: System = checks.enc.system
        self.tr = _Translator(D.Declarations.of(checks._program()))
        self.s, s2 = D._Sym("s", ST), D._Sym("s2", ST)
        env = D._Env({"s": self.s, "s2": s2})
        not_phi = z3.Not(self.tr.run(checks.fenc.prop(prop, L.Var("s2")), env))
        done = z3.Not(self.tr.field(s2, REVERT))
        self.queries: List[_Query] = []
        for c, p in self.system.methods:
            if p.name == S.CONSTRUCTOR:
                continue
            choices: List[Dict[str, str]] = [{}]
            for x in p.params:
                if x.type == S.ADDRESS:
                    choices = [{**ch, x.name: a} for ch in choices for a in self.system.addresses]
            for sender in self.system.users:
                for ch in choices:
                    tx, variables = self._transaction(c, p, sender, ch)
                    nxt = checks.fenc.trans_term(
                        S.Modal(S.NullLit(), c.name, S.ProcConst(c.name, p.name), (),
                                S.IntLit(0), S.IntLit(0), S.BoolLit(True)), L.Var("s"), tx)
                    step = self.tr.run(eq(L.Var("s2"), nxt),
                                       D._Env({"s": self.s, "s2": s2, **variables}))
                    self.queries.append(_Query(c.name, p.name, sender, ch,
                                               {n[2:]: v for n, v in variables.items()},
                                               z3.And(step, done, not_phi)))
        self.read, self.balance = _reads(prop.formula)
        self.keys: set = set()
        # states to complete, each with the index of its next query
        self.queue: Deque[Tuple[List[Tx], State, int]] = deque()

    @staticmethod
    def make(checks, prop: S.Property) -> Optional["Completion"]:
        """The completion of `prop`, or None if it does not apply (`applicable`) or its
        formula is outside the translation (e.g. records under quantifiers, mode "exists")."""
        if not applicable(prop.formula):
            return None
        try:
            return Completion(checks, prop)
        except (D.NotApplicable, z3.Z3Exception, RecursionError, KeyError, ValueError):
            return None

    def _transaction(self, c: S.Contract, p: S.Procedure, sender: str,
                     addresses: Dict[str, str]):
        """The transaction record of a call of p by `sender`, with the address arguments
        given and the others variables (x_name, x_value, x_blocks), and the z3 variables."""
        system, variables = self.system, {}

        def variable(name: str, typ: str) -> L.LExpr:
            variables[f"x_{name}"] = D._scalar(f"x_{name}", typ, self.tr.decls)
            return L.Var(f"x_{name}")
        amount = system.program.balance_type
        fields = {"sender": L.Var(addr_const(sender)), "cx": L.Var(addr_const(c.name)),
                  "fx": L.Var(proc_const(c.name, p.name)),
                  "value": (variable("value", base_type(amount)) if p.payable
                            else default_value(amount, system))}
        for v in system.param_vars:
            fields[param_var(v.contract, v.proc, v.name)] = default_value(v.type, system)
        for x in p.params:
            fields[param_var(c.name, p.name, x.name)] = (
                L.Var(addr_const(addresses[x.name])) if x.type == S.ADDRESS
                else variable(x.name, base_type(x.type)))
        if system.uses_block_num:
            fields[BLOCKS] = variable("blocks", "int")
        tx = L.record(TX, [(n, fields[n]) for n, _ in self.checks.enc.tx_fields()])
        return tx, variables

    # ------------------------------------------------------------------ states

    def key(self, st: State, st0: State) -> tuple:
        def abstract(v, v0):
            if isinstance(v, (bool, str)):
                return (v, v != v0)
            return ((v > 0) - (v < 0), v != v0)
        out = []
        for k in self.read:
            v, v0 = st.fields[k], st0.fields[k]
            if isinstance(v, dict):
                out += [abstract(v[a], v0[a]) for a in sorted(v)]
            else:
                out.append(abstract(v, v0))
        if self.balance:
            out += [abstract(st.balance[a], st0.balance[a]) for a in sorted(st.balance)]
        return tuple(out)

    def _new_states(self, fuzzer, stream: str, seconds: float) -> List[Tuple[List[Tx], State]]:
        """The states of random traces of `stream` whose key is new, within `seconds`."""
        out = []
        end = time.time() + seconds
        while time.time() < end:
            st0 = None
            for txs, st in fuzzer.traces(stream):
                if time.time() >= end:
                    break
                if not all(st.constructed.values()):
                    continue
                st0 = st0 or st
                k = self.key(st, st0)
                if k not in self.keys:
                    self.keys.add(k)
                    out.append((txs, st))
        return out

    # ------------------------------------------------------------------ queries

    def candidates(self, fuzzer, deadline: float) -> Iterator[Tuple[List[Tx], State, Tx]]:
        """Transactions proposed by the queries (prefix, state, transaction), until
        `deadline`; a state not finished goes on at the next call."""
        stream = f"complete:{self.prop.name}"
        while time.time() < deadline - 0.5:
            if not self.queue:
                batch = self._new_states(fuzzer, stream,
                                         min(SELECT_SECONDS, (deadline - time.time()) / 4))
                self.queue.extend((txs, st, 0) for txs, st in batch)
                if not self.queue:
                    return
            txs, st, i = self.queue.popleft()
            literal = self.tr.run(state_literal(st, self.system, self.checks.enc), D._Env({}))
            pairs: List[Tuple[z3.ExprRef, z3.ExprRef]] = []
            self._pairs(self.s, literal, pairs)
            for j in range(i, len(self.queries)):
                left = deadline - time.time()
                if left <= 0.5:
                    self.queue.appendleft((txs, st, j))
                    return
                tx = self._ask(self.queries[j], pairs, min(QUERY_SECONDS, left))
                if tx is not None:
                    yield txs, st, tx

    def _pairs(self, sym, value, out: list) -> None:
        for f in self.tr.fields(sym):
            a, b = self.tr.field(sym, f), value[f]
            if isinstance(a, D._Sym):
                self._pairs(a, b, out)
            else:
                out.append((a, b))

    def _ask(self, q: _Query, pairs, seconds: float) -> Optional[Tx]:
        f = z3.simplify(z3.substitute(q.formula, *pairs) if pairs else q.formula)
        if z3.is_false(f):
            return None
        solver = z3.Solver()
        solver.set("timeout", max(1, int(seconds * 1000)))
        solver.add(f)
        if solver.check() != z3.sat:
            return None
        model = solver.model()
        values = {n: _python(model.eval(v, model_completion=True))
                  for n, v in q.variables.items()}
        args = dict(q.addresses)
        args.update({n: v for n, v in values.items() if n not in ("value", "blocks")})
        return Tx(q.sender, q.contract, (q.contract, q.proc), args, values.get("value", 0),
                  values.get("blocks", 0))
