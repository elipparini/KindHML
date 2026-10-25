"""Instances of a chain of existentials over methods (DESIGN.md, Sect. 7.9; 2026-10-25).

A property `forall xs . premise -> exists f1 args1 ... fk argsk . << s : C.f1(args1) >> ...
<< s : C.fk(argsk) >> body`, k >= 2 (lending `Liquidation_attack_any`: three calls of an
attacker that increase its net worth), holds if one of its instances holds: the methods are
procedures g1, ..., gk of C, the address arguments terms in scope (the address variables xs, the
contract, null), and the numeric arguments existential variables quantified before the chain,
whose values are chosen at its start, as those of args_i. An instance implies the property (the
introduction of the existentials), so its proof proves the property. The single existentials of
`witness.py` fix the numbers too, as terms; here they stay existential, for z3 directly
(`direct.py`).

There are (procedures)^k sequences (1331 on lending-real), each proof about 1 s, so the order
matters. `Search` scores the sequences at sample states: states s with C(s) and the premise
(models of z3 on a free state, `verify._chain_rounds`; not necessarily reachable, since the proof
is on such free states too), and the counterexamples of the instances tried. At each state and
assignment of xs where the premise holds (at most ENVS of them), a sequence gets the best
margin of body (L - R for L > R) over K runs of its calls with sampled arguments (the numbers of the state, their halves
and doubles, boundary values, `fuzz.boundaries`); the sequences are ranked by the number of
states where the margin is positive, then by the sum of their ranks at each state (Borda: the
margins of different states are not comparable). The next instance is the best sequence not
tried, with the address arguments of its best sample. A counterexample of its proof is a new
state, scored before the next choice (counterexample-guided, as CEGIS).

Only the contract and the property are used: never another property (2026-10-25, with the
user). On the 4 true `Liquidation_attack_any` rows, the first or second instance tried was
proved (11-34 s after the invariants); the order of the source proved none of the 6859
instances of lending_simple_real_v2 in 300 s (402 tried).
"""

from __future__ import annotations

import itertools
import os
import random
from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, List, Optional, Tuple

from . import fuzz, pretty
from . import syntax as S
from .model import NULL, System
from .reference import FormulaEvaluator, Revert, State, Tx

# samples of the arguments of a sequence at a state, and assignments of the universals scored
# at a state (KINDHML_CHAIN_SAMPLES, KINDHML_CHAIN_ENVS: experiments). Provisional: with 8 and 2,
# scoring took 9-16 s per state on lending; with 4 and 1, 2-4 s, and the proofs of
# lending_real_v2 and lending_simple_real_v2 came after 2 and 3 instances (2 and 2 before)
K = int(os.environ.get("KINDHML_CHAIN_SAMPLES", "4"))
ENVS = int(os.environ.get("KINDHML_CHAIN_ENVS", "1"))
BOUNDARY = 0.3                  # probability of a boundary value for a numeric argument
MAX_SEQUENCES = 20_000          # method sequences scored at most (procedures^k)


@dataclass
class Shape:
    """The parts of a chain property (module docstring)."""
    univ: List[Tuple[str, S.Type]]
    premise: S.Expr
    chain: List[S.Modal]
    body: S.Expr


def shape(prop: S.Property) -> Optional[Shape]:
    """The parts of `prop` if it is a chain of at least two existentials over methods, each
    with its arguments, whose modalities are those of the chain in order (module docstring),
    with universals over addresses only; else None."""
    univ, e = [], prop.formula
    while isinstance(e, S.Quant) and e.kind == "forall":
        if e.type != S.ADDRESS:
            return None
        univ.append((e.var, e.type))
        e = e.body
    if not (isinstance(e, S.BinOp) and e.op == "->"):
        return None
    premise, e = e.left, e.right
    pairs: List[List[Optional[str]]] = []
    while isinstance(e, S.Quant) and e.kind == "exists" and e.type in (S.METHOD, S.ARGS):
        if e.type == S.METHOD:
            pairs.append([e.var, None])
        elif pairs and pairs[-1][1] is None:
            pairs[-1][1] = e.var
        else:
            return None
        e = e.body
    chain = []
    while isinstance(e, S.Modal):
        chain.append(e)
        e = e.body
    if len(pairs) < 2 or len(chain) != len(pairs) or len({m.contract for m in chain}) != 1:
        return None
    for m, (f, args) in zip(chain, pairs):
        if not (isinstance(m.proc, S.QVar) and m.proc.name == f and args is not None
                and len(m.args) == 1 and isinstance(m.args[0], S.QVar)
                and m.args[0].name == args):
            return None
    used = {f for f, _ in pairs} | {x for _, x in pairs}
    if _mentions(e, used) or any(_mentions(x, used) for m in chain
                                 for x in (m.sender, m.value, m.blocks)):
        return None
    return Shape(univ, premise, chain, e)


def _names(e) -> set:
    """The names of the variables quantified or used in e."""
    out = {e.var} if isinstance(e, S.Quant) else {e.name} if isinstance(e, S.QVar) else set()
    for n in getattr(e, "__dataclass_fields__", ()):
        v = getattr(e, n)
        for x in (v if isinstance(v, tuple) else (v,)):
            if isinstance(x, S.Expr):
                out |= _names(x)
    return out


def _mentions(e, names: set) -> bool:
    if isinstance(e, S.QVar):
        return e.name in names
    return any(_mentions(x, names) for n in getattr(e, "__dataclass_fields__", ())
               for v in [getattr(e, n)] for x in (v if isinstance(v, tuple) else (v,))
               if isinstance(x, S.Expr))


def _numbers(st: State) -> set:
    out = set()
    for v in list(st.balance.values()) + list(st.fields.values()):
        for x in (v.values() if isinstance(v, dict) else [v]):
            if not isinstance(x, (bool, str)) and x > 0:
                out.add(x)
    return out


class Search:
    """The scores of the method sequences of a chain property at sample states, and the next
    instance to try (module docstring)."""

    def __init__(self, program: S.Program, prop: S.Property, sh: Shape, seed: str = "c1"):
        self.program, self.prop, self.sh = program, prop, sh
        self.contract = sh.chain[0].contract
        procs = [p for p in program.contract(self.contract).procs if p.name != S.CONSTRUCTOR]
        # the names that a new existential must avoid (no capture, no clash): those of the
        # property, of the procedures, fields and contracts
        self.taken = _names(prop.formula) | {c.name for c in program.contracts}
        for c in program.contracts:
            self.taken |= {p.name for p in c.procs} | {f.name for f in c.fields}
        self.seqs = (list(itertools.product(procs, repeat=len(sh.chain)))
                     if len(procs) ** len(sh.chain) <= MAX_SEQUENCES else [])
        self.rnd = random.Random(seed)
        self.total = [0] * len(self.seqs)       # the sums of the ranks
        self.wins = [0] * len(self.seqs)        # the states with a positive margin
        self.best: Dict[int, Tuple[int, dict, list]] = {}   # best rank, env, arguments
        self.tried: set = set()
        self.states = 0

    def envs(self, ev: FormulaEvaluator, st: State) -> List[dict]:
        """The assignments of the universals (users and contracts) where the premise holds."""
        out = []
        domain = [a for a in ev.system.addresses if a != NULL]
        for vals in itertools.product(domain, repeat=len(self.sh.univ)):
            env = dict(zip([v for v, _ in self.sh.univ], vals))
            try:
                if ev.holds(self.sh.premise, [st], env):
                    out.append(env)
            except (Revert, KeyError, ZeroDivisionError, TypeError):
                pass
        return out

    def add(self, st: State, system: System) -> int:
        """Scores the sequences at a new state; returns the number of assignments of the
        universals where the premise holds (0: the state is not used)."""
        ev = FormulaEvaluator(system, range(-1, 4), max_records=fuzz.MAX_RECORDS, rnd=self.rnd)
        envs = self.envs(ev, st)
        for env in envs[:ENVS]:
            res = [(self._run(ev, st, env, seq), i) for i, seq in enumerate(self.seqs)]
            res.sort(key=lambda r: (r[0][0] is not None, r[0][0] or 0))
            for rank, ((g, args), i) in enumerate(res):
                self.total[i] += rank
                if g is not None and g > 0:
                    self.wins[i] += 1
                if args is not None and rank > self.best.get(i, (-1,))[0]:
                    self.best[i] = (rank, env, args)
        self.states += 1
        return len(envs)

    def _run(self, ev: FormulaEvaluator, st: State, env: dict, seq) -> tuple:
        """The best margin of the sequence at (st, env) over K samples, and its arguments."""
        best, best_args = None, None
        for _ in range(K):
            hist, chosen = [st], []
            try:
                for m, p in zip(self.sh.chain, seq):
                    sender = ev.eval(m.sender, hist, env)
                    args = self._args(ev, p, st, hist[0], env, sender)
                    chosen.append(args)
                    tx = Tx(sender, self.contract, (self.contract, p.name), args,
                            ev.eval(m.value, hist, env), ev.eval(m.blocks, hist, env))
                    hist = [ev.interp.step(hist[0], tx)] + hist
                g = self._margin(ev, hist, env)
            except (KeyError, ZeroDivisionError, TypeError):
                continue
            if best is None or g > best:
                best, best_args = g, chosen
        return best, best_args

    def _margin(self, ev: FormulaEvaluator, hist: list, env: dict):
        b = self.sh.body
        if isinstance(b, S.BinOp) and b.op in (">", ">=", "<", "<="):
            x, y = ev.eval(b.left, hist, env), ev.eval(b.right, hist, env)
            return (x - y) if b.op in (">", ">=") else (y - x)
        return 1 if ev.holds(b, hist, env) else -1

    def _args(self, ev, p: S.Procedure, st0: State, st: State, env: dict, sender) -> dict:
        pool = sorted(_numbers(st0) | _numbers(st))
        pool = sorted(set(pool) | {Fraction(x) / 2 for x in pool} | {x * 2 for x in pool}
                      | {Fraction(1), Fraction(1, 10)})
        addresses = sorted(set(env.values()) | {self.contract, NULL})
        args = {}
        for x in p.params:
            if x.type == S.ADDRESS:
                args[x.name] = self.rnd.choice(addresses)
            elif x.type == S.BOOL:
                args[x.name] = self.rnd.choice([False, True])
            elif x.type == S.REAL:
                args[x.name] = self.rnd.choice(pool)
            else:
                args[x.name] = self.rnd.choice(sorted({int(v) for v in pool} | {1}))
        bounds = fuzz.boundaries(p)
        for x in p.params:
            if bounds.get(x.name) and self.rnd.random() < BOUNDARY:
                benv = {"sender": sender, "value": 0, "this": self.contract,
                        "args": dict(args)}
                try:
                    v = fuzz._number_of(ev.interp.eval(self.rnd.choice(bounds[x.name]), st,
                                                       benv), x.type)
                except (Revert, KeyError, TypeError, ZeroDivisionError):
                    v = None
                if v is not None:
                    args[x.name] = v
        return args

    def next(self) -> Optional[Tuple[str, S.Property]]:
        """The instance of the best sequence not tried (description, property), or None."""
        order = sorted((i for i in range(len(self.seqs)) if i not in self.tried),
                       key=lambda i: (-self.wins[i], -self.total[i], i))
        if not order:
            return None
        i = order[0]
        self.tried.add(i)
        _, env, args = self.best.get(i, (0, {}, None))
        return self.instance(self.seqs[i], env, args)

    def instance(self, seq, env: dict, args: Optional[list]) -> Tuple[str, S.Property]:
        """The instance of the sequence: its address arguments those of `args` (as terms:
        a universal with that value at env, the contract, or null), its numeric arguments
        existential."""
        exists, calls, used = [], [], set(self.taken)
        for j, (m, p) in enumerate(zip(self.sh.chain, seq)):
            terms = []
            for x in p.params:
                if x.type == S.ADDRESS:
                    value = args[j][x.name] if args else NULL
                    terms.append(self._term(env, value))
                else:
                    name = f"{p.name}_{j}_{x.name}"
                    while name in used:
                        name += "_"
                    used.add(name)
                    exists.append((name, x.type))
                    terms.append(S.QVar(name, x.type))
            calls.append((m, S.ProcConst(self.contract, p.name), tuple(terms)))
        e = self.sh.body
        for m, pc, terms in reversed(calls):
            e = S.Modal(m.sender, m.contract, pc, terms, m.value, m.blocks, e)
        for name, t in reversed(exists):
            e = S.Quant("exists", name, t, e)
        e = S.BinOp("->", self.sh.premise, e)
        for v, t in reversed(self.sh.univ):
            e = S.Quant("forall", v, t, e)
        text = "; ".join(f"{pc.proc}({', '.join(pretty.expr(x) for x in terms)})"
                         for _, pc, terms in calls)
        return text, S.Property(f"{self.prop.name}__c{len(self.tried)}", e, None, self.prop.pos)

    def _term(self, env: dict, value) -> S.Expr:
        for v, _ in self.sh.univ:
            if env.get(v) == value:
                return S.QVar(v, S.ADDRESS)
        if value == NULL or value not in {c.name for c in self.program.contracts}:
            return S.NullLit()
        return S.ContractAddr(value)
