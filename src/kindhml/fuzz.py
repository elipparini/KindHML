"""Search of counterexamples by random testing (task "fuzz" of the portfolio, DESIGN.md,
Sect. 6).

Random sequences of transactions are run by the reference interpreter from random initial
states, so their states are reachable. The property is evaluated on these states with bounded
quantifiers (`reference.FormulaEvaluator`, with a random sample of the arguments of all
procedures when they are too many). A state where it fails is only a candidate: a bounded
existential may have missed its witness. Kind 2 then evaluates the exact formula at that
concrete state (`Checks.concrete_check`); if the formula is false there, the state, with the
transactions that reach it, is a counterexample.

Kind 2 alone rarely finds such counterexamples when the transitions are nonlinear: on the
integer AMM, BMC reaches depth 1 in 60 s, while a counterexample needs a constructor, a
deposit and a swap.

A counterexample to induction s* (a free state that satisfies the proved invariants and
violates the property) guides the search (`guided`): at each step, of a few random
transactions, the one whose state is closest to s* is taken. s* itself may be unreachable,
but the reachable states near it often violate the property too: on lending-simple-int,
1 random state in 64,776 satisfies the premise of the liquidation attacks, and the guided
search finds a counterexample of Liquidation_attack within 1 s (DESIGN.md, Sect. 6).
"""

from __future__ import annotations

import random
import signal
import time
from fractions import Fraction
from typing import Dict, Iterator, List, Optional, Tuple

from . import syntax as S
from .model import NULL, System
from .reference import FormulaEvaluator, Interpreter, State, Tx, initial_state

INT_DOMAIN = range(-1, 4)       # bounded quantifiers of the evaluation (candidates only)
MAX_RECORDS = 20                # sampled assignments of the arguments of all procedures
MAX_STEPS = 12                  # transactions of a trace after the constructors
GUIDED_TRIES = 20               # random transactions compared at each step of `guided`
GUIDED_RANDOM = 0.2             # probability of a random step instead of the closest one
MISMATCH = 5                    # distance between two different addresses or booleans


class _TooSlow(Exception):
    pass


def _alarm(signum, frame):
    raise _TooSlow()


class Fuzzer:
    def __init__(self, system: System, seed: str = "kindhml"):
        self.system = system
        self.interp = Interpreter(system)
        self.rnd = random.Random(seed)
        self.ev = FormulaEvaluator(system, INT_DOMAIN, max_records=MAX_RECORDS, rnd=self.rnd)
        self.seen: dict = {}            # property name -> states already proposed (`states`)

    # ------------------------------------------------------------ random values

    def number(self, t: S.Type, pool=()):
        """A random number of type t; half of the time, if `pool` (the positive numbers of
        the current state) is not empty, one of them, or its half or quarter: amounts that
        fit the wallets and reserves make the transactions succeed more often."""
        r = self.rnd
        if pool and r.random() < 0.5:
            v = Fraction(r.choice(pool)) / r.choice([1, 1, 2, 4])
            return v if t == S.REAL else int(v)
        if t == S.REAL:
            return Fraction(r.choice([0, 1, 2, 3, 4, 6, 10, r.randint(0, 40)]),
                            r.choice([1, 1, 1, 2, 4]))
        n = r.choice([0, 1, 1, 2, 3, 4, 5, 7, 10, 100, r.randint(-2, 20)])
        return max(n, 0) if t == S.UINT else n

    def value(self, t: S.AnyType, pool=()):
        if isinstance(t, S.MapType):
            return {a: self.value(t.value) for a in self.system.addresses}
        if t == S.BOOL:
            return self.rnd.random() < 0.5
        if t == S.ADDRESS:
            r = self.rnd.random()
            if r < 0.7:
                return self.rnd.choice(self.system.users)
            return self.rnd.choice(self.system.addresses)
        return self.number(t, pool)

    def amount(self, pool=()):
        return self.number(self.system.program.balance_type, pool)

    @staticmethod
    def pool(st: Optional[State]) -> List:
        """The positive numbers of a state."""
        if st is None:
            return []
        out = [v for v in st.balance.values() if v > 0]
        for v in st.fields.values():
            for x in (v.values() if isinstance(v, dict) else [v]):
                if not isinstance(x, (bool, str)) and x > 0:
                    out.append(x)
        return out

    @staticmethod
    def addresses(st: Optional[State]) -> List[str]:
        """The users stored in address fields of a state (e.g. an owner or an oracle)."""
        if st is None:
            return []
        out = []
        for v in st.fields.values():
            for x in (v.values() if isinstance(v, dict) else [v]):
                if isinstance(x, str) and not x.startswith("A_"):
                    out.append(x)
        return out

    def transaction(self, c: S.Contract, p: S.Procedure, st: Optional[State] = None) -> Tx:
        pool = self.pool(st)
        stored = [a for a in self.addresses(st) if a in self.system.users]
        r = self.rnd.random()
        if stored and r < 0.2:
            # procedures restricted to an owner or an oracle succeed only with that sender
            sender = self.rnd.choice(stored)
        elif r < 0.95:
            sender = self.rnd.choice(self.system.users)
        else:
            sender = self.rnd.choice(self.system.addresses)
        args = {x.name: self.value(x.type, pool) for x in p.params}
        value = self.amount(pool) if p.payable else 0
        blocks = self.rnd.choice([0, 0, 1, 2, 5, 10]) if self.system.uses_block_num else 0
        return Tx(sender, c.name, (c.name, p.name), args, value, blocks)

    # ------------------------------------------------------------ traces

    def traces(self) -> Iterator[Tuple[List[Tx], State]]:
        """The states of a random trace, each with the transactions that reach it: the
        constructors first, then up to 12 random transactions (reverted ones left out)."""
        amount = self.system.program.balance_type
        st = initial_state(self.system, {a: abs(self.number(amount))
                                         for a in self.system.addresses if a != NULL},
                           self.rnd.choice([0, 1, 10]))
        txs: List[Tx] = []
        yield list(txs), st
        for c in self.system.contracts:
            for _ in range(5):                  # a few attempts to construct c
                tx = self.transaction(c, c.procs[0])
                nxt = self.interp.step(st, tx)
                if not nxt.revert:
                    st = nxt
                    txs.append(tx)
                    yield list(txs), st
                    break
        methods = [(c, p) for c, p in self.system.methods if p.name != S.CONSTRUCTOR]
        for _ in range(self.rnd.randint(1, MAX_STEPS)):
            if not methods:
                return
            tx = self.transaction(*self.rnd.choice(methods), st)
            nxt = self.interp.step(st, tx)
            if nxt.revert:                      # reverted transactions are left out
                continue
            st = nxt
            txs.append(tx)
            yield list(txs), st

    def candidates(self, prop: S.Property, seconds: float,
                   limit: int = 3) -> List[Tuple[List[Tx], State]]:
        """Reachable states where the bounded evaluation of the property is false, found within
        `seconds` (properties and invariants are required in states where all contracts are
        constructed). For a property with an existential quantifier over numbers in
        positive position, the bounded evaluation almost always misses the witnesses (e.g.
        the values carried across the branches of an additivity property): then any new
        reachable state is a candidate, and only the exact check decides."""
        if has_witness(prop.formula):
            return self.states(prop, seconds, limit)
        out: List[Tuple[List[Tx], State]] = []
        deadline = time.time() + seconds
        old = signal.signal(signal.SIGALRM, _alarm)
        try:
            while time.time() < deadline and len(out) < limit:
                for txs, st in self.traces():
                    left = deadline - time.time()
                    if left <= 0 or len(out) >= limit:
                        break
                    if not all(st.constructed.values()):
                        continue
                    try:
                        if self._violates(prop, st, left):
                            out.append((txs, st))
                    except _TooSlow:
                        break
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, old)
        return out

    def _violates(self, prop: S.Property, st: State, seconds: float) -> bool:
        """Whether the bounded evaluation of the property is false at st; _TooSlow if it
        takes more than `seconds` (the caller installs `_alarm`)."""
        signal.setitimer(signal.ITIMER_REAL, seconds)
        try:
            return not self.ev.holds(prop.formula, [st])
        except (ZeroDivisionError, KeyError, TypeError):
            return False        # unspecified values (unguarded division) in a property
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)

    def guided(self, prop: S.Property, target: Dict[tuple, object], seconds: float,
               limit: int = 3, filtered: bool = True) -> List[Tuple[List[Tx], State]]:
        """The candidates of `candidates`, on traces that go towards `target` (values by
        location, `locations`; e.g. a counterexample to induction): after the constructors,
        at each step, of GUIDED_TRIES random transactions that do not revert, the one whose
        state is closest to the target (`distance`), or, with probability GUIDED_RANDOM, a
        random one. The property is evaluated only at the states closer to the target than
        the earlier ones of their trace (the evaluation takes most of the time: on
        lending-simple-int, this halves the time to a candidate). For a property with a
        witness (see `candidates`), the candidate of a trace is its closest state to the
        target where the bounded evaluation is false, if not returned before: near the
        target, the bounded evaluation is a useful filter (on lending-simple-int,
        Liquidation_attack_exists holds wherever its premise fails). Without `filtered`, when
        the exact checks are cheap (z3 directly, `direct.py`), it is the closest state of the
        trace: on amm_real_v4 Sandwich_slippage, the filter rejected almost every state near
        the target (one candidate in 12 s), while the closest state of the first trace
        violates the property."""
        methods = [(c, p) for c, p in self.system.methods if p.name != S.CONSTRUCTOR]
        witness = has_witness(prop.formula)
        seen = self.seen.setdefault(prop.name, set())
        out: List[Tuple[List[Tx], State]] = []
        deadline = time.time() + seconds
        old = signal.signal(signal.SIGALRM, _alarm)
        try:
            while methods and time.time() < deadline and len(out) < limit:
                start = self.constructed()
                if start is None:
                    continue
                txs, st = start
                best = (distance(st, target), txs, st)
                closest = None          # a property with a witness: the candidate of the trace
                for _ in range(MAX_STEPS):
                    left = deadline - time.time()
                    if left <= 0:
                        break
                    steps = []
                    for _ in range(GUIDED_TRIES):
                        tx = self.transaction(*self.rnd.choice(methods), st)
                        nxt = self.interp.step(st, tx)
                        if not nxt.revert:
                            steps.append((distance(nxt, target), tx, nxt))
                    if not steps:
                        break
                    d, tx, st = (self.rnd.choice(steps) if self.rnd.random() < GUIDED_RANDOM
                                 else min(steps, key=lambda s: s[0]))
                    txs = txs + [tx]
                    if d >= best[0]:
                        continue
                    best = (d, txs, st)
                    if witness and not filtered:
                        closest = (txs, st)
                    elif self._violates(prop, st, left):
                        if not witness:
                            out.append((txs, st))
                            break
                        closest = (txs, st)
                if closest is not None and _key(closest[1]) not in seen:
                    seen.add(_key(closest[1]))
                    out.append(closest)
        except _TooSlow:
            pass
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, old)
        return out

    def constructed(self) -> Optional[Tuple[List[Tx], State]]:
        """The first state of a random trace where all contracts are constructed, with its
        transactions, or None."""
        for txs, st in self.traces():
            if all(st.constructed.values()):
                return txs, st
        return None

    def states(self, prop: S.Property, seconds: float,
               limit: int) -> List[Tuple[List[Tx], State]]:
        """Distinct reachable states with all contracts constructed, not returned before:
        the last of random traces."""
        out: List[Tuple[List[Tx], State]] = []
        deadline = time.time() + seconds
        while time.time() < deadline and len(out) < limit:
            last = None
            for txs, st in self.traces():
                if all(st.constructed.values()):
                    last = (txs, st)
            if last is None:
                continue
            seen = self.seen.setdefault(prop.name, set())
            if _key(last[1]) not in seen:
                seen.add(_key(last[1]))
                out.append(last)
        return out


def _key(st: State) -> str:
    return repr(sorted(st.fields.items())) + repr(sorted(st.balance.items()))


def locations(st: State) -> Dict[tuple, object]:
    """The values of a state by location: (None, a) for the balance of a, (c, f) for a field
    of contract c, (c, f, a) for the entry of a in a map field."""
    out: Dict[tuple, object] = {(None, a): v for a, v in st.balance.items()}
    for (c, f), v in st.fields.items():
        if isinstance(v, dict):
            out.update({(c, f, a): x for a, x in v.items()})
        else:
            out[(c, f)] = v
    return out


def distance(st: State, target: Dict[tuple, object]):
    """The distance from a state to the target values (by location, `locations`): the sum of
    the differences of the numbers, plus MISMATCH for each other value that differs."""
    have = locations(st)
    d = 0
    for loc, v in target.items():
        x = have.get(loc)
        if _number(x) and _number(v):
            d += abs(x - v)
        elif x != v:
            d += MISMATCH
    return d


def _number(x) -> bool:
    return isinstance(x, (int, Fraction)) and not isinstance(x, bool)


def has_witness(e: S.Expr, positive: bool = True) -> bool:
    """Whether e has an existential quantifier over int, uint or real in positive position
    (or a universal one in negative position)."""
    if isinstance(e, S.Quant):
        if e.type in (S.INT, S.UINT, S.REAL) and (e.kind == "exists") == positive:
            return True
        return has_witness(e.body, positive)
    if isinstance(e, S.UnOp) and e.op == "!":
        return has_witness(e.arg, not positive)
    if isinstance(e, S.BinOp) and e.op == "->":
        return has_witness(e.left, not positive) or has_witness(e.right, positive)
    if isinstance(e, S.BinOp) and e.op in ("&&", "||"):
        return has_witness(e.left, positive) or has_witness(e.right, positive)
    if isinstance(e, S.Modal):
        return has_witness(e.body, positive)
    return False
