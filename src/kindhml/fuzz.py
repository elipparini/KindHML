"""Search of counterexamples by random testing (task "fuzz" of the portfolio, DESIGN.md,
Sect. 6).

Random sequences of transactions are run by the reference interpreter from random initial
states, so their states are reachable. The rule is evaluated on these states with bounded
quantifiers (`reference.FormulaEvaluator`, with a random sample of the arguments of all
procedures when they are too many). A state where it fails is only a candidate: a bounded
existential may have missed its witness. Kind 2 then evaluates the exact formula at that
concrete state (`Checks.concrete_check`); if the formula is false there, the state, with the
transactions that reach it, is a counterexample.

Kind 2 alone rarely finds such counterexamples when the transitions are nonlinear: on the
integer AMM, BMC reaches depth 1 in 60 s, while a counterexample needs a constructor, a
deposit and a swap.
"""

from __future__ import annotations

import random
import signal
import time
from fractions import Fraction
from typing import Iterator, List, Optional, Tuple

from . import syntax as S
from .model import NULL, System
from .reference import FormulaEvaluator, Interpreter, State, Tx, initial_state

INT_DOMAIN = range(-1, 4)       # bounded quantifiers of the evaluation (candidates only)
MAX_RECORDS = 20                # sampled assignments of the arguments of all procedures


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
        self.seen: dict = {}            # rule name -> states already proposed (`states`)

    # ------------------------------------------------------------ random values

    def number(self, t: S.Type):
        r = self.rnd
        if t == S.REAL:
            return Fraction(r.choice([0, 1, 2, 3, 4, 6, 10, r.randint(0, 40)]),
                            r.choice([1, 1, 1, 2, 4]))
        n = r.choice([0, 1, 1, 2, 3, 4, 5, 7, 10, 100, r.randint(-2, 20)])
        return max(n, 0) if t == S.UINT else n

    def value(self, t: S.AnyType):
        if isinstance(t, S.MapType):
            return {a: self.value(t.value) for a in self.system.addresses}
        if t == S.BOOL:
            return self.rnd.random() < 0.5
        if t == S.ADDRESS:
            r = self.rnd.random()
            if r < 0.7:
                return self.rnd.choice(self.system.users)
            return self.rnd.choice(self.system.addresses)
        return self.number(t)

    def amount(self):
        return self.number(self.system.program.balance_type)

    def transaction(self, c: S.Contract, p: S.Procedure) -> Tx:
        sender = (self.rnd.choice(self.system.users) if self.rnd.random() < 0.95
                  else self.rnd.choice(self.system.addresses))
        args = {x.name: self.value(x.type) for x in p.params}
        value = self.amount() if p.payable else 0
        blocks = self.rnd.choice([0, 0, 1, 2, 5, 10]) if self.system.uses_block_num else 0
        return Tx(sender, c.name, (c.name, p.name), args, value, blocks)

    # ------------------------------------------------------------ traces

    def traces(self) -> Iterator[Tuple[List[Tx], State]]:
        """The states of a random trace, each with the transactions that reach it: the
        constructors first, then up to 6 random transactions."""
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
        for _ in range(self.rnd.randint(1, 8)):
            if not methods:
                return
            tx = self.transaction(*self.rnd.choice(methods))
            nxt = self.interp.step(st, tx)
            if nxt.revert:                      # reverted transactions are left out
                continue
            st = nxt
            txs.append(tx)
            yield list(txs), st

    def candidates(self, rule: S.Rule, seconds: float,
                   limit: int = 3) -> List[Tuple[List[Tx], State]]:
        """Reachable states where the bounded evaluation of the rule is false, found within
        `seconds` (rules and invariants are required in states where all contracts are
        constructed). For a rule with an existential quantifier over numbers in
        positive position, the bounded evaluation almost always misses the witnesses (e.g.
        the values carried across the branches of an additivity rule): then any new
        reachable state is a candidate, and only the exact check decides."""
        if has_witness(rule.formula):
            return self.states(rule, seconds, limit)
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
                    signal.setitimer(signal.ITIMER_REAL, left)
                    try:
                        if not self.ev.holds(rule.formula, [st]):
                            out.append((txs, st))
                    except _TooSlow:
                        break
                    except (ZeroDivisionError, KeyError, TypeError):
                        pass          # unspecified values (unguarded division) in a rule
                    finally:
                        signal.setitimer(signal.ITIMER_REAL, 0)
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, old)
        return out

    def states(self, rule: S.Rule, seconds: float,
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
            key = repr(sorted(last[1].fields.items())) + repr(sorted(last[1].balance.items()))
            seen = self.seen.setdefault(rule.name, set())
            if key not in seen:
                seen.add(key)
                out.append(last)
        return out


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
