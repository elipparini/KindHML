"""Cutoffs on the number of users (parameterized mode; DESIGN.md, Sect. 7).

A check on free values (`invariants.py`) is a verification condition χ = P ⇒ Q: P the
premises (invariants, axioms), Q a property, or the candidates after a call. Read in
first-order logic, with a sort of addresses whose only constants are null and the contracts,
χ is in the *fragment* if
* no map has address values, and no sum over the addresses occurs (in parameterized mode,
  sum(m) is a state variable: `System.ghost_sums`);
* in ¬χ, no address existential is in the scope of a universal quantifier, unless the
  latter ranges over a finite domain independent of the users (methods, booleans).
Then ¬χ is equivalent to ∃ā ∀ȳ. ψ with ψ quantifier-free and ā of k addresses: the address
fields of the free state and the outermost address existentials of ¬χ (`Scanner.skolems`).

Lemma (substructure). If ¬χ holds with n users, it holds with any n' users,
max(1, k) <= n' <= n. Proof: keep null, the contracts, the values of ā, and further users up
to n'; the restriction is a substructure, and universal sentences hold in substructures.

So, with the cutoff c = max(1, k): χ valid with c users implies χ valid with every n >= c.
Each check has its own cutoff: the steps of Houdini (`Checks.step_count`) and each property
(`Checks.property_count`) are checked with their own numbers of users.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from . import syntax as S
from .encode_trans import BALANCE, field_var, key_field
from .model import System


class OutOfFragment(Exception):
    """A check outside the fragment: no cutoff."""


@dataclass
class Cutoff:
    """Upper bounds on the cutoffs of the checks of a file, with all the candidates: the
    steps of Houdini, and each property on a free state. A property outside the fragment has none,
    and is checked as without parameterized mode; if a step is outside the fragment, no property
    has one."""
    steps: Optional[int]                      # max(1, the counts of the steps); None: outside
    reason: str = ""                          # why the steps have no cutoff
    checks: Dict[str, int] = field(default_factory=dict)   # the count k of each check
    outside: Dict[str, str] = field(default_factory=dict)  # property -> why it has none

    def of_property(self, name: str) -> Optional[int]:
        """The least number of users for which a verdict on the property `name` can be claimed
        for every larger number: max(steps, its own cutoff); None outside the fragment."""
        if self.steps is None or name in self.outside:
            return None
        return max(self.steps, self.checks.get(f"property {name}", 1))

    def describe(self) -> str:
        if self.steps is None:
            return f"no cutoff ({self.reason})"
        properties = [max(1, v) for k, v in self.checks.items() if k.startswith("property ")]
        out = f"cutoffs: steps of Houdini <= {self.steps}"
        if properties:
            out += (f", properties {min(properties)}" if min(properties) == max(properties)
                    else f", properties {min(properties)}-{max(properties)}")
        if self.outside:
            out += f", {len(self.outside)} properties outside the fragment"
        return out


def _has_binder(e) -> bool:
    """Whether e contains a quantifier or a modality."""
    if isinstance(e, (S.Quant, S.Modal)):
        return True
    for name in getattr(e, "__dataclass_fields__", ()):
        v = getattr(e, name)
        for x in (v if isinstance(v, tuple) else (v,)):
            if isinstance(x, S.Expr) and _has_binder(x):
                return True
    return False


class Scanner:
    """Counts the address Skolem constants of ¬χ, for a formula occurring in χ with a given
    polarity (`positive`: as in χ itself; a premise is negative)."""

    def __init__(self, system: System):
        self.methods = sum(1 for _, p in system.methods if p.name != S.CONSTRUCTOR)
        # per contract, the parameters of the procedures a method variable can denote (not
        # the constructor): only those of the called procedure matter in a modality
        self.params: Dict[str, int] = {}
        self.addr_params: Dict[str, int] = {}
        for c, p in system.methods:
            if p.name != S.CONSTRUCTOR:
                self.params[c.name] = self.params.get(c.name, 0) + len(p.params)
                self.addr_params[c.name] = self.addr_params.get(c.name, 0) + sum(
                    1 for x in p.params if x.type == S.ADDRESS)

    @staticmethod
    def _callees(var: str, e) -> set:
        """The contracts called by the modalities of e whose arguments are the variable var
        (of type calldataargs)."""
        out = set()
        if isinstance(e, S.Modal) and any(isinstance(a, S.QVar) and a.name == var
                                          for a in e.args):
            out.add(e.contract)
        for name in getattr(e, "__dataclass_fields__", ()):
            v = getattr(e, name)
            for x in (v if isinstance(v, tuple) else (v,)):
                if isinstance(x, S.Expr):
                    out |= Scanner._callees(var, x)
        return out

    def _args(self, e: S.Quant) -> Tuple[int, int]:
        """(parameters, address parameters) that matter for the calldataargs variable of e:
        those of the procedures, other than the constructors, of the contracts it calls."""
        callees = self._callees(e.var, e.body)
        return (sum(self.params.get(c, 0) for c in callees),
                sum(self.addr_params.get(c, 0) for c in callees))

    def skolems(self, e: S.Expr, positive: bool, blocked: bool = False) -> int:
        """The number of address existentials of ¬χ in e (Skolem constants), bounded from
        above: through a disjunction of ¬χ, the larger count (the witnesses can be shared);
        through a conjunction, the sum. `blocked`: e is in the scope of a universal of ¬χ
        over an infinite or address domain. Raises OutOfFragment."""
        if not _has_binder(e):
            return 0
        if isinstance(e, S.Quant):
            existential = (e.kind == "forall") == positive      # in ¬χ
            body = lambda b: self.skolems(e.body, positive, b)
            if e.type == S.ADDRESS:
                if not existential:
                    return body(True)
                if blocked:
                    raise OutOfFragment(f"address existential '{e.var}' under a universal")
                return 1 + body(blocked)
            if e.type == S.ARGS:
                params, addrs = self._args(e)
                if not existential:
                    return body(blocked or params > 0)
                if blocked and addrs:
                    raise OutOfFragment(f"address arguments '{e.var}' under a universal")
                return addrs + body(blocked)
            if e.type in (S.METHOD, S.BOOL):
                # a universal over a finite domain: one copy of the witnesses per value
                size = self.methods if e.type == S.METHOD else 2
                return body(blocked) * (1 if existential else size)
            return body(blocked or not existential)            # numbers
        if isinstance(e, S.Modal):
            for x in (e.sender, e.proc, e.value, e.blocks) + tuple(e.args):
                if _has_binder(x):
                    raise OutOfFragment("a quantifier inside a term")
            k = 0
            if isinstance(e.proc, S.QVar) and not e.args:
                # h(): its parameters are existential in χ (DESIGN.md, Sect. 4)
                if positive:
                    blocked = blocked or self.params.get(e.contract, 0) > 0
                elif self.addr_params.get(e.contract, 0):
                    if blocked:
                        raise OutOfFragment("address arguments of h() under a universal")
                    k = self.addr_params[e.contract]
            return k + self.skolems(e.body, positive, blocked)    # Trans is a function
        if isinstance(e, S.UnOp) and e.op == "!":
            return self.skolems(e.arg, not positive, blocked)
        if isinstance(e, S.Old):
            return self.skolems(e.arg, positive, blocked)
        if isinstance(e, S.BinOp) and e.op in ("&&", "||", "->"):
            a = self.skolems(e.left, positive if e.op != "->" else not positive, blocked)
            b = self.skolems(e.right, positive, blocked)
            # in ¬χ: a disjunction for a positive && and for a negative || or ->
            disjunction = (e.op == "&&") == positive
            return max(a, b) if disjunction else a + b
        if isinstance(e, S.BinOp) and e.op in ("==", "!="):
            # an equivalence of formulas: both polarities of both sides
            return sum(self.skolems(x, p, blocked) for x in (e.left, e.right)
                       for p in (True, False))
        raise OutOfFragment(f"a quantifier inside {type(e).__name__}")

    def dual(self, e: S.Expr) -> bool:
        """Whether some address variable of e is universal in ¬e. If not, ¬e is preserved
        when idle users are added (Lemma 7.5, DESIGN.md, Sect. 7)."""
        return self.idle_needed(e) > 0

    def idle_needed(self, e: S.Expr, positive: bool = True) -> int:
        """The number of idle users that a counterexample of e needs to extend to more users
        (Lemma 7.6): the largest number, along a branch of ¬e, of the address variables up
        to the last one universal in ¬e (an existential before a universal may take an idle
        user). 0 if no address variable is universal in ¬e (Lemma 7.5)."""
        if not _has_binder(e):
            return 0
        if isinstance(e, (S.Quant, S.Modal)):
            if isinstance(e, S.Quant):
                universal = (e.kind == "exists") == positive        # in ¬e
                count = (1 if e.type == S.ADDRESS
                         else self._args(e)[1] if e.type == S.ARGS else 0)
                inner = self.idle_needed(e.body, positive)
            else:
                # h(): its parameters are existential in e (DESIGN.md, Sect. 4)
                universal = positive
                count = (self.addr_params.get(e.contract, 0)
                         if isinstance(e.proc, S.QVar) and not e.args else 0)
                inner = self.idle_needed(e.body, positive)
            return inner + count if count and (universal or inner) else inner
        if isinstance(e, S.UnOp) and e.op == "!":
            return self.idle_needed(e.arg, not positive)
        if isinstance(e, S.Old):
            return self.idle_needed(e.arg, positive)
        if isinstance(e, S.BinOp) and e.op == "->":
            return max(self.idle_needed(e.left, not positive),
                       self.idle_needed(e.right, positive))
        if isinstance(e, S.BinOp) and e.op in ("&&", "||"):
            return max(self.idle_needed(e.left, positive), self.idle_needed(e.right, positive))
        if isinstance(e, S.BinOp) and e.op in ("==", "!="):
            return max(self.idle_needed(x, p) for x in (e.left, e.right) for p in (True, False))
        return UNBOUNDED                             # unexpected: assume the worst


UNBOUNDED = 10 ** 9


def idle_users(state: Dict[str, object], system: System) -> Dict[object, List[str]]:
    """The idle users of a state given by path (`s.f`, `s.f.k_a`, with the values of the
    reference interpreter), grouped by balance: every map entry has its default value, and
    no address field holds the user (Lemma 7.6). A user with a missing value is not idle."""
    holders = []
    maps = []
    for c in system.contracts:
        for f in c.fields:
            name = field_var(c.name, f.name)
            if f.type == S.ADDRESS:
                if f"s.{name}" not in state:
                    return {}
                holders.append(state[f"s.{name}"])
            elif isinstance(f.type, S.MapType):
                maps.append((name, False if f.type.value == S.BOOL else 0))
    out: Dict[object, List[str]] = {}
    for u in system.users:
        if u in holders:
            continue
        if all(state.get(f"s.{name}.{key_field(u)}", None) == d
               and f"s.{name}.{key_field(u)}" in state for name, d in maps):
            balance = state.get(f"s.{BALANCE}.{key_field(u)}")
            if balance is not None:
                out.setdefault(balance, []).append(u)
    return out


def check_program(system: System) -> int:
    """The number of address fields (constants of the free state). Raises OutOfFragment if
    a map has address values (a function from addresses to addresses)."""
    count = 0
    for c in system.contracts:
        for f in c.fields:
            if isinstance(f.type, S.MapType) and f.type.value == S.ADDRESS:
                raise OutOfFragment(f"the map {c.name}.{f.name} has address values")
            if f.type == S.ADDRESS:
                count += 1
    return count


def nonnegative_maps(formulas: List[S.Expr]) -> set:
    """The maps (contract, field) all of whose entries are nonnegative by `formulas`:
    `forall u : address . m[u] >= 0` (which excludes null) and `m[null] >= 0` or
    `m[null] == 0`, as the generated candidates write them, or as conjuncts of a formula
    (also under the `forall`, e.g. `forall u : address . t0[u] >= 0 && t1[u] >= 0`)."""
    def zero(e):
        return isinstance(e, (S.IntLit, S.RealLit)) and e.value == 0

    def entry(e, key):
        return (isinstance(e, S.Index) and isinstance(e.map, S.Field) and key(e.key))

    def conjuncts(e):
        if isinstance(e, S.BinOp) and e.op == "&&":
            return conjuncts(e.left) + conjuncts(e.right)
        return [e]

    every, null = set(), set()
    for f in (c for g in formulas for c in conjuncts(g)):
        if isinstance(f, S.Quant) and f.kind == "forall" and f.type == S.ADDRESS:
            for b in conjuncts(f.body):
                if (isinstance(b, S.BinOp) and b.op == ">=" and zero(b.right)
                        and entry(b.left,
                                  lambda k: isinstance(k, S.QVar) and k.name == f.var)):
                    every.add((b.left.map.contract, b.left.map.name))
        elif (isinstance(f, S.BinOp) and f.op in (">=", "==") and zero(f.right)
              and entry(f.left, lambda k: isinstance(k, S.NullLit))):
            null.add((f.left.map.contract, f.left.map.name))
    return every & null
