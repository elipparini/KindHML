"""Cutoffs on the number of users (parameterized mode; DESIGN.md, Sect. 7).

A check on free values (`invariants.py`) is a verification condition χ = P ⇒ Q: P the
premises (invariants, axioms), Q a rule, or the candidates after a call. Read in
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
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional

from . import syntax as S
from .model import System


class OutOfFragment(Exception):
    """A check outside the fragment: no cutoff."""


@dataclass
class Cutoff:
    """The cutoffs of the checks of a file: the steps of Houdini, and each rule on a free
    state. A rule outside the fragment has none, and is checked as without parameterized
    mode; if a step is outside the fragment, the file has no cutoff."""
    value: Optional[int]                      # of the steps and the rules in the fragment
    reason: str = ""                          # why the file has no cutoff
    checks: Dict[str, int] = field(default_factory=dict)   # the cutoff of each check
    outside: Dict[str, str] = field(default_factory=dict)  # rule -> why it has none

    def of_rule(self, name: str) -> Optional[int]:
        """The cutoff for the rule `name` (with the steps), or None."""
        return None if self.value is None or name in self.outside else self.value

    def describe(self) -> str:
        if self.value is None:
            return f"no cutoff ({self.reason})"
        worst = max(self.checks.items(), key=lambda x: x[1])[0] if self.checks else "-"
        out = f"cutoff {self.value} (largest: {worst})"
        if self.outside:
            out += f", {len(self.outside)} rules outside the fragment"
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
        self.params = len(system.param_vars)
        self.addr_params = sum(1 for v in system.param_vars if v.type == S.ADDRESS)

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
                if not existential:
                    return body(blocked or self.params > 0)
                if blocked and self.addr_params:
                    raise OutOfFragment(f"address arguments '{e.var}' under a universal")
                return self.addr_params + body(blocked)
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
                    blocked = blocked or self.params > 0
                elif self.addr_params:
                    if blocked:
                        raise OutOfFragment("address arguments of h() under a universal")
                    k = self.addr_params
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

    def dual(self, e: S.Expr, positive: bool = True) -> bool:
        """Whether some address variable of e is universal in ¬e. If not, ¬e is preserved
        when users with default values are added (Lemma (idle users), DESIGN.md, Sect. 7)."""
        if not _has_binder(e):
            return False
        if isinstance(e, S.Quant):
            universal = (e.kind == "exists") == positive        # in ¬e
            if universal and (e.type == S.ADDRESS
                              or (e.type == S.ARGS and self.addr_params)):
                return True
            return self.dual(e.body, positive)
        if isinstance(e, S.Modal):
            if isinstance(e.proc, S.QVar) and not e.args and positive and self.addr_params:
                return True
            return self.dual(e.body, positive)
        if isinstance(e, S.UnOp) and e.op == "!":
            return self.dual(e.arg, not positive)
        if isinstance(e, S.Old):
            return self.dual(e.arg, positive)
        if isinstance(e, S.BinOp) and e.op == "->":
            return self.dual(e.left, not positive) or self.dual(e.right, positive)
        if isinstance(e, S.BinOp) and e.op in ("&&", "||"):
            return self.dual(e.left, positive) or self.dual(e.right, positive)
        if isinstance(e, S.BinOp) and e.op in ("==", "!="):
            return any(self.dual(x, p) for x in (e.left, e.right) for p in (True, False))
        return True                                  # unexpected: assume the worst


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
    `m[null] == 0`, as the generated candidates write them."""
    def zero(e):
        return isinstance(e, (S.IntLit, S.RealLit)) and e.value == 0

    def entry(e, key):
        return (isinstance(e, S.Index) and isinstance(e.map, S.Field) and key(e.key))

    every, null = set(), set()
    for f in formulas:
        if isinstance(f, S.Quant) and f.kind == "forall" and f.type == S.ADDRESS:
            b = f.body
            if (isinstance(b, S.BinOp) and b.op == ">=" and zero(b.right)
                    and entry(b.left, lambda k: isinstance(k, S.QVar) and k.name == f.var)):
                every.add((b.left.map.contract, b.left.map.name))
        elif (isinstance(f, S.BinOp) and f.op in (">=", "==") and zero(f.right)
              and entry(f.left, lambda k: isinstance(k, S.NullLit))):
            null.add((f.left.map.contract, f.left.map.name))
    return every & null
