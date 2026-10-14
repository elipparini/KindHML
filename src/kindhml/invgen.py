"""Generation of candidate invariants for Houdini (DESIGN.md, Sect. 6, "Invariant generation").

Kind 2's invariant generators relate pairs of terms of the Lustre program; on the nonlinear
use cases they exceeded the memory, and they cannot express the invariants that the proofs
of the use cases need: sums over the addresses (AMM Shares, lending Totals) and polynomial
relations (lending Exchange_rate). The candidates below come from templates over the fields
of the contracts (f, g numeric fields, m mappings to numbers, c constants of the contracts):

* signs:        f >= 0;  f > 0;  forall u. m[u] >= 0
* bounds:       f >= c;  f <= c
* positivity:   (f > 0) == (g > 0);  f > 0 -> g > 0
* holders:      forall u. !is_EOA(u) -> m[u] == 0         (only users hold m);
                m[null] == 0;  m[null] >= 0              (quantifiers exclude null)
* totals:       sum(m) == f;  sum(m) <= f;  forall u. m[u] <= f
* reserves:     sum(m) == balance[C];  sum(m) <= balance[C], for a contract C (the funds
                that the users can claim are held by C)
* definitions:  G -> f == e, for an assignment f = e under the conditions G of the
                enclosing ifs, with e over fields and constants; G && d != 0 -> f * d == e',
                for f = e' / d
* addresses:    a != null, for an address field a

They are written as source text and type-checked like invariants written by the user. A
candidate false in a reachable state of the fuzzer (random transactions run by the reference
interpreter) is discarded at once, as Daikon does; Houdini proves the others or drops them.
The rules then assume the proved ones not implied by others (`minimize`).
"""

from __future__ import annotations

import time
from fractions import Fraction
from typing import Dict, List, Optional, Tuple

from . import syntax as S
from .builder import parse_expr
from .errors import KindHMLError
from .fuzz import Fuzzer
from .lustre import render_real
from .reference import FormulaEvaluator
from .typecheck import check_rule

PREFIX = "_gen_"


def _const(v) -> Optional[str]:
    v = Fraction(v)
    if v.denominator == 1:
        return str(v.numerator)
    text = render_real(abs(v))
    if "/" in text:
        return None
    return text if v >= 0 else f"-{text}"


def _text(e: S.Expr) -> Optional[str]:
    """Source text of a resolved expression over fields and constants (None otherwise)."""
    if isinstance(e, S.Field):
        return f"{e.contract}.{e.name}"
    if isinstance(e, (S.IntLit, S.RealLit)):
        c = _const(e.value)
        return f"({c})" if c is not None else None
    if isinstance(e, S.BoolLit):
        return "true" if e.value else "false"
    if isinstance(e, S.ToReal):
        return _text(e.arg)
    if isinstance(e, S.UnOp):
        a = _text(e.arg)
        return None if a is None else f"({e.op}{a})"
    if isinstance(e, S.BinOp):
        a, b = _text(e.left), _text(e.right)
        return None if a is None or b is None else f"({a} {e.op} {b})"
    return None


def _fields(e: S.Expr) -> set:
    out = set()
    if isinstance(e, S.Field):
        out.add((e.contract, e.name))
    for name in getattr(e, "__dataclass_fields__", ()):
        v = getattr(e, name)
        for x in (v if isinstance(v, tuple) else (v,)):
            if isinstance(x, S.Expr):
                out |= _fields(x)
    return out


def _constants(program: S.Program) -> List[Fraction]:
    found = {Fraction(0), Fraction(1)}

    def visit(x):
        if isinstance(x, (S.IntLit, S.RealLit)):
            found.add(Fraction(x.value))
        elif isinstance(x, tuple):
            for y in x:
                visit(y)
        elif hasattr(x, "__dataclass_fields__"):
            for n in x.__dataclass_fields__:
                visit(getattr(x, n))
    visit(program.contracts)
    return sorted(found)


def _definitions(program: S.Program) -> List[str]:
    """Candidates from the assignments f = e of the contracts (see the module docstring)."""
    out: List[str] = []

    def visit(s: S.Stmt, guards: List[str], c: S.Contract):
        if isinstance(s, S.Seq):
            for x in s.stmts:
                visit(x, guards, c)
        elif isinstance(s, S.If):
            g = _text(s.cond)
            if g is None:
                return
            visit(s.then, guards + [g], c)
            visit(s.orelse, guards + [f"(!{g})"], c)
        elif isinstance(s, S.Assign) and s.key is None:
            f = (c.name, s.target)
            if f in _fields(s.value):
                return                          # f = f * 1.1: not a definition
            value = s.value.arg if isinstance(s.value, S.ToReal) else s.value
            lhs = f"{c.name}.{s.target}"
            if isinstance(value, S.BinOp) and value.op == "/":
                num, den = _text(value.left), _text(value.right)
                if num is not None and den is not None:
                    g = " && ".join(guards + [f"{den} != 0"])
                    out.append(f"({g}) -> {lhs} * {den} == {num}")
                return
            e = _text(value)
            if e is not None:
                out.append(f"({' && '.join(guards)}) -> {lhs} == {e}" if guards
                           else f"{lhs} == {e}")

    for c in program.contracts:
        for p in c.procs:
            visit(p.body, [], c)
    return out


def _templates(program: S.Program) -> List[Tuple[str, tuple]]:
    """The candidate invariants, as source text, each with a key that describes it (used to
    find the candidates implied by others, `minimize`)."""
    nums, maps, addrs = [], [], []
    for c in program.contracts:
        for f in c.fields:
            name = f"{c.name}.{f.name}"
            if isinstance(f.type, S.MapType):
                if S.is_num(f.type.value):
                    maps.append(name)
            elif S.is_num(f.type):
                nums.append(name)
            elif f.type == S.ADDRESS:
                addrs.append(name)
    out: List[Tuple[str, tuple]] = []
    for f in nums:
        out += [(f"{f} >= 0", ("ge", f, Fraction(0))), (f"{f} > 0", ("gt", f))]
        for c in _constants(program):
            text = _const(c)
            if text is not None and c != 0:
                out += [(f"{f} >= ({text})", ("ge", f, c)), (f"{f} <= ({text})", ("le", f, c))]
    for i, f in enumerate(nums):
        for g in nums[i + 1:]:
            out.append((f"({f} > 0) == ({g} > 0)", ("peq", f, g)))
        for g in nums:
            if g != f:
                out.append((f"{f} > 0 -> {g} > 0", ("pimp", f, g)))
    for m in maps:
        # address quantifiers exclude null, but sum(m) includes m[null]: without these, a
        # free state may have m[null] < 0, and sum(m) == f no longer bounds the entries
        out += [(f"{m}[null] == 0", ("null_eq", m)), (f"{m}[null] >= 0", ("null_ge", m))]
        out.append((f"forall _u : address . {m}[_u] >= 0", ("all_ge", m)))
        out.append((f"forall _u : address . !is_EOA(_u) -> {m}[_u] == 0", ("holders", m)))
        for f in nums:
            out += [(f"sum({m}) == {f}", ("sum_eq", m, f)), (f"sum({m}) <= {f}", ("sum_le", m, f)),
                    (f"forall _u : address . {m}[_u] <= {f}", ("entry_le", m, f))]
        for c in program.contracts:
            b = f"balance[{c.name}]"
            out += [(f"sum({m}) == {b}", ("sum_eq", m, b)), (f"sum({m}) <= {b}", ("sum_le", m, b))]
    for a in addrs:
        out.append((f"{a} != null", ("addr", a)))
    out += [(t, ("def", t)) for t in _definitions(program)]
    return list(dict(out).items())            # without duplicates, in order


def templates(program: S.Program) -> List[str]:
    """The candidate invariants, as source text."""
    return [t for t, _ in _templates(program)]


def minimize(keys: List[tuple]) -> List[tuple]:
    """The keys of the candidates not implied by others among `keys` (syntactically):
    f >= c by f >= c' (c' > c) or, for c <= 0, by f > 0; f > 0 by f >= c (c > 0);
    f <= c by f <= c' (c' < c); f > 0 -> g > 0 by (f > 0) == (g > 0) or by g positive;
    (f > 0) == (g > 0) by f and g positive; sum(m) <= f by sum(m) == f; m[null] >= 0 by
    m[null] == 0. Fewer, stronger premises are faster for the solvers."""
    ks = set(keys)
    ge = {}
    for k in ks:
        if k[0] == "ge":
            ge.setdefault(k[1], []).append(k[2])

    def positive(f):
        return ("gt", f) in ks or any(c > 0 for c in ge.get(f, []))

    def implied(k) -> bool:
        kind = k[0]
        if kind == "ge":
            return any(c > k[2] for c in ge.get(k[1], [])) or (k[2] <= 0 and ("gt", k[1]) in ks)
        if kind == "gt":
            return any(c > 0 for c in ge.get(k[1], []))
        if kind == "le":
            return any(x[0] == "le" and x[1] == k[1] and x[2] < k[2] for x in ks)
        if kind == "pimp":
            return (("peq", k[1], k[2]) in ks or ("peq", k[2], k[1]) in ks
                    or positive(k[2]))
        if kind == "peq":
            return positive(k[1]) and positive(k[2])
        if kind == "sum_le":
            return ("sum_eq", k[1], k[2]) in ks
        if kind == "null_ge":
            return ("null_eq", k[1]) in ks
        return False
    return [k for k in keys if not implied(k)]


def _typed(program: S.Program) -> List[Tuple[S.Rule, tuple]]:
    """The templates as resolved invariants, with their keys (ill-typed ones are left out)."""
    out = []
    for i, (text, key) in enumerate(_templates(program)):
        try:
            raw = S.Rule(f"{PREFIX}{i}", parse_expr(text), invariant=True)
            out.append((check_rule(program, raw), key))
        except KindHMLError:
            pass
    return out


def candidates(program: S.Program) -> List[S.Rule]:
    """The templates as resolved invariants (ill-typed ones are left out)."""
    return [r for r, _ in _typed(program)]


def generate(program: S.Program, fuzzer: Fuzzer,
             seconds: float = 2.0) -> Tuple[List[S.Rule], int, Dict[str, tuple]]:
    """The candidates that hold in the reachable states (all contracts constructed) of
    random traces explored for `seconds`; also returns the number of candidates, and the
    keys of the candidates (for `minimize`, which is applied after Houdini, to the proved
    ones: before, a candidate implied by a false one would be lost, e.g. res0 > 0 -> sc0 > 0
    by (res0 > 0) == (sc0 > 0), false when all the reserves are borrowed)."""
    typed = _typed(program)
    key_of = {r.name: k for r, k in typed}
    rules = [r for r, _ in typed]
    ev = FormulaEvaluator(fuzzer.system, range(-1, 4))
    alive = list(rules)
    deadline = time.time() + seconds
    while time.time() < deadline and alive:
        for _, st in fuzzer.traces():
            if not all(st.constructed.values()):
                continue
            keep = []
            for r in alive:
                try:
                    ok = ev.holds(r.formula, [st])
                except (ZeroDivisionError, KeyError, TypeError):
                    ok = True                 # unspecified value: left to Houdini
                if ok:
                    keep.append(r)
            alive = keep
    return alive, len(rules), key_of
