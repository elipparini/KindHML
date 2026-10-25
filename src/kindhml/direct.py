"""Checks on free values sent to z3 directly, for formulas with quantifiers over real numbers
(DESIGN.md, Sect. 6, "Existentials over numbers").

A check on free values (`invariants.py`) is a Lustre node property, which Kind 2 turns into one
SMT query. When the property has an existential over a real in positive position (e.g. the
amount of a swap that undoes another one), that query is not decided: Kind 2 asks it with
`check-sat-assuming`, so z3 uses its incremental solver (quantifier instantiation), and the
encoding puts divisions and if-then-else terms under the quantifier, which z3's procedure for
quantified nonlinear real arithmetic (nlqsat, complete) does not accept. On the AMM, with one
user, Kind 2 gave no answer in 15 s, while nlqsat decides the rewritten query in 0.02 s.

So the formula of the node property (after `invariants.hoist`) is translated here into a z3
term (records become their fields, Lustre functions are inlined), rewritten under each
quantifier into pure real arithmetic, and checked by the z3 binary, non-incrementally, with
nlqsat, in the memory scope of `kind2.run_command`:
* a division a / b by a non-constant b becomes a fresh variable d of the innermost quantifier
  around it (or a free constant outside quantifiers), with the definition b != 0 -> b * d = a;
* an if-then-else term ite(c, x, y) of a number type becomes a fresh variable v, with the
  definition (c -> v = x) and (not c -> v = y).
Each fresh variable is determined by its definition (for d, when b != 0), so the rewritten
formula is equivalent to the original if, wherever a / b occurs, its value matters only when
b != 0. This holds for the divisions of contract code, which the encoding guards with
def^i: ite(b != 0, ..a / b.., old). A division written in a property may be unguarded (the
type checker only warns): then the check is out of the fragment (`NotApplicable`), since d
would take any value when b = 0, and a proof of the rewritten formula would not be one of the
original. Formulas with integers, addresses or methods that are not constants are out of the
fragment too (nlqsat is a procedure for real arithmetic). A field of enumerated type of an
input record (e.g. the oracle of the lending contracts, an address) is fixed to each of its
constants in turn, one query per case (`SplitQuery`, at most MAX_CASES): the field ranges over
exactly these constants, so the formula is valid iff every case is (2026-10-25: the free-state
checks of Liquidation_attack on lending-real were all outside the fragment because of the
oracle; split, each case is decided in under 0.1 s)."""

from __future__ import annotations

import itertools
import os
import tempfile
import time
from dataclasses import dataclass, field
from fractions import Fraction
from math import ceil
from typing import Dict, List, Optional, Sequence, Tuple

import z3

from . import kind2
from . import lustre as L

TACTIC = "(then simplify nlqsat)"
MAX_CASES = 64                      # cases of the fields of enumerated type (`SplitQuery`)


class NotApplicable(Exception):
    """The formula is outside the fragment of this module (the reason is the message)."""


class _EnumField(NotApplicable):
    """A free variable of enumerated type: `prepare` may split the check on it."""


@dataclass
class Answer:
    status: str                 # 'valid', 'invalid' (the negation has a model), 'unknown'
    # 'invalid': the model, the values of the free constants of the formula that are rational
    values: Dict[str, object] = field(default_factory=dict)
    # those that are not (algebraic numbers, which no literal of the encoding expresses)
    missing: List[str] = field(default_factory=list)
    note: str = ""              # why unknown


@dataclass
class Declarations:
    """The types and functions of a Lustre program that a check may use."""
    structs: Dict[str, List[Tuple[str, str]]]
    enums: Dict[str, List[str]]
    functions: Dict[str, L.Function]

    @staticmethod
    def of(program: L.Program) -> "Declarations":
        return Declarations(
            {d.name: list(d.fields) for d in program.decls if isinstance(d, L.StructType)},
            {d.name: list(d.constants) for d in program.decls if isinstance(d, L.EnumType)},
            {d.name: d for d in program.decls if isinstance(d, L.Function) and not d.node})


# ------------------------------------------------------------------ translation

@dataclass
class _Sym:
    """A record input (e.g. the free state s): its fields are made on demand."""
    path: str
    type: str


class _Env:
    """Values of the variables, and the translations made with them (by node identity: the
    terms of the encoding share subterms, and their hash traverses the whole tree)."""

    def __init__(self, values: dict):
        self.values = values
        self.memo: Dict[int, object] = {}


class _Translator:
    def __init__(self, decls: Declarations, fixed: Optional[Dict[str, str]] = None):
        self.decls = decls
        self.free: Dict[str, z3.ExprRef] = {}       # free constants by name: paths and inputs
        self.fresh = itertools.count()
        self.fixed = fixed or {}                    # fields of enumerated type: their constant

    def constant(self, name: str, typ: str):
        if typ in self.decls.structs:
            return _Sym(name, typ)
        if name in self.fixed:
            return self.fixed[name]
        if name not in self.free:
            self.free[name] = _scalar(name, typ, self.decls)
        return self.free[name]

    def field(self, r, f: str):
        if isinstance(r, dict):
            return r[f]
        if isinstance(r, _Sym):
            typ = dict(self.decls.structs[r.type])[f]
            return self.constant(f"{r.path}.{f}", typ)
        raise NotApplicable(f"projection .{f} of a non-record")

    def fields(self, r) -> List[str]:
        return list(r) if isinstance(r, dict) else [n for n, _ in self.decls.structs[r.type]]

    def eq(self, a, b) -> z3.BoolRef:
        if isinstance(a, (dict, _Sym)) or isinstance(b, (dict, _Sym)):
            return z3.And([self.eq(self.field(a, f), self.field(b, f)) for f in self.fields(a)])
        if isinstance(a, str) or isinstance(b, str):
            if isinstance(a, str) and isinstance(b, str):
                return z3.BoolVal(a == b)
            raise NotApplicable("a comparison of an enumerated value that is not a constant")
        return a == b

    def ite(self, c, a, b):
        if z3.is_true(c):
            return a
        if z3.is_false(c):
            return b
        if isinstance(a, (dict, _Sym)) or isinstance(b, (dict, _Sym)):
            return {f: self.ite(c, self.field(a, f), self.field(b, f)) for f in self.fields(a)}
        if isinstance(a, str) or isinstance(b, str):
            if a == b:
                return a
            raise NotApplicable("an enumerated value that is not a constant")
        return z3.If(c, a, b)

    def run(self, e: L.LExpr, env: _Env):
        key = id(e)
        if key not in env.memo:
            env.memo[key] = self._run(e, env)
        return env.memo[key]

    def _run(self, e: L.LExpr, env: _Env):
        r = lambda x: self.run(x, env)
        if isinstance(e, L.Var):
            if e.name in env.values:
                return env.values[e.name]
            if e.name.startswith(("A_", "P_")):
                return e.name                       # an enum constant
            raise NotApplicable(f"free variable {e.name}")
        if isinstance(e, L.Bool):
            return z3.BoolVal(e.value)
        if isinstance(e, L.Int):
            return z3.IntVal(e.value)
        if isinstance(e, L.Real):
            v = Fraction(e.value)
            return z3.RealVal(f"{v.numerator}/{v.denominator}")
        if isinstance(e, L.Op):
            return self.op(e.op, [r(a) for a in e.args])
        if isinstance(e, L.Ite):
            return self.ite(r(e.cond), r(e.then), r(e.orelse))
        if isinstance(e, L.Proj):
            return self.field(r(e.record), e.field)
        if isinstance(e, L.Record):
            return {n: r(v) for n, v in e.fields}
        if isinstance(e, L.Call):
            args = [r(a) for a in e.args]
            if e.fn == "real":
                return z3.ToReal(args[0])
            f = self.decls.functions.get(e.fn)
            if f is None:
                raise NotApplicable(f"call to an unknown function {e.fn}")
            local = _Env({n: a for (n, _), a in zip(f.inputs, args)})
            for n, body in f.equations:
                local.values[n] = self.run(body, local)
            return local.values[f.outputs[0][0]]
        if isinstance(e, L.Quant):
            bound = {n: _scalar(f"{n}__{next(self.fresh)}", t, self.decls) for n, t in e.vars}
            body = self.run(e.body, _Env({**env.values, **bound}))
            q = z3.ForAll if e.kind == "forall" else z3.Exists
            return q(list(bound.values()), body)
        raise NotApplicable(f"{type(e).__name__} in a check on free values")

    def op(self, o: str, args: list):
        if len(args) == 1:
            return z3.Not(args[0]) if o == "not" else -args[0]
        a, b = args
        if o == "=":
            return self.eq(a, b)
        if o == "<>":
            return z3.Not(self.eq(a, b))
        if isinstance(a, (str, dict, _Sym)) or isinstance(b, (str, dict, _Sym)):
            raise NotApplicable(f"operator {o} on a record or an enumerated value")
        if o == "and":
            return z3.And(a, b)
        if o == "or":
            return z3.Or(a, b)
        if o == "=>":
            return z3.Implies(a, b)
        if o in ("div", "/"):                   # SMT-LIB div on ints, / on reals
            return a / b
        if o == "mod":
            return a % b
        return {"<": lambda: a < b, "<=": lambda: a <= b, ">": lambda: a > b,
                ">=": lambda: a >= b, "+": lambda: a + b, "-": lambda: a - b,
                "*": lambda: a * b}[o]()


def _scalar(name: str, typ: str, decls: Declarations) -> z3.ExprRef:
    if typ == "real":
        return z3.Real(name)
    if typ == "int":
        return z3.Int(name)
    if typ == "bool":
        return z3.Bool(name)
    if typ in decls.enums:
        raise _EnumField(f"a variable of type {typ} ({name})")
    raise NotApplicable(f"a variable of type {typ} ({name})")


# ------------------------------------------------------------------ guards and rewriting

def _nonzero(c: z3.ExprRef) -> List[z3.ExprRef]:
    """Terms that are nonzero whenever the formula c holds (syntactically: its conjuncts
    b != 0, b > 0, b < 0, not b <= 0, not b >= 0, with 0 on either side)."""
    if z3.is_and(c):
        return [t for x in c.children() for t in _nonzero(x)]
    negated = z3.is_not(c)
    x = c.arg(0) if negated else c
    if not (z3.is_eq(x) or z3.is_le(x) or z3.is_ge(x) or z3.is_lt(x) or z3.is_gt(x)):
        return []
    lhs, rhs = x.arg(0), x.arg(1)
    zero_r, zero_l = _is_zero(rhs), _is_zero(lhs)
    if not (zero_r or zero_l):
        return []
    t = lhs if zero_r else rhs
    if negated and (z3.is_eq(x) or z3.is_le(x) or z3.is_ge(x)):
        return [t]
    if not negated and (z3.is_lt(x) or z3.is_gt(x)):
        return [t]
    return []


def _zero(c: z3.ExprRef) -> List[z3.ExprRef]:
    """Terms that are zero whenever c holds (c is b = 0 or 0 = b)."""
    if z3.is_eq(c):
        if _is_zero(c.arg(1)):
            return [c.arg(0)]
        if _is_zero(c.arg(0)):
            return [c.arg(1)]
    return []


def _is_zero(t: z3.ExprRef) -> bool:
    if z3.is_rational_value(t):
        return t.as_fraction() == 0
    return z3.is_int_value(t) and t.as_long() == 0


def _is_numeral(t: z3.ExprRef) -> bool:
    return z3.is_rational_value(t) or z3.is_int_value(t)


def check_guards(f: z3.ExprRef) -> None:
    """NotApplicable unless every division a / b of f by a non-constant b is guarded: on the
    path from the top of f to it there is a context that makes its value irrelevant when
    b = 0 — the condition of an implication, another conjunct of a conjunction, the negation
    of another disjunct, or the condition of an if-then-else (for the branch taken) — that
    implies b != 0 (`_nonzero`). If b = 0, such a context does not depend on a / b."""
    seen = set()
    fresh = itertools.count()

    def visit(e: z3.ExprRef, guards: Tuple[z3.ExprRef, ...]):
        key = (e.get_id(), tuple(g.get_id() for g in guards))
        if key in seen:
            return
        seen.add(key)
        if z3.is_quantifier(e):
            # the body with its bound variables as fresh constants: in e.body() they are de
            # Bruijn indices, and a guard on an outer variable would match a divisor that is
            # an inner one with the same index
            xs = [z3.Const(f"{e.var_name(i)}__g{next(fresh)}", e.var_sort(i))
                  for i in range(e.num_vars())]
            visit(z3.substitute_vars(e.body(), *reversed(xs)), guards)
            return
        if not z3.is_app(e):
            return
        kids = e.children()
        if z3.is_implies(e):
            visit(kids[0], guards)
            visit(kids[1], guards + tuple(_nonzero(kids[0])))
            return
        if z3.is_and(e) or z3.is_or(e):
            for i, k in enumerate(kids):
                others = [x for j, x in enumerate(kids) if j != i]
                extra = ([t for x in others for t in _nonzero(x)] if z3.is_and(e)
                         else [t for x in others for t in _zero(x)])
                visit(k, guards + tuple(extra))
            return
        if z3.is_app_of(e, z3.Z3_OP_ITE):
            c, x, y = kids
            visit(c, guards)
            visit(x, guards + tuple(_nonzero(c)))
            visit(y, guards + tuple(_zero(c)))
            return
        if (z3.is_div(e) or z3.is_idiv(e) or z3.is_mod(e)) \
                and (_is_zero(kids[1]) or not _is_numeral(kids[1])) \
                and not any(kids[1].eq(g) for g in guards):
            raise NotApplicable(f"unguarded division by {kids[1]}")
        for k in kids:
            visit(k, guards)

    visit(f, ())


def _arith_ite(e: z3.ExprRef) -> bool:
    return z3.is_app_of(e, z3.Z3_OP_ITE) and not z3.is_bool(e)


def _division(e: z3.ExprRef) -> bool:
    return z3.is_div(e) and not _is_numeral(e.arg(1))


class _Rewriter:
    """The rewriting of the module docstring: divisions and if-then-else terms of number type
    become variables with their definitions, bound at the innermost quantifier around them."""

    def __init__(self):
        self.fresh = itertools.count()

    def formula(self, f: z3.ExprRef) -> Tuple[z3.ExprRef, List[z3.ExprRef], List[z3.ExprRef]]:
        """f rewritten outside its quantifiers (each quantifier rewritten inside), with the
        new free constants and their definitions."""
        body = self._quantifiers(f)
        return self._name_terms(body)

    def _quantifiers(self, e: z3.ExprRef) -> z3.ExprRef:
        memo: Dict[int, z3.ExprRef] = {}

        def visit(x: z3.ExprRef) -> z3.ExprRef:
            if x.get_id() in memo:
                return memo[x.get_id()]
            if z3.is_quantifier(x):
                out = self._quantifier(x)
            elif z3.is_app(x) and x.num_args() > 0:
                kids = [visit(k) for k in x.children()]
                out = x.decl()(*kids) if any(not a.eq(b) for a, b in zip(kids, x.children())) \
                    else x
            else:
                out = x
            memo[x.get_id()] = out
            return out

        return visit(e)

    def _quantifier(self, q: z3.QuantifierRef) -> z3.ExprRef:
        xs = [z3.Const(f"{q.var_name(i)}__b{next(self.fresh)}", q.var_sort(i))
              for i in range(q.num_vars())]
        body = z3.substitute_vars(q.body(), *reversed(xs))
        body, new, defs = self._name_terms(self._quantifiers(body))
        if q.is_exists():
            return z3.Exists(xs + new, z3.And(defs + [body]) if defs else body)
        return z3.ForAll(xs + new, z3.Implies(z3.And(defs), body) if defs else body)

    def _name_terms(self, body: z3.ExprRef):
        """The divisions and if-then-else terms of body outside its quantifiers (already
        rewritten), replaced by fresh constants, innermost first (one pass, bottom-up; equal
        terms share their constant); returns (body, the constants, their definitions)."""
        new: List[z3.ExprRef] = []
        defs: List[z3.ExprRef] = []
        memo: Dict[int, z3.ExprRef] = {}

        def visit(x: z3.ExprRef) -> z3.ExprRef:
            if x.get_id() in memo:
                return memo[x.get_id()]
            out = x
            if z3.is_app(x) and x.num_args() > 0:
                kids = [visit(k) for k in x.children()]
                if any(not a.eq(b) for a, b in zip(kids, x.children())):
                    out = x.decl()(*kids)
                if _division(out) or _arith_ite(out):
                    v = z3.Const(f"_v{next(self.fresh)}", out.sort())
                    if _division(out):
                        a, b = out.arg(0), out.arg(1)
                        defs.append(z3.Implies(z3.Not(b == 0), b * v == a))
                    else:
                        c, p, q = out.children()
                        defs.append(z3.And(z3.Implies(c, v == p), z3.Implies(z3.Not(c), v == q)))
                    new.append(v)
                    out = v
            memo[x.get_id()] = out
            return out

        return visit(body), new, defs


def check_fragment(f: z3.ExprRef) -> None:
    """NotApplicable unless f is in pure real arithmetic for nlqsat: Booleans, reals, no
    division by a non-constant, no if-then-else of number type, no other function."""
    seen = set()
    allowed = {z3.Z3_OP_TRUE, z3.Z3_OP_FALSE, z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_NOT,
               z3.Z3_OP_IMPLIES, z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT, z3.Z3_OP_IFF,
               z3.Z3_OP_XOR, z3.Z3_OP_ITE, z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT,
               z3.Z3_OP_GT, z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_MUL, z3.Z3_OP_UMINUS,
               z3.Z3_OP_DIV, z3.Z3_OP_ANUM, z3.Z3_OP_UNINTERPRETED, z3.Z3_OP_POWER}

    def visit(e: z3.ExprRef):
        if e.get_id() in seen:
            return
        seen.add(e.get_id())
        if z3.is_quantifier(e):
            for i in range(e.num_vars()):
                if e.var_sort(i) not in (z3.BoolSort(), z3.RealSort()):
                    raise NotApplicable(f"a quantifier over {e.var_sort(i)}")
            visit(e.body())
            return
        if z3.is_var(e):
            return
        s = e.sort()
        if not (z3.is_bool(e) or s == z3.RealSort()):
            raise NotApplicable(f"a term of sort {s}")
        k = e.decl().kind()
        if k not in allowed or (k == z3.Z3_OP_UNINTERPRETED and e.num_args() > 0) \
                or _arith_ite(e) or _division(e):
            raise NotApplicable(f"the term {str(e)[:80]}")
        for c in e.children():
            visit(c)

    visit(f)


# ------------------------------------------------------------------ queries

class Query:
    """The check that a formula is valid (it holds for all values of its free constants),
    prepared for z3."""

    def __init__(self, formula: z3.BoolRef, free: Dict[str, z3.ExprRef]):
        self.free = free
        rw = _Rewriter()
        negation, new, defs = rw.formula(z3.Not(formula))
        self.assertion = z3.simplify(z3.And(defs + [negation]))
        check_fragment(self.assertion)
        self.trivial = z3.is_false(self.assertion)

    def asked(self) -> List[str]:
        """The free constants whose values a model gives: those left in the assertion (the
        others are not declared, and do not matter)."""
        occurring = _constants(self.assertion)
        return sorted(n for n in self.free if n in occurring)

    def smtlib(self) -> str:
        s = z3.Solver()
        s.add(self.assertion)
        names = " ".join(_quote(n) for n in self.asked())
        return ("(set-option :produce-models true)\n" + s.sexpr()
                + f"(check-sat-using {TACTIC})\n"
                + (f"(get-value ({names}))\n" if names else "")
                + "(get-info :reason-unknown)\n")

    def run(self, timeout: float) -> Answer:
        """z3 on the negation, at most `timeout` seconds: unsat, the formula is valid; sat,
        a model of the negation (the values of the free constants, rational ones only)."""
        if self.trivial:
            return Answer("valid")
        with tempfile.TemporaryDirectory(prefix="kindhml_") as tmp:
            path = os.path.join(tmp, "query.smt2")
            with open(path, "w") as f:
                f.write(self.smtlib())
            secs = max(1, ceil(timeout))
            raw, err, killed, oom = kind2.run_command([kind2.find_z3(), f"-T:{secs}", path],
                                                      secs + 5)
        lines = [x for x in raw.splitlines() if x.strip()]
        first = lines[0].strip() if lines else ""
        if first == "unsat":
            return Answer("valid")
        if first == "sat":
            values = parse_values(raw[raw.index("sat") + 3:])
            return Answer("invalid", values, [n for n in self.asked() if n not in values])
        note = "timeout" if killed or first == "timeout" else (
            "memory limit" if oom else _reason(raw) or first or err.strip()[-200:])
        return Answer("unknown", note=note)


class SplitQuery:
    """The cases of a check, one per assignment of constants to the fields of enumerated type
    of its input records (module docstring): valid when every case is valid, invalid when one
    is refuted (its model completed with the constants of the case). The cases proved are
    kept from one call to the next."""

    def __init__(self, cases: List[Tuple[Dict[str, str], Query]]):
        self.cases = cases
        self.proved: set = set()
        self.trivial = all(q.trivial for _, q in cases)

    def run(self, timeout: float) -> Answer:
        deadline = time.time() + timeout
        todo = [k for k in range(len(self.cases)) if k not in self.proved]
        for j, k in enumerate(todo):
            left = deadline - time.time()
            if left <= 0.2:
                return Answer("unknown", note="timeout")
            fixed, query = self.cases[k]
            answer = query.run(left / (len(todo) - j))
            if answer.status == "valid":
                self.proved.add(k)
            elif answer.status == "invalid":
                return Answer("invalid", {**answer.values, **fixed}, answer.missing)
            else:
                return answer
        return Answer("valid")


def prepare(formula: L.LExpr, inputs: Sequence[Tuple[str, str]],
            decls: Declarations) -> "Query | SplitQuery":
    """The check that the Lustre formula `formula`, over the inputs (name, type; records by
    the names of `decls.structs`), holds for all their values; split into cases on the fields
    of enumerated type of the input records if needed (`SplitQuery`). NotApplicable if the
    formula is outside the fragment of the module docstring."""
    try:
        return _prepare(formula, inputs, decls, {})
    except _EnumField:
        fields = [(f"{n}.{f}", t) for n, rt in inputs if rt in decls.structs
                  for f, t in decls.structs[rt] if t in decls.enums]
        size = 1
        for _, t in fields:
            size *= len(decls.enums[t])
        if not fields or size > MAX_CASES:
            raise
        choices = [[(path, c) for c in decls.enums[t]] for path, t in fields]
        return SplitQuery([(dict(case), _prepare(formula, inputs, decls, dict(case)))
                           for case in itertools.product(*choices)])


def _prepare(formula: L.LExpr, inputs: Sequence[Tuple[str, str]], decls: Declarations,
             fixed: Dict[str, str]) -> Query:
    tr = _Translator(decls, fixed)
    env = _Env({n: tr.constant(n, t) for n, t in inputs})
    f = tr.run(formula, env)
    if not isinstance(f, z3.BoolRef):
        raise NotApplicable("not a formula")
    check_guards(f)
    return Query(f, dict(tr.free))


def _constants(f: z3.ExprRef) -> set:
    """The names of the free constants of f."""
    seen, out = set(), set()

    def visit(e: z3.ExprRef):
        if e.get_id() in seen:
            return
        seen.add(e.get_id())
        if z3.is_quantifier(e):
            visit(e.body())
        elif z3.is_app(e):
            if e.num_args() == 0 and e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                out.add(e.decl().name())
            for c in e.children():
                visit(c)

    visit(f)
    return out


def _quote(name: str) -> str:
    return name if name.replace("_", "a").isalnum() else f"|{name}|"


def _reason(raw: str) -> str:
    i = raw.find(":reason-unknown")
    if i < 0:
        return ""
    rest = raw[i + len(":reason-unknown"):].strip()
    return rest.split(")")[0].strip().strip('"')


# ------------------------------------------------------------------ values of a model

def _tokens(text: str) -> List[str]:
    out, i = [], 0
    while i < len(text):
        ch = text[i]
        if ch.isspace():
            i += 1
        elif ch in "()":
            out.append(ch)
            i += 1
        elif ch == "|":
            j = text.index("|", i + 1)
            out.append(text[i + 1:j])
            i = j + 1
        elif ch == '"':
            j = text.index('"', i + 1)
            out.append(text[i:j + 1])
            i = j + 1
        else:
            j = i
            while j < len(text) and not text[j].isspace() and text[j] not in "()":
                j += 1
            out.append(text[i:j])
            i = j
    return out


def _sexp(tokens: List[str], i: int):
    if tokens[i] == "(":
        out, i = [], i + 1
        while tokens[i] != ")":
            x, i = _sexp(tokens, i)
            out.append(x)
        return out, i + 1
    return tokens[i], i + 1


def _value(v):
    """A value of z3's get-value: a bool, a rational (Fraction), or None (e.g. an algebraic
    number, which no literal of the encoding can express)."""
    if v == "true":
        return True
    if v == "false":
        return False
    if isinstance(v, str):
        try:
            return Fraction(v)
        except ValueError:
            return None
    if len(v) == 2 and v[0] == "-":
        x = _value(v[1])
        return -x if isinstance(x, Fraction) else None
    if len(v) == 3 and v[0] == "/":
        a, b = _value(v[1]), _value(v[2])
        return a / b if isinstance(a, Fraction) and isinstance(b, Fraction) and b else None
    return None


def parse_values(text: str) -> Dict[str, object]:
    """The values of the answer to (get-value (...)) in `text`, by name; values that are not
    rational are left out."""
    tokens = _tokens(text)
    try:
        start = tokens.index("(")
        pairs, _ = _sexp(tokens, start)
    except (ValueError, IndexError):
        return {}
    out: Dict[str, object] = {}
    for p in pairs if isinstance(pairs, list) else []:
        if isinstance(p, list) and len(p) == 2 and isinstance(p[0], str):
            v = _value(p[1])
            if v is not None:
                out[p[0]] = v
    return out


def literal(v) -> L.LExpr:
    """A value of `parse_values`, or a constant of a `SplitQuery` case, as a Lustre literal
    (the format of `invariants.state_values`)."""
    if isinstance(v, str):
        return L.Var(v)                 # an enum constant (A_u1, ...)
    if isinstance(v, bool):
        return L.Bool(v)
    return L.Real(Fraction(v))
