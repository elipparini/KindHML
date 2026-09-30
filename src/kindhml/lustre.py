"""A small Lustre AST (the fragment accepted by Kind 2 that we need) and its printer.

Expressions are printed fully parenthesised, so no precedence reasoning is needed.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Sequence, Tuple


class LExpr:
    def __str__(self) -> str:
        return render(self)


@dataclass(frozen=True)
class Var(LExpr):
    """Variable or enum constant."""
    name: str


@dataclass(frozen=True)
class Int(LExpr):
    value: int


@dataclass(frozen=True)
class Bool(LExpr):
    value: bool


@dataclass(frozen=True)
class Op(LExpr):
    """Unary (one argument) or binary operator: not - and or => = <> < <= > >= + * div mod."""
    op: str
    args: Tuple[LExpr, ...]


@dataclass(frozen=True)
class Ite(LExpr):
    cond: LExpr
    then: LExpr
    orelse: LExpr


@dataclass(frozen=True)
class Call(LExpr):
    fn: str
    args: Tuple[LExpr, ...]


@dataclass(frozen=True)
class Proj(LExpr):
    record: LExpr
    field: str


@dataclass(frozen=True)
class Record(LExpr):
    type: str
    fields: Tuple[Tuple[str, LExpr], ...]


@dataclass(frozen=True)
class Quant(LExpr):
    kind: str                                   # 'forall' or 'exists'
    vars: Tuple[Tuple[str, str], ...]           # (name, type)
    body: LExpr


@dataclass(frozen=True)
class Arrow(LExpr):
    init: LExpr
    then: LExpr


@dataclass(frozen=True)
class Pre(LExpr):
    arg: LExpr


TRUE, FALSE = Bool(True), Bool(False)


# ------------------------------------------------------------------ smart constructors

def op(o: str, *args: LExpr) -> LExpr:
    return Op(o, tuple(args))


def conj(args: Sequence[LExpr]) -> LExpr:
    args = [a for a in args if a != TRUE]
    if not args:
        return TRUE
    if FALSE in args:
        return FALSE
    out = args[0]
    for a in args[1:]:
        out = Op("and", (out, a))
    return out


def disj(args: Sequence[LExpr]) -> LExpr:
    args = [a for a in args if a != FALSE]
    if not args:
        return FALSE
    if TRUE in args:
        return TRUE
    out = args[0]
    for a in args[1:]:
        out = Op("or", (out, a))
    return out


def neg(a: LExpr) -> LExpr:
    if isinstance(a, Bool):
        return Bool(not a.value)
    return Op("not", (a,))


def ite(c: LExpr, t: LExpr, e: LExpr) -> LExpr:
    if c == TRUE or t == e:
        return t
    if c == FALSE:
        return e
    return Ite(c, t, e)


def call(fn: str, *args: LExpr) -> LExpr:
    return Call(fn, tuple(args))


def record(type_: str, fields: Sequence[Tuple[str, LExpr]]) -> LExpr:
    return Record(type_, tuple(fields))


def render(e: LExpr) -> str:
    if isinstance(e, Var):
        return e.name
    if isinstance(e, Int):
        return str(e.value) if e.value >= 0 else f"(- {-e.value})"
    if isinstance(e, Bool):
        return "true" if e.value else "false"
    if isinstance(e, Op):
        if len(e.args) == 1:
            return f"({e.op} {render(e.args[0])})"
        return f"({render(e.args[0])} {e.op} {render(e.args[1])})"
    if isinstance(e, Ite):
        return f"(if {render(e.cond)} then {render(e.then)} else {render(e.orelse)})"
    if isinstance(e, Call):
        return f"{e.fn}({', '.join(render(a) for a in e.args)})"
    if isinstance(e, Proj):
        return f"{render(e.record)}.{e.field}"
    if isinstance(e, Record):
        inner = "; ".join(f"{n} = {render(v)}" for n, v in e.fields)
        return f"{e.type} {{ {inner} }}"
    if isinstance(e, Quant):
        decls = "; ".join(f"{n}: {t}" for n, t in e.vars)
        return f"({e.kind} ({decls}) {render(e.body)})"
    if isinstance(e, Arrow):
        return f"({render(e.init)} -> {render(e.then)})"
    if isinstance(e, Pre):
        return f"(pre {render(e.arg)})"
    raise TypeError(f"unknown Lustre expression {e!r}")


# ------------------------------------------------------------------ declarations

@dataclass
class EnumType:
    name: str
    constants: List[str]

    def render(self) -> str:
        return f"type {self.name} = enum {{ {', '.join(self.constants)} }};"


@dataclass
class StructType:
    name: str
    fields: List[Tuple[str, str]]

    def render(self) -> str:
        inner = "".join(f"\n  {n}: {t};" for n, t in self.fields)
        return f"type {self.name} = struct {{{inner}\n}};"


@dataclass
class Function:
    """A Lustre function (or node, if `node` is set)."""
    name: str
    inputs: List[Tuple[str, str]]
    outputs: List[Tuple[str, str]]
    locals: List[Tuple[str, str]] = field(default_factory=list)
    equations: List[Tuple[str, LExpr]] = field(default_factory=list)
    asserts: List[LExpr] = field(default_factory=list)
    properties: List[Tuple[str, LExpr]] = field(default_factory=list)
    node: bool = False
    comment: str = ""

    def render(self) -> str:
        decl = lambda vs: "; ".join(f"{n}: {t}" for n, t in vs)
        kind = "node" if self.node else "function"
        out = []
        if self.comment:
            out += [f"-- {line}" for line in self.comment.splitlines()]
        out.append(f"{kind} {self.name}({decl(self.inputs)}) returns ({decl(self.outputs)});")
        if self.locals:
            out.append("var")
            out += [f"  {n}: {t};" for n, t in self.locals]
        out.append("let")
        out += [f"  assert {render(a)};" for a in self.asserts]
        out += [f"  {n} = {render(e)};" for n, e in self.equations]
        out += [f"  --%PROPERTY \"{n}\" {render(e)};" for n, e in self.properties]
        out.append("tel")
        return "\n".join(out)


@dataclass
class Program:
    decls: list = field(default_factory=list)

    def render(self) -> str:
        return "\n\n".join(d.render() for d in self.decls) + "\n"
