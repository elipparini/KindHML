"""Abstract syntax of contracts and rules.

The builder produces a *raw* AST in which names are unresolved (`Name`,
`Member`). The type checker produces a *resolved* AST in which every name is
replaced by a node saying what it denotes (`Field`, `Param`, `QVar`, ...).
Both use the classes below; `Name` and `Member` never occur in a resolved AST.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional, Tuple, Union


@dataclass(frozen=True)
class Pos:
    line: int
    col: int

    def __str__(self) -> str:
        return f"line {self.line}, column {self.col}"


NOPOS = Pos(0, 0)


def _pos():
    return field(default=NOPOS, compare=False, repr=False)


# ------------------------------------------------------------------ types

@dataclass(frozen=True)
class Type:
    """Base types: int, uint, bool, address, method, args."""
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class MapType:
    """`mapping(address => value)`. Keys are always addresses (A2)."""
    value: Type

    def __str__(self) -> str:
        return f"mapping(address => {self.value})"


INT = Type("int")
UINT = Type("uint")
BOOL = Type("bool")
ADDRESS = Type("address")
METHOD = Type("method")
ARGS = Type("calldataargs")

AnyType = Union[Type, MapType]


def is_int(t: AnyType) -> bool:
    """`uint` is a subtype of `int` for arithmetic and comparisons."""
    return t in (INT, UINT)


# ------------------------------------------------------------------ expressions

class Expr:
    pos: Pos


@dataclass(frozen=True)
class IntLit(Expr):
    value: int
    pos: Pos = _pos()


@dataclass(frozen=True)
class BoolLit(Expr):
    value: bool
    pos: Pos = _pos()


@dataclass(frozen=True)
class NullLit(Expr):
    pos: Pos = _pos()


@dataclass(frozen=True)
class Name(Expr):
    """Unresolved identifier (raw AST only)."""
    name: str
    pos: Pos = _pos()


@dataclass(frozen=True)
class Member(Expr):
    """Unresolved `e.x` (raw AST only)."""
    obj: Expr
    name: str
    pos: Pos = _pos()


@dataclass(frozen=True)
class FunCall(Expr):
    """Unresolved `f(e1, ..., ek)` (raw AST only): `old`, `is_EOA`."""
    fn: str
    args: Tuple[Expr, ...]
    pos: Pos = _pos()


@dataclass(frozen=True)
class Index(Expr):
    """`m[key]`. In a resolved AST `map` is a `Field` or `Balance`."""
    map: Expr
    key: Expr
    pos: Pos = _pos()


@dataclass(frozen=True)
class UnOp(Expr):
    op: str            # '!' or '-'
    arg: Expr
    pos: Pos = _pos()


@dataclass(frozen=True)
class BinOp(Expr):
    op: str            # * / % + - < <= > >= == != && || ->
    left: Expr
    right: Expr
    pos: Pos = _pos()


@dataclass(frozen=True)
class Quant(Expr):
    kind: str          # 'forall' or 'exists'
    var: str
    type: Type
    body: Expr
    pos: Pos = _pos()


@dataclass(frozen=True)
class Modal(Expr):
    """`<< sender : contract . proc(args) $ value >> body`.

    `proc` is a `Name` in the raw AST, and a `ProcConst` or `QVar` of type
    method in the resolved AST.
    """
    sender: Expr
    contract: str
    proc: Expr
    args: Tuple[Expr, ...]
    value: Expr
    body: Expr
    pos: Pos = _pos()


# Resolved expressions -------------------------------------------------

@dataclass(frozen=True)
class Field(Expr):
    """Field `name` of contract `contract` (a map field if its type is a MapType)."""
    contract: str
    name: str
    pos: Pos = _pos()


@dataclass(frozen=True)
class Param(Expr):
    """Formal parameter `name` of procedure `proc` of `contract`."""
    contract: str
    proc: str
    name: str
    pos: Pos = _pos()


@dataclass(frozen=True)
class QVar(Expr):
    """Variable bound by a quantifier of a rule."""
    name: str
    type: Type
    pos: Pos = _pos()


@dataclass(frozen=True)
class ProcConst(Expr):
    """Procedure constant (type method)."""
    contract: str
    proc: str
    pos: Pos = _pos()


@dataclass(frozen=True)
class ContractAddr(Expr):
    """Address of a contract: `this` or a contract name."""
    contract: str
    pos: Pos = _pos()


@dataclass(frozen=True)
class Balance(Expr):
    """The balance map; only occurs as `Index(Balance(), a)`."""
    pos: Pos = _pos()


@dataclass(frozen=True)
class Sender(Expr):
    pos: Pos = _pos()


@dataclass(frozen=True)
class Value(Expr):
    pos: Pos = _pos()


@dataclass(frozen=True)
class BlockNum(Expr):
    pos: Pos = _pos()


@dataclass(frozen=True)
class Reverted(Expr):
    pos: Pos = _pos()


@dataclass(frozen=True)
class Old(Expr):
    arg: Expr
    pos: Pos = _pos()


@dataclass(frozen=True)
class IsEOA(Expr):
    arg: Expr
    pos: Pos = _pos()


# ------------------------------------------------------------------ statements

class Stmt:
    pos: Pos


@dataclass(frozen=True)
class Skip(Stmt):
    pos: Pos = _pos()


@dataclass(frozen=True)
class Require(Stmt):
    cond: Expr
    pos: Pos = _pos()


@dataclass(frozen=True)
class Assign(Stmt):
    """`x = e` (key is None) or `x[key] = e`. `target` is the field name."""
    target: str
    key: Optional[Expr]
    value: Expr
    pos: Pos = _pos()


@dataclass(frozen=True)
class Transfer(Stmt):
    """`to.transfer(amount)`."""
    to: Expr
    amount: Expr
    pos: Pos = _pos()


@dataclass(frozen=True)
class Call(Stmt):
    """Contract call `callee.proc(args) $ value` (unfolded by the desugaring)."""
    callee: Expr
    proc: str
    args: Tuple[Expr, ...]
    value: Expr
    pos: Pos = _pos()


@dataclass(frozen=True)
class Seq(Stmt):
    stmts: Tuple[Stmt, ...]
    pos: Pos = _pos()


@dataclass(frozen=True)
class If(Stmt):
    cond: Expr
    then: Stmt
    orelse: Stmt
    pos: Pos = _pos()


# Core statements, produced by the desugaring (`desugar.py`) --------------
# Core statements carry the contract they act on explicitly, since after the
# unfolding of contract calls a body mixes statements of several contracts.

@dataclass(frozen=True)
class Constructed(Expr):
    """The state variable constructed_C."""
    contract: str
    pos: Pos = _pos()


@dataclass(frozen=True)
class TxBlockNum(Expr):
    """The block number carried by the transaction (extension, see DESIGN.md)."""
    pos: Pos = _pos()


@dataclass(frozen=True)
class SetField(Stmt):
    """`C.x = value` (key is None) or `C.x[key] = value`."""
    contract: str
    name: str
    key: Optional[Expr]
    value: Expr
    pos: Pos = _pos()


@dataclass(frozen=True)
class Send(Stmt):
    """Transfer of `amount` tokens from `src` to `dst`: the statement `initPay` (src = sender)
    and `dst.transfer(amount)` (src = this) of Table `tab:statement-to-fol`."""
    src: Expr
    dst: Expr
    amount: Expr
    pos: Pos = _pos()


@dataclass(frozen=True)
class SetConstructed(Stmt):
    """constructed_C := true."""
    contract: str
    pos: Pos = _pos()


@dataclass(frozen=True)
class SetBlockNum(Stmt):
    """block_num := Tx.block_num."""
    pos: Pos = _pos()


# ------------------------------------------------------------------ declarations

CONSTRUCTOR = "constructor"


@dataclass(frozen=True)
class VarDecl:
    type: AnyType
    name: str
    pos: Pos = _pos()


@dataclass(frozen=True)
class Procedure:
    name: str                       # CONSTRUCTOR for the constructor
    params: Tuple[VarDecl, ...]
    payable: bool
    body: Stmt
    pos: Pos = _pos()


@dataclass(frozen=True)
class Contract:
    name: str
    fields: Tuple[VarDecl, ...]
    procs: Tuple[Procedure, ...]    # the constructor is always procs[0]
    pos: Pos = _pos()

    def field_decl(self, name: str) -> Optional[VarDecl]:
        return next((f for f in self.fields if f.name == name), None)

    def proc(self, name: str) -> Optional[Procedure]:
        return next((p for p in self.procs if p.name == name), None)


@dataclass(frozen=True)
class Rule:
    name: str
    formula: Expr
    groundtruth: Optional[bool] = None
    pos: Pos = _pos()


@dataclass(frozen=True)
class Program:
    contracts: Tuple[Contract, ...]
    rules: Tuple[Rule, ...]

    def contract(self, name: str) -> Optional[Contract]:
        return next((c for c in self.contracts if c.name == name), None)

    def rule(self, name: str) -> Optional[Rule]:
        return next((r for r in self.rules if r.name == name), None)
