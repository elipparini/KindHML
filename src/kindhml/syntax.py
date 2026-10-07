"""Abstract syntax of contracts and rules.

The builder produces a *raw* AST in which names are unresolved (`Name`,
`Member`). The type checker produces a *resolved* AST in which every name is
replaced by a node saying what it denotes (`Field`, `Param`, `QVar`, ...).
Both use the classes below; `Name` and `Member` never occur in a resolved AST.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
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
    """Base types: int, uint, real, bool, address, method, args."""
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
REAL = Type("real")
BOOL = Type("bool")
ADDRESS = Type("address")
METHOD = Type("method")
ARGS = Type("calldataargs")

AnyType = Union[Type, MapType]


def is_int(t: AnyType) -> bool:
    """`uint` is a subtype of `int` for arithmetic and comparisons."""
    return t in (INT, UINT)


def is_num(t: AnyType) -> bool:
    """Numbers: int, uint, real. An int can be used where a real is expected."""
    return t in (INT, UINT, REAL)


def zero(t: Type) -> "Expr":
    """The literal 0 of the number type t."""
    return RealLit(Fraction(0)) if t == REAL else IntLit(0)


# ------------------------------------------------------------------ expressions

class Expr:
    pos: Pos


@dataclass(frozen=True)
class IntLit(Expr):
    value: int
    pos: Pos = _pos()


@dataclass(frozen=True)
class RealLit(Expr):
    value: Fraction
    pos: Pos = _pos()


@dataclass(frozen=True)
class ToReal(Expr):
    """The conversion of an integer to a real (resolved AST only; inserted by the type
    checker where an int is used as a real)."""
    arg: Expr
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
    """In a resolved AST, `real` is set iff the operands are numbers and at least one of them
    is real; then both are real (the type checker inserts `ToReal`), and `/` is the division
    of reals (otherwise Euclidean)."""
    op: str            # * / % + - < <= > >= == != && || ->
    left: Expr
    right: Expr
    pos: Pos = _pos()
    real: bool = False


@dataclass(frozen=True)
class Quant(Expr):
    kind: str          # 'forall' or 'exists'
    var: str
    type: Type
    body: Expr
    pos: Pos = _pos()


@dataclass(frozen=True)
class Modal(Expr):
    """`<< sender : contract . proc(args) $ value @ blocks >> body`.

    `proc` is a `Name` in the raw AST, and a `ProcConst` or `QVar` of type
    method in the resolved AST. `blocks` is the increase of the block number made by the
    transaction (0 when omitted).
    """
    sender: Expr
    contract: str
    proc: Expr
    args: Tuple[Expr, ...]
    value: Expr
    blocks: Expr
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


@dataclass(frozen=True)
class SumMap(Expr):
    """`sum(m)`: the sum of m[a] over all addresses a (they are finite, A1). In a resolved
    AST, `map` is a `Field` (a mapping to numbers) or `Balance`."""
    map: Expr
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
class TxBlocks(Expr):
    """The increase of the block number carried by the transaction (see DESIGN.md)."""
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
    """block_num := block_num + Tx.blocks."""
    pos: Pos = _pos()


@dataclass(frozen=True)
class Unfold(Stmt):
    """The contract call `callee.proc(args) $ value` made by `caller`, with the core body of
    the callee (initPay, constructed guard, uint guards, body). In `body`, `Sender`, `Value`
    and `Param(callee, proc, x)` denote the caller, the value, and the actual parameters,
    evaluated at the call point (Sect. `sec:encoding:contract`)."""
    caller: str
    callee: str
    proc: str
    args: Tuple[Expr, ...]
    value: Expr
    body: Stmt
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
    """A rule, or an invariant: a rule without modalities, which the tool proves inductive
    and then assumes when checking other rules. Both are required in the reachable states
    where all contracts are constructed."""
    name: str
    formula: Expr
    groundtruth: Optional[bool] = None
    pos: Pos = _pos()
    invariant: bool = False


@dataclass(frozen=True)
class Program:
    contracts: Tuple[Contract, ...]
    rules: Tuple[Rule, ...]
    balance_type: Type = INT        # of balances, values and amounts (`pragma balance real`)

    def contract(self, name: str) -> Optional[Contract]:
        return next((c for c in self.contracts if c.name == name), None)

    def rule(self, name: str) -> Optional[Rule]:
        return next((r for r in self.rules if r.name == name), None)
