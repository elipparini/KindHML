"""Desugaring of procedures into core statements.

A procedure f of contract C with body s becomes, for a transaction,

    [block_num := Tx.block_num;]            -- only if block.number is used (extension)
    require(sender != null && sender != C);  -- A5(iv) and the null-sender extension
    callee(C, f)

where callee(C, f), also used for the contract calls of C.f, is

    initPay;                                  -- Sect. `sec:encoding:contract`
    require(!constructed_C); constructed_C := true    (constructor)
  | require(constructed_C)                           (other procedures)
    [require(x >= 0) for each uint parameter x;]     -- uint extension
    s'

`initPay` is `Send(sender, C, value)` for a payable procedure and `require(value == 0)`
otherwise; s' is s with `x = e` on a uint field preceded by `require(e >= 0)`,
`to.transfer(n)` replaced by `Send(C, to, n)`, and each contract call `D.g(ē) $ e` replaced by
`Unfold(C, D, g, ē, e, callee(D, g))` (unfolding, A4: the call graph must be acyclic).

The division guards def^i(s) are not added here: they are part of the encoding of each
statement (`encode_trans.py`), as in Appendix `app:correctness:transition`.
"""

from __future__ import annotations

from typing import List, Tuple

from . import syntax as S
from .errors import KindHMLError
from .model import System


def _and(a: S.Expr, b: S.Expr) -> S.Expr:
    return S.BinOp("&&", a, b)


def _seq(stmts: List[S.Stmt]) -> S.Stmt:
    flat: List[S.Stmt] = []
    for s in stmts:
        flat.extend(s.stmts if isinstance(s, S.Seq) else [s])
    return flat[0] if len(flat) == 1 else S.Seq(tuple(flat))


def procedure(system: System, c: S.Contract, p: S.Procedure) -> S.Stmt:
    """The core statement for a transaction calling procedure `p` of contract `c`."""
    this = S.ContractAddr(c.name)
    stmts: List[S.Stmt] = []
    if system.uses_block_num:
        stmts.append(S.SetBlockNum())
    stmts.append(S.Require(_and(S.BinOp("!=", S.Sender(), S.NullLit()),
                                S.BinOp("!=", S.Sender(), this))))
    stmts.append(callee(system, c, p, ()))
    return _seq(stmts)


def callee(system: System, c: S.Contract, p: S.Procedure,
           stack: Tuple[Tuple[str, str], ...]) -> S.Stmt:
    """initPay, the constructed guard, the uint guards, and the body of `p`; `stack` lists
    the procedures being unfolded (to reject cyclic calls)."""
    this = S.ContractAddr(c.name)
    stmts: List[S.Stmt] = [S.Send(S.Sender(), this, S.Value()) if p.payable
                           else S.Require(S.BinOp("==", S.Value(), S.IntLit(0)))]
    if p.name == S.CONSTRUCTOR:
        stmts += [S.Require(S.UnOp("!", S.Constructed(c.name))), S.SetConstructed(c.name)]
    else:
        stmts.append(S.Require(S.Constructed(c.name)))
    uint_guards = [S.BinOp(">=", S.Param(c.name, p.name, x.name), S.IntLit(0))
                   for x in p.params if x.type == S.UINT]
    if uint_guards:
        cond = uint_guards[0]
        for g in uint_guards[1:]:
            cond = _and(cond, g)
        stmts.append(S.Require(cond))
    stmts.append(_stmt(system, c, p.body, stack + ((c.name, p.name),)))
    return _seq(stmts)


def body(system: System, c: S.Contract, s: S.Stmt) -> S.Stmt:
    """The core statement for a statement of a procedure body of `c` (no guards added)."""
    return _stmt(system, c, s, ())


def _stmt(system: System, c: S.Contract, s: S.Stmt, stack) -> S.Stmt:
    rec = lambda x: _stmt(system, c, x, stack)
    if isinstance(s, (S.Skip, S.Require)):
        return s
    if isinstance(s, S.Seq):
        return _seq([rec(x) for x in s.stmts])
    if isinstance(s, S.If):
        return S.If(s.cond, rec(s.then), rec(s.orelse), s.pos)
    if isinstance(s, S.Assign):
        t = system.field_type(c.name, s.target)
        value_type = t.value if isinstance(t, S.MapType) else t
        assign = S.SetField(c.name, s.target, s.key, s.value, s.pos)
        if value_type == S.UINT:
            return _seq([S.Require(S.BinOp(">=", s.value, S.IntLit(0)), s.pos), assign])
        return assign
    if isinstance(s, S.Transfer):
        return S.Send(S.ContractAddr(c.name), s.to, s.amount, s.pos)
    if isinstance(s, S.Call):
        d = system.program.contract(s.callee.contract)
        g = d.proc(s.proc)
        if (d.name, g.name) in stack:
            chain = " -> ".join(f"{x}.{y}" for x, y in stack + ((d.name, g.name),))
            raise KindHMLError(f"cyclic contract calls are not supported (A4): {chain}", s.pos)
        return S.Unfold(c.name, d.name, g.name, s.args, s.value,
                        callee(system, d, g, stack), s.pos)
    raise KindHMLError(f"unexpected statement {s!r}", getattr(s, "pos", None))
