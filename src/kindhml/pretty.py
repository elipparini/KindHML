"""Fully parenthesised printing of expressions (raw or resolved), for debugging and messages."""

from . import syntax as S
from .lustre import render_real


def expr(e: S.Expr) -> str:
    if isinstance(e, S.IntLit):
        return str(e.value)
    if isinstance(e, S.RealLit):
        return render_real(e.value) if e.value >= 0 else f"-{render_real(-e.value)}"
    if isinstance(e, S.ToReal):
        return f"real({expr(e.arg)})"
    if isinstance(e, S.BoolLit):
        return "true" if e.value else "false"
    if isinstance(e, S.NullLit):
        return "null"
    if isinstance(e, S.Name):
        return e.name
    if isinstance(e, S.Member):
        return f"{expr(e.obj)}.{e.name}"
    if isinstance(e, S.FunCall):
        return f"{e.fn}({', '.join(map(expr, e.args))})"
    if isinstance(e, S.Index):
        return f"{expr(e.map)}[{expr(e.key)}]"
    if isinstance(e, S.UnOp):
        return f"{e.op}{expr(e.arg)}"
    if isinstance(e, S.BinOp):
        return f"({expr(e.left)} {e.op} {expr(e.right)})"
    if isinstance(e, S.Quant):
        return f"({e.kind} {e.var}:{e.type}. {expr(e.body)})"
    if isinstance(e, S.Modal):
        args = ", ".join(map(expr, e.args))
        blocks = ("" if isinstance(e.blocks, S.IntLit) and e.blocks.value == 0
                  else f" @ {expr(e.blocks)}")
        return (f"(<< {expr(e.sender)} : {e.contract}.{expr(e.proc)}({args}) $ {expr(e.value)}"
                f"{blocks} >> {expr(e.body)})")
    if isinstance(e, S.Field):
        return e.name
    if isinstance(e, S.Param):
        return e.name
    if isinstance(e, S.QVar):
        return e.name
    if isinstance(e, S.ProcConst):
        return e.proc
    if isinstance(e, S.ContractAddr):
        return e.contract
    if isinstance(e, S.Balance):
        return "balance"
    if isinstance(e, S.Sender):
        return "msg.sender"
    if isinstance(e, S.Value):
        return "msg.value"
    if isinstance(e, S.BlockNum):
        return "block.number"
    if isinstance(e, S.Reverted):
        return "lastReverted"
    if isinstance(e, S.Old):
        return f"old({expr(e.arg)})"
    if isinstance(e, S.IsEOA):
        return f"is_EOA({expr(e.arg)})"
    raise TypeError(f"unknown expression {e!r}")
