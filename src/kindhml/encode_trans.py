"""Encoding of contracts: Init, S^i(s), Trans_f, Trans_C, Trans (Sect. `sec:encoding:contract`).

Lustre representation (see DESIGN.md, Sect. 2):

* a state (an assignment of StateVars) is a value of the record type `St`;
* a transaction label (an assignment of TransVars) is a value of the record type `Tx`;
* maps `address => τ` (and `balance`) are records with one field `k_a` per address a;
* the level i of a procedure body is the local variable `l<i>` (level 0 is the input `s`);
* `Trans_f` is the function `trans_<C>_<f>`, `Trans_C` is `trans_<C>`, `Trans` is `trans`.
  Kind 2 inlines these functions, which yields the functions χ_v of the paper.
"""

from __future__ import annotations

from typing import Callable, Dict, List, Optional, Tuple

from . import desugar
from . import lustre as L
from . import syntax as S
from .errors import KindHMLError
from .model import NULL, System

ST, TX, ADDR, PROC = "St", "Tx", "address", "proc"
REVERT, BALANCE, BLOCK = "revert", "balance", "block_num"

BINOPS = {"&&": "and", "||": "or", "->": "=>", "==": "=", "!=": "<>", "/": "div", "%": "mod",
          "+": "+", "-": "-", "*": "*", "<": "<", "<=": "<=", ">": ">", ">=": ">="}


def addr_const(a: str) -> str:
    return f"A_{a}"


def key_field(a: str) -> str:
    return f"k_{a}"


def addr_is(a: str, e: L.LExpr) -> L.LExpr:
    """The formula `A_a = e`, simplified when e is an address constant."""
    if isinstance(e, L.Var) and e.name.startswith("A_"):
        return L.Bool(e.name == addr_const(a))
    return L.op("=", L.Var(addr_const(a)), e)


def proc_const(contract: str, proc: str) -> str:
    return f"P_{contract}_{proc}"


def field_var(contract: str, name: str) -> str:
    return f"{contract}_{name}"


def constructed_var(contract: str) -> str:
    return f"constructed_{contract}"


def param_var(contract: str, proc: str, name: str) -> str:
    return f"{contract}_{proc}_{name}"


def base_type(t: S.Type) -> str:
    return {S.INT: "int", S.UINT: "int", S.BOOL: "bool", S.ADDRESS: ADDR, S.METHOD: PROC}[t]


def map_type(t: S.Type) -> str:
    return f"Map_{base_type(t)}"


def lustre_type(t: S.AnyType) -> str:
    return map_type(t.value) if isinstance(t, S.MapType) else base_type(t)


def default_value(t: S.AnyType, system: System) -> L.LExpr:
    if isinstance(t, S.MapType):
        v = default_value(t.value, system)
        return L.record(map_type(t.value), [(key_field(a), v) for a in system.addresses])
    return {"int": L.Int(0), "bool": L.FALSE, ADDR: L.Var(addr_const(NULL))}[base_type(t)]


def divisors(e: S.Expr) -> List[S.Expr]:
    """The divisors e'' of all subexpressions e'/e'' (and e' % e'') of e."""
    out: List[S.Expr] = []

    def visit(x):
        if isinstance(x, S.BinOp):
            visit(x.left)
            visit(x.right)
            if x.op in ("/", "%"):
                out.append(x.right)
        elif isinstance(x, (S.UnOp, S.Old, S.IsEOA)):
            visit(x.arg)
        elif isinstance(x, S.Index):
            visit(x.key)
    visit(e)
    return out


class Frame:
    """The meaning of `msg.sender`, `msg.value`, and the parameters in a procedure body:
    the transition variables for a transaction, or, in a contract call unfolded at level i,
    the caller and the terms of the actual parameters and value at level i."""

    def __init__(self, sender: L.LExpr, value: L.LExpr,
                 params: Optional[Dict[Tuple[str, str, str], L.LExpr]], tx: L.LExpr):
        self.sender, self.value, self.params, self.tx = sender, value, params, tx

    @staticmethod
    def of(t) -> "Frame":
        """`t` itself if it is a frame; the frame of a transaction if it is a Tx term."""
        if isinstance(t, Frame):
            return t
        return Frame(L.Proj(t, "sender"), L.Proj(t, "value"), None, t)

    def param(self, contract: str, proc: str, name: str) -> L.LExpr:
        if self.params is None:
            return L.Proj(self.tx, param_var(contract, proc, name))
        return self.params[(contract, proc, name)]


class Encoder:
    def __init__(self, system: System):
        self.system = system

    # ------------------------------------------------------------ variables

    def state_fields(self) -> List[Tuple[str, str]]:
        """StateVars: balance, revert, constructed_C, contract fields, [block_num]."""
        fields = [(BALANCE, map_type(S.INT)), (REVERT, "bool")]
        fields += [(constructed_var(c.name), "bool") for c in self.system.contracts]
        fields += [(field_var(c.name, f.name), lustre_type(f.type))
                   for c in self.system.contracts for f in c.fields]
        if self.system.uses_block_num:
            fields.append((BLOCK, "int"))
        return fields

    def tx_fields(self) -> List[Tuple[str, str]]:
        """TransVars: sender, cx, fx, value, ParamVars, [block_num]."""
        fields = [("sender", ADDR), ("cx", ADDR), ("fx", PROC), ("value", "int")]
        fields += [(param_var(v.contract, v.proc, v.name), base_type(v.type))
                   for v in self.system.param_vars]
        if self.system.uses_block_num:
            fields.append((BLOCK, "int"))
        return fields

    def map_value_types(self) -> List[S.Type]:
        types = [S.INT]
        for c in self.system.contracts:
            for f in c.fields:
                if isinstance(f.type, S.MapType):
                    t = S.INT if f.type.value == S.UINT else f.type.value
                    if t not in types:
                        types.append(t)
        return types

    # ------------------------------------------------------------ expressions

    def expr(self, e: S.Expr, s: L.LExpr, t: Optional[L.LExpr],
             other: Optional[Callable[[S.Expr], L.LExpr]] = None) -> L.LExpr:
        """e^i: the encoding of e in state s (a term of type St) and transaction t.

        `other` encodes the nodes that only occur in formulae (QVar, Old, ...)."""
        rec = lambda x: self.expr(x, s, t, other)
        if isinstance(e, S.IntLit):
            return L.Int(e.value)
        if isinstance(e, S.BoolLit):
            return L.Bool(e.value)
        if isinstance(e, S.NullLit):
            return L.Var(addr_const(NULL))
        if isinstance(e, S.ContractAddr):
            return L.Var(addr_const(e.contract))
        if isinstance(e, S.ProcConst):
            return L.Var(proc_const(e.contract, e.proc))
        if isinstance(e, S.Field):
            return L.proj(s, field_var(e.contract, e.name))
        if isinstance(e, S.Index):
            if isinstance(e.map, S.Balance):
                return self.get(S.INT, L.proj(s, BALANCE), rec(e.key))
            ft = self.system.field_type(e.map.contract, e.map.name)
            return self.get(ft.value, L.proj(s, field_var(e.map.contract, e.map.name)), rec(e.key))
        if isinstance(e, S.Constructed):
            return L.proj(s, constructed_var(e.contract))
        if isinstance(e, S.BlockNum):
            return L.proj(s, BLOCK)
        if isinstance(e, S.Reverted):
            return L.proj(s, REVERT)
        if isinstance(e, S.IsEOA):
            return L.call("is_eoa", rec(e.arg))
        if isinstance(e, S.UnOp):
            return L.neg(rec(e.arg)) if e.op == "!" else L.op("-", rec(e.arg))
        if isinstance(e, S.BinOp):
            return L.op(BINOPS[e.op], rec(e.left), rec(e.right))
        if t is not None:
            frame = Frame.of(t)
            if isinstance(e, S.Param):
                return frame.param(e.contract, e.proc, e.name)
            if isinstance(e, S.Sender):
                return frame.sender
            if isinstance(e, S.Value):
                return frame.value
            if isinstance(e, S.TxBlockNum):
                return L.Proj(frame.tx, BLOCK)
        if other is not None:
            return other(e)
        raise KindHMLError(f"cannot encode expression {e!r}", getattr(e, "pos", None))

    def get(self, value_type: S.Type, m: L.LExpr, key: L.LExpr) -> L.LExpr:
        """m[key] for a map record m."""
        if isinstance(key, L.Var) and key.name.startswith("A_"):
            return L.proj(m, key_field(key.name[2:]))
        return L.call(f"get_{base_type(value_type)}", m, key)

    def definedness(self, exprs: List[S.Expr], s: L.LExpr, t: L.LExpr) -> L.LExpr:
        """def^i: all divisors occurring in `exprs` are nonzero."""
        return L.conj([L.op("<>", self.expr(d, s, t), L.Int(0))
                       for e in exprs for d in divisors(e)])

    # ------------------------------------------------------------ statements

    @staticmethod
    def length(stmt: S.Stmt) -> int:
        """|s|: |s1;s2| = |s1|+|s2|, |if e s1 s2| = max(|s1|,|s2|), 1 otherwise."""
        if isinstance(stmt, S.Seq):
            return sum(Encoder.length(x) for x in stmt.stmts)
        if isinstance(stmt, S.If):
            return max(Encoder.length(stmt.then), Encoder.length(stmt.orelse))
        if isinstance(stmt, S.Unfold):
            return Encoder.length(stmt.body)
        return 1

    def update(self, level: L.LExpr, changes: Dict[str, L.LExpr]) -> L.LExpr:
        """The record equal to `level` except for `changes`; revert defaults to false
        (the omitted constraints of Table `tab:statement-to-fol`)."""
        changes = {REVERT: L.FALSE, **changes}
        return L.record(ST, [(n, changes.get(n, L.Proj(level, n))) for n, _ in self.state_fields()])

    def step(self, stmt: S.Stmt, s: L.LExpr, t: L.LExpr) -> L.LExpr:
        """S^i(a) for an atomic statement a, as the value of level i+1 given level i = s."""
        e = lambda x: self.expr(x, s, t)
        if isinstance(stmt, S.Skip):
            return self.update(s, {})
        if isinstance(stmt, S.Require):
            return self.update(s, {REVERT: L.neg(e(stmt.cond))})
        if isinstance(stmt, S.SetField):
            name = field_var(stmt.contract, stmt.name)
            if stmt.key is None:
                return self.update(s, {name: e(stmt.value)})
            vt = self.system.field_type(stmt.contract, stmt.name).value
            key, value, old = e(stmt.key), e(stmt.value), L.Proj(s, name)
            new = L.record(map_type(vt), [
                (key_field(a), L.ite(addr_is(a, key), value,
                                     L.Proj(old, key_field(a))))
                for a in self.system.addresses])
            return self.update(s, {name: new})
        if isinstance(stmt, S.Send):
            return self.send(stmt, s, t)
        if isinstance(stmt, S.SetConstructed):
            return self.update(s, {constructed_var(stmt.contract): L.TRUE})
        if isinstance(stmt, S.SetBlockNum):
            return self.update(s, {BLOCK: L.Proj(t, BLOCK)})
        raise KindHMLError(f"cannot encode statement {stmt!r}", getattr(stmt, "pos", None))

    def send(self, stmt: S.Send, s: L.LExpr, t: L.LExpr) -> L.LExpr:
        """ITE(send_enabled^i(e0,e1,e2), revert^{i+1} = false ∧ send^i(e0,e1,e2),
        revert^{i+1} = true)."""
        src, dst, amount = (self.expr(x, s, t) for x in (stmt.src, stmt.dst, stmt.amount))
        bal = L.Proj(s, BALANCE)
        enabled = L.conj([L.op(">=", self.get(S.INT, bal, src), amount),
                          L.op(">=", amount, L.Int(0)), L.op("<>", src, dst)])
        sent = L.record(map_type(S.INT), [
            (key_field(a), L.ite(addr_is(a, src),
                                 L.op("-", L.Proj(bal, key_field(a)), amount),
                                 L.ite(addr_is(a, dst),
                                       L.op("+", L.Proj(bal, key_field(a)), amount),
                                       L.Proj(bal, key_field(a)))))
            for a in self.system.addresses])
        return self.update(s, {BALANCE: L.ite(enabled, sent, bal), REVERT: L.neg(enabled)})

    @staticmethod
    def level(i: int) -> L.LExpr:
        return L.Var("s") if i == 0 else L.Var(f"l{i}")

    def levels(self, stmt: S.Stmt, i: int, t: L.LExpr) -> Dict[int, L.LExpr]:
        """S^i(s): the values of the levels i+1, ..., i+|s| (each in terms of the previous
        levels). A statement whose def^i is not trivially true is encoded as
        ITE(def^i(s), S^i(s), S^i(pad_{|s|}(require false)))."""
        if isinstance(stmt, S.Seq):
            out: Dict[int, L.LExpr] = {}
            for x in stmt.stmts:
                out.update(self.levels(x, i, t))
                i += self.length(x)
            return out
        s = self.level(i)
        n = self.length(stmt)
        if isinstance(stmt, S.If):
            cond = self.expr(stmt.cond, s, t)
            then = self.levels(self.pad(stmt.then, n), i, t)
            orelse = self.levels(self.pad(stmt.orelse, n), i, t)
            body = {k: L.ite(cond, then[k], orelse[k]) for k in then}
            direct = [stmt.cond]
        elif isinstance(stmt, S.Unfold):
            # The actual parameters and the value are evaluated at the call point (level i);
            # in the callee, sender is the caller (Sect. `sec:encoding:contract`).
            params = self.system.params_of(stmt.callee, stmt.proc)
            frame = Frame(L.Var(addr_const(stmt.caller)), self.expr(stmt.value, s, t),
                          {(v.contract, v.proc, v.name): self.expr(a, s, t)
                           for v, a in zip(params, stmt.args)},
                          Frame.of(t).tx)
            body = self.levels(stmt.body, i, frame)
            direct = list(stmt.args) + [stmt.value]
        else:
            body = {i + 1: self.step(stmt, s, t)}
            direct = self.direct_exprs(stmt)
        defined = self.definedness(direct, s, t)
        if defined == L.TRUE:
            return body
        failed = self.levels(self.pad(S.Require(S.BoolLit(False)), n), i, t)
        return {k: L.ite(defined, body[k], failed[k]) for k in body}

    @staticmethod
    def direct_exprs(stmt: S.Stmt) -> List[S.Expr]:
        if isinstance(stmt, S.Require):
            return [stmt.cond]
        if isinstance(stmt, S.SetField):
            return [stmt.value] + ([stmt.key] if stmt.key is not None else [])
        if isinstance(stmt, S.Send):
            return [stmt.src, stmt.dst, stmt.amount]
        return []

    def pad(self, stmt: S.Stmt, n: int) -> S.Stmt:
        k = n - self.length(stmt)
        return stmt if k == 0 else S.Seq((stmt,) + (S.Skip(),) * k)

    # ------------------------------------------------------------ transition relation

    def trans_proc(self, c: S.Contract, p: S.Procedure) -> L.Function:
        """Trans_f := S^0(s0;s) ∧ ITE(∨_i revert^i, revert^nx = true ∧ v^nx = v^0, v^nx = v^m)."""
        body = desugar.procedure(self.system, c, p)
        t = L.Var("t")
        levels = self.levels(body, 0, t)
        m = self.length(body)
        reverted = L.disj([L.Proj(self.level(k), REVERT) for k in range(1, m + 1)])
        result = L.ite(reverted, L.call("revert_state", L.Var("s")), self.level(m))
        return L.Function(
            f"trans_{c.name}_{p.name}", [("s", ST), ("t", TX)], [("r", ST)],
            locals=[(f"l{k}", ST) for k in range(1, m + 1)],
            equations=[(f"l{k}", levels[k]) for k in range(1, m + 1)] + [("r", result)],
            comment=f"Trans_{p.name} for contract {c.name}")

    def trans_contract(self, c: S.Contract) -> L.Function:
        """Trans_C := switch fx { case f1: Trans_f1 | ... | default: Revert }."""
        s, t = L.Var("s"), L.Var("t")
        result = L.call("revert_state", s)
        for p in reversed(c.procs):
            result = L.Ite(L.op("=", L.Proj(t, "fx"), L.Var(proc_const(c.name, p.name))),
                           L.call(f"trans_{c.name}_{p.name}", s, t), result)
        return L.Function(f"trans_{c.name}", [("s", ST), ("t", TX)], [("r", ST)],
                          equations=[("r", result)], comment=f"Trans_{c.name}")

    def trans(self) -> L.Function:
        """Trans := switch cx { case c1: Trans_c1 | ... | default: Revert }."""
        s, t = L.Var("s"), L.Var("t")
        result = L.call("revert_state", s)
        for c in reversed(self.system.contracts):
            result = L.Ite(L.op("=", L.Proj(t, "cx"), L.Var(addr_const(c.name))),
                           L.call(f"trans_{c.name}", s, t), result)
        return L.Function("trans", [("s", ST), ("t", TX)], [("r", ST)],
                          equations=[("r", result)], comment="Trans")

    def init(self) -> L.Function:
        """Init: the balances are given (and nonnegative, see the main node), contracts are
        not constructed, all other variables have default values."""
        values = {BALANCE: L.Var("ib"), REVERT: L.FALSE}
        for c in self.system.contracts:
            values[constructed_var(c.name)] = L.FALSE
            for f in c.fields:
                values[field_var(c.name, f.name)] = default_value(f.type, self.system)
        if self.system.uses_block_num:
            values[BLOCK] = L.Int(0)
        return L.Function("init", [("ib", map_type(S.INT))], [("r", ST)],
                          equations=[("r", L.record(ST, [(n, values[n])
                                                         for n, _ in self.state_fields()]))],
                          comment="Init")

    # ------------------------------------------------------------ program

    def helpers(self) -> List[L.Function]:
        a = L.Var("a")
        out = []
        for vt in self.map_value_types():
            result = L.Proj(L.Var("m"), key_field(self.system.addresses[-1]))
            for x in reversed(self.system.addresses[:-1]):
                result = L.Ite(L.op("=", a, L.Var(addr_const(x))),
                               L.Proj(L.Var("m"), key_field(x)), result)
            out.append(L.Function(f"get_{base_type(vt)}", [("m", map_type(vt)), ("a", ADDR)],
                                  [("r", base_type(vt))], equations=[("r", result)]))
        eoa = L.conj([L.op("<>", a, L.Var(addr_const(x)))
                      for x in [NULL] + [c.name for c in self.system.contracts]])
        out.append(L.Function("is_eoa", [("a", ADDR)], [("r", "bool")], equations=[("r", eoa)],
                              comment="a is a user address (neither null nor a contract)"))
        s = L.Var("s")
        out.append(L.Function("revert_state", [("s", ST)], [("r", ST)],
                              equations=[("r", L.record(ST, [
                                  (n, L.TRUE if n == REVERT else L.Proj(s, n))
                                  for n, _ in self.state_fields()]))],
                              comment="Revert: the state is unchanged, the revert flag is set"))
        return out

    def types(self) -> list:
        out = [L.EnumType(ADDR, [addr_const(a) for a in self.system.addresses]),
               L.EnumType(PROC, [proc_const(c.name, p.name) for c, p in self.system.methods])]
        out += [L.StructType(map_type(vt), [(key_field(a), base_type(vt))
                                            for a in self.system.addresses])
                for vt in self.map_value_types()]
        out += [L.StructType(ST, self.state_fields()), L.StructType(TX, self.tx_fields())]
        return out

    def main_node(self) -> L.Function:
        """The transition system: s = Init -> pre Trans(s, t)."""
        s, t, ib = L.Var("s"), L.Var("t"), L.Var("ib")
        asserts = [L.conj([L.op(">=", L.Proj(ib, key_field(a)), L.Int(0))
                           for a in self.system.addresses])]
        if self.system.uses_block_num:
            asserts.append(L.op(">=", L.Proj(t, BLOCK), L.Proj(s, BLOCK)))
        return L.Function(
            "main", [("t", TX), ("ib", map_type(S.INT))], [], locals=[("s", ST)],
            asserts=asserts,
            equations=[("s", L.Arrow(L.call("init", ib), L.Pre(L.call("trans", s, t))))],
            node=True, comment="The transition system (Init, Trans)")

    def lemmas(self) -> List[Tuple[str, L.LExpr]]:
        """Invariants of every system, as auxiliary properties: all balances are nonnegative
        (Init makes them so, and a transfer requires 0 <= amount <= balance of the source)."""
        bal = L.Proj(L.Var("s"), BALANCE)
        return [("_lemma_balances_nonnegative",
                 L.conj([L.op(">=", L.Proj(bal, key_field(a)), L.Int(0))
                         for a in self.system.addresses]))]

    def program(self) -> Tuple[L.Program, L.Function]:
        """The Lustre program without properties, and its main node (to add properties to)."""
        prog = L.Program(self.types() + self.helpers())
        for c in self.system.contracts:
            prog.decls += [self.trans_proc(c, p) for p in c.procs]
            prog.decls.append(self.trans_contract(c))
        prog.decls += [self.trans(), self.init()]
        main = self.main_node()
        prog.decls.append(main)
        return prog, main
