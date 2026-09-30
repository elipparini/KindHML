"""Name resolution and type checking.

Contracts: the (typed version of the) language of Fig. `fig:contracts:syntax`.
Rules: the typing judgement Γ, n ⊢ e : T of the logic, where n is the modal depth
(`old(e)` at depth n needs e at depth n-1), plus assumptions A2 (maps indexed by
addresses), A6 (no `sender`/`value` in formulae) and A7 (each `args` variable is used in
exactly one modality).

`check(program)` returns a resolved program: `Name`, `Member`, `FunCall` are replaced by
the nodes they denote (see `syntax.py`).
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Dict, List, Optional, Tuple

from . import syntax as S
from .errors import KindHMLError

RESERVED = {"balance", "this", "sender", "value", "msg", "block", "null",
            "lastReverted", "reverted", "old", "is_EOA", "true", "false"}


def _err(msg: str, node) -> KindHMLError:
    return KindHMLError(msg, getattr(node, "pos", None))


def _compatible(expected: S.AnyType, actual: S.AnyType) -> bool:
    """`actual` can be used where `expected` is required (int and uint mix)."""
    return expected == actual or (S.is_int(expected) and S.is_int(actual))


@dataclass
class _Ctx:
    """Where an expression occurs."""
    contract: Optional[S.Contract] = None       # contract context: enclosing contract
    proc: Optional[S.Procedure] = None
    in_rule: bool = False
    depth: int = 0                              # modal depth (rules only)
    env: Dict[str, S.Type] = field(default_factory=dict)   # quantified variables

    def at(self, depth: int) -> "_Ctx":
        return replace(self, depth=depth)

    def bind(self, name: str, t: S.Type) -> "_Ctx":
        return replace(self, env={**self.env, name: t})


class Checker:
    def __init__(self, program: S.Program):
        self.program = program
        self.warnings: List[str] = []
        # Per rule: quantified names (unique within a rule, so a name identifies its
        # binder) and the number of modalities using each `args` variable (A7).
        self._bound: set = set()
        self._args_uses: Dict[str, int] = {}

    # ------------------------------------------------------------ program

    def check(self) -> S.Program:
        p = self.program
        self._unique([c.name for c in p.contracts], p.contracts, "contract")
        self._unique([r.name for r in p.rules], p.rules, "rule")
        contracts = tuple(self._contract(c) for c in p.contracts)
        rules = tuple(self._rule(r) for r in p.rules)
        return S.Program(contracts, rules)

    @staticmethod
    def _unique(names, nodes, what):
        seen = set()
        for n, node in zip(names, nodes):
            if n in seen:
                raise _err(f"duplicate {what} '{n}'", node)
            seen.add(n)

    # ------------------------------------------------------------ contracts

    def _contract(self, c: S.Contract) -> S.Contract:
        self._unique([f.name for f in c.fields], c.fields, "field")
        self._unique([p.name for p in c.procs], c.procs, "procedure")
        for f in c.fields:
            if f.name in RESERVED:
                raise _err(f"'{f.name}' is a reserved name", f)
        procs = tuple(self._procedure(c, p) for p in c.procs)
        return replace(c, procs=procs)

    def _procedure(self, c: S.Contract, p: S.Procedure) -> S.Procedure:
        self._unique([x.name for x in p.params], p.params, "parameter")
        for x in p.params:
            if isinstance(x.type, S.MapType):
                raise _err("parameters cannot have mapping type", x)
            if x.name in RESERVED or c.field_decl(x.name):
                raise _err(f"parameter '{x.name}' clashes with a field or a reserved name", x)
        ctx = _Ctx(contract=c, proc=p)
        return replace(p, body=self._stmt(p.body, ctx))

    def _stmt(self, s: S.Stmt, ctx: _Ctx) -> S.Stmt:
        c = ctx.contract
        if isinstance(s, S.Skip):
            return s
        if isinstance(s, S.Require):
            return replace(s, cond=self._expect(s.cond, S.BOOL, ctx))
        if isinstance(s, S.Seq):
            return replace(s, stmts=tuple(self._stmt(x, ctx) for x in s.stmts))
        if isinstance(s, S.If):
            return replace(s, cond=self._expect(s.cond, S.BOOL, ctx),
                           then=self._stmt(s.then, ctx), orelse=self._stmt(s.orelse, ctx))
        if isinstance(s, S.Assign):
            decl = c.field_decl(s.target)
            if decl is None:
                raise _err(f"'{s.target}' is not a field of contract {c.name}"
                           " (only fields can be assigned)", s)
            if s.key is None:
                if isinstance(decl.type, S.MapType):
                    raise _err(f"cannot assign the whole mapping '{s.target}'", s)
                return replace(s, value=self._expect(s.value, decl.type, ctx))
            if not isinstance(decl.type, S.MapType):
                raise _err(f"'{s.target}' is not a mapping", s)
            return replace(s, key=self._expect(s.key, S.ADDRESS, ctx),
                           value=self._expect(s.value, decl.type.value, ctx))
        if isinstance(s, S.Transfer):
            return replace(s, to=self._expect(s.to, S.ADDRESS, ctx),
                           amount=self._expect(s.amount, S.INT, ctx))
        if isinstance(s, S.Call):
            callee, _ = self._expr(s.callee, ctx)
            if not isinstance(callee, S.ContractAddr):
                raise _err("the callee of a contract call must be a contract name", s)
            target = self.program.contract(callee.contract)
            proc = target.proc(s.proc)
            if proc is None or proc.name == S.CONSTRUCTOR:
                raise _err(f"contract {target.name} has no procedure '{s.proc}'", s)
            args = self._actuals(proc, s.args, ctx, s)
            return replace(s, callee=callee, args=args, value=self._expect(s.value, S.INT, ctx))
        raise _err(f"unknown statement {s!r}", s)

    def _actuals(self, proc: S.Procedure, args, ctx: _Ctx, node) -> Tuple[S.Expr, ...]:
        if len(args) != len(proc.params):
            raise _err(f"procedure {proc.name} requires {len(proc.params)} argument(s),"
                       f" but {len(args)} are given", node)
        return tuple(self._expect(a, x.type, ctx) for a, x in zip(args, proc.params))

    # ------------------------------------------------------------ rules

    def _rule(self, r: S.Rule) -> S.Rule:
        self._bound, self._args_uses = set(), {}
        formula = self._expect(r.formula, S.BOOL, _Ctx(in_rule=True))
        return replace(r, formula=formula)

    # ------------------------------------------------------------ expressions

    def _expect(self, e: S.Expr, t: S.AnyType, ctx: _Ctx) -> S.Expr:
        r, rt = self._expr(e, ctx)
        if not _compatible(t, rt):
            raise _err(f"expected an expression of type {t}, found {rt}", e)
        return r

    def _expr(self, e: S.Expr, ctx: _Ctx) -> Tuple[S.Expr, S.AnyType]:
        """Resolve `e` and compute its type."""
        if isinstance(e, S.IntLit):
            return e, S.INT
        if isinstance(e, S.BoolLit):
            return e, S.BOOL
        if isinstance(e, S.NullLit):
            return e, S.ADDRESS
        if isinstance(e, S.Name):
            return self._name(e, ctx)
        if isinstance(e, S.Member):
            return self._member(e, ctx)
        if isinstance(e, (S.Sender, S.Value)):
            if ctx.in_rule:
                raise _err("msg.sender and msg.value cannot occur in rules (A6)", e)
            return e, (S.ADDRESS if isinstance(e, S.Sender) else S.INT)
        if isinstance(e, S.BlockNum):
            return e, S.INT
        if isinstance(e, S.Reverted):
            if not ctx.in_rule:
                raise _err("lastReverted can only occur in rules", e)
            return e, S.BOOL
        if isinstance(e, S.Old):
            if not ctx.in_rule:
                raise _err("old(...) can only occur in rules", e)
            if ctx.depth == 0:
                raise _err("old(...) must occur within the scope of a modality", e)
            arg, t = self._expr(e.arg, ctx.at(ctx.depth - 1))
            return replace(e, arg=arg), t
        if isinstance(e, S.IsEOA):
            return replace(e, arg=self._expect(e.arg, S.ADDRESS, ctx)), S.BOOL
        if isinstance(e, S.Index):
            return self._index(e, ctx)
        if isinstance(e, S.UnOp):
            t = S.BOOL if e.op == "!" else S.INT
            return replace(e, arg=self._expect(e.arg, t, ctx)), t
        if isinstance(e, S.BinOp):
            return self._binop(e, ctx)
        if isinstance(e, S.Quant):
            return self._quant(e, ctx)
        if isinstance(e, S.Modal):
            return self._modal(e, ctx)
        raise _err(f"unexpected expression {e!r}", e)

    def _single_contract(self, e) -> S.Contract:
        if len(self.program.contracts) != 1:
            raise _err(f"'{getattr(e, 'name', 'this')}' is ambiguous with several contracts;"
                       " qualify it with the contract name", e)
        return self.program.contracts[0]

    def _name(self, e: S.Name, ctx: _Ctx) -> Tuple[S.Expr, S.AnyType]:
        n = e.name
        if ctx.in_rule and n in ctx.env:
            return S.QVar(n, ctx.env[n], e.pos), ctx.env[n]
        if not ctx.in_rule:
            c, p = ctx.contract, ctx.proc
            decl = next((x for x in p.params if x.name == n), None)
            if decl:
                return S.Param(c.name, p.name, n, e.pos), decl.type
            if n == "sender":
                return self._expr(S.Sender(e.pos), ctx)
            if n == "value":
                return self._expr(S.Value(e.pos), ctx)
        if n == "this":
            c = ctx.contract or self._single_contract(e)
            return S.ContractAddr(c.name, e.pos), S.ADDRESS
        if n == "balance":
            c = ctx.contract or self._single_contract(e)
            return S.Index(S.Balance(e.pos), S.ContractAddr(c.name, e.pos), e.pos), S.INT
        # fields
        owners = [ctx.contract] if ctx.contract else list(self.program.contracts)
        with_field = [c for c in owners if c.field_decl(n)]
        if len(with_field) > 1:
            raise _err(f"field '{n}' is ambiguous; qualify it with the contract name", e)
        if with_field:
            c = with_field[0]
            return S.Field(c.name, n, e.pos), c.field_decl(n).type
        # procedure constants (type method), in rules only
        if ctx.in_rule:
            with_proc = [c for c in self.program.contracts if c.proc(n)]
            if len(with_proc) > 1:
                raise _err(f"procedure '{n}' is ambiguous; qualify it with the contract name", e)
            if with_proc:
                return S.ProcConst(with_proc[0].name, n, e.pos), S.METHOD
        # contract addresses
        if self.program.contract(n):
            return S.ContractAddr(n, e.pos), S.ADDRESS
        raise _err(f"unknown name '{n}'", e)

    def _member(self, e: S.Member, ctx: _Ctx) -> Tuple[S.Expr, S.AnyType]:
        """`C.x` (field of contract C) or `C.f` (procedure constant)."""
        if isinstance(e.obj, S.Name) and self.program.contract(e.obj.name):
            c = self.program.contract(e.obj.name)
            decl = c.field_decl(e.name)
            if decl:
                if ctx.contract and ctx.contract.name != c.name:
                    raise _err("a contract cannot read the fields of another contract", e)
                return S.Field(c.name, e.name, e.pos), decl.type
            if ctx.in_rule and c.proc(e.name):
                return S.ProcConst(c.name, e.name, e.pos), S.METHOD
        raise _err(f"unknown member '{e.name}'", e)

    def _index(self, e: S.Index, ctx: _Ctx) -> Tuple[S.Expr, S.AnyType]:
        key = self._expect(e.key, S.ADDRESS, ctx)
        if isinstance(e.map, S.Balance) or (isinstance(e.map, S.Name) and e.map.name == "balance"):
            return S.Index(S.Balance(e.map.pos), key, e.pos), S.INT
        m, t = self._expr(e.map, ctx)
        if not isinstance(t, S.MapType):
            raise _err("only mappings (and balance) can be indexed", e)
        return S.Index(m, key, e.pos), t.value

    def _binop(self, e: S.BinOp, ctx: _Ctx) -> Tuple[S.Expr, S.AnyType]:
        op = e.op
        if op in ("&&", "||", "->"):
            return replace(e, left=self._expect(e.left, S.BOOL, ctx),
                           right=self._expect(e.right, S.BOOL, ctx)), S.BOOL
        if op in ("+", "-", "*", "/", "%", "<", "<=", ">", ">="):
            if op in ("/", "%") and ctx.in_rule:
                self.warnings.append(f"{e.pos}: divisions in rules must be guarded (A3)")
            res = S.INT if op in ("+", "-", "*", "/", "%") else S.BOOL
            return replace(e, left=self._expect(e.left, S.INT, ctx),
                           right=self._expect(e.right, S.INT, ctx)), res
        if op in ("==", "!="):
            left, lt = self._expr(e.left, ctx)
            right, rt = self._expr(e.right, ctx)
            if isinstance(lt, S.MapType) or lt == S.ARGS or not _compatible(lt, rt):
                raise _err(f"cannot compare {lt} with {rt}", e)
            return replace(e, left=left, right=right), S.BOOL
        raise _err(f"unknown operator '{op}'", e)

    def _quant(self, e: S.Quant, ctx: _Ctx) -> Tuple[S.Expr, S.AnyType]:
        if e.var in RESERVED or e.var in self._bound or any(
                c.field_decl(e.var) or c.proc(e.var) or c.name == e.var
                for c in self.program.contracts):
            raise _err(f"quantified variable '{e.var}' clashes with another name"
                       " (quantified names must be unique within a rule)", e)
        self._bound.add(e.var)
        body = self._expect(e.body, S.BOOL, ctx.bind(e.var, e.type))
        if e.type == S.ARGS and self._args_uses.get(e.var, 0) == 0:
            self.warnings.append(f"{e.pos}: variable '{e.var}' of type calldataargs is not used")
        return replace(e, body=body), S.BOOL

    def _modal(self, e: S.Modal, ctx: _Ctx) -> Tuple[S.Expr, S.AnyType]:
        if not ctx.in_rule:
            raise _err("modalities can only occur in rules", e)
        c = self.program.contract(e.contract)
        if c is None:
            raise _err(f"unknown contract '{e.contract}'", e)
        sender = self._expect(e.sender, S.ADDRESS, ctx)
        value = self._expect(e.value, S.INT, ctx)
        name = e.proc.name
        if ctx.env.get(name) == S.METHOD:
            proc: S.Expr = S.QVar(name, S.METHOD, e.proc.pos)
            args = self._method_var_args(e, ctx)
        elif c.proc(name):
            proc = S.ProcConst(c.name, name, e.proc.pos)
            args = self._actuals(c.proc(name), e.args, ctx, e)
        else:
            raise _err(f"'{name}' is neither a procedure of {c.name} nor a variable of type"
                       " method", e.proc)
        body = self._expect(e.body, S.BOOL, ctx.at(ctx.depth + 1))
        return replace(e, sender=sender, proc=proc, args=args, value=value, body=body), S.BOOL

    def _method_var_args(self, e: S.Modal, ctx: _Ctx) -> Tuple[S.Expr, ...]:
        """`h(a)` with `a : calldataargs`, or `h()` (parameters existentially quantified)."""
        if not e.args:
            return ()
        if len(e.args) == 1 and isinstance(e.args[0], S.Name) \
                and ctx.env.get(e.args[0].name) == S.ARGS:
            a = e.args[0].name
            self._args_uses[a] = self._args_uses.get(a, 0) + 1
            if self._args_uses[a] > 1:
                raise _err(f"variable '{a}' of type calldataargs is used in more than one"
                           " modality (A7)", e)
            return (S.QVar(a, S.ARGS, e.args[0].pos),)
        raise _err("a procedure given by a variable of type method takes a single argument"
                   " of type calldataargs", e)


def check(program: S.Program) -> Tuple[S.Program, List[str]]:
    """Resolve and type-check a raw program. Returns the resolved program and warnings."""
    checker = Checker(program)
    return checker.check(), checker.warnings
