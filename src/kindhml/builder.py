"""Parsing: source text -> raw AST (see `syntax.py`)."""

from __future__ import annotations

import re
from fractions import Fraction
from typing import List, Optional, Tuple

from antlr4 import CommonTokenStream, InputStream, Token
from antlr4.error.ErrorListener import ErrorListener

from . import syntax as S
from .errors import KindHMLError
from .grammar.KindHMLLexer import KindHMLLexer
from .grammar.KindHMLParser import KindHMLParser
from .grammar.KindHMLVisitor import KindHMLVisitor

GROUNDTRUTH_RE = re.compile(r"@groundtruth:\s*(True|False)\b")

QTYPES = {
    "int": S.INT, "uint": S.UINT, "real": S.REAL, "bool": S.BOOL, "address": S.ADDRESS,
    "method": S.METHOD, "proc": S.METHOD,
    "calldataargs": S.ARGS, "args": S.ARGS,
}


class _RaisingErrorListener(ErrorListener):
    def __init__(self, source: str = ""):
        self.source = source

    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        raise KindHMLError(f"syntax error: {msg}", S.Pos(line, column + 1, self.source))


def _pos(ctx) -> S.Pos:
    """Position of a parse-tree node or of a token (with the source name of its input
    stream, see `_parser`)."""
    tok = ctx if isinstance(ctx, Token) else ctx.start
    return S.Pos(tok.line, tok.column + 1, tok.getInputStream().name)


class _Builder(KindHMLVisitor):
    def __init__(self, tokens: CommonTokenStream):
        self.tokens = tokens

    # ---------------------------------------------------------- program

    def visitProgram(self, ctx):
        balance_type = S.INT
        for p in ctx.pragma():
            t = self.visit(p.type_())
            if p.key.text != "balance" or t not in (S.INT, S.REAL):
                raise KindHMLError("the only pragmas are 'pragma balance int' and"
                                   " 'pragma balance real'", _pos(p))
            balance_type = t
        contracts = tuple(self.visit(c) for c in ctx.contract())
        rules = tuple(self.visit(r) for r in ctx.rule_())
        return S.Program(contracts, rules, balance_type)

    def visitContract(self, ctx):
        fields: List[S.VarDecl] = []
        procs: List[S.Procedure] = []
        for m in ctx.member():
            decl = self.visit(m)
            (fields if isinstance(decl, S.VarDecl) else procs).append(decl)
        ctors = [p for p in procs if p.name == S.CONSTRUCTOR]
        if len(ctors) > 1:
            raise KindHMLError("more than one constructor", ctors[1].pos)
        if not ctors:
            # A contract without constructor has an implicit empty one.
            ctors = [S.Procedure(S.CONSTRUCTOR, (), False, S.Skip(), _pos(ctx))]
        others = [p for p in procs if p.name != S.CONSTRUCTOR]
        return S.Contract(ctx.name.text, tuple(fields), tuple(ctors + others), _pos(ctx))

    def visitFieldDecl(self, ctx):
        return S.VarDecl(self.visit(ctx.type_()), ctx.name.text, _pos(ctx))

    def _procedure(self, name, ctx):
        params = tuple(self.visit(p) for p in ctx.params().param()) if ctx.params() else ()
        payable = any(m.getText() == "payable" for m in ctx.modifier())
        return S.Procedure(name, params, payable, self.visit(ctx.block()), _pos(ctx))

    def visitConstructorDecl(self, ctx):
        return self._procedure(S.CONSTRUCTOR, ctx)

    def visitFunctionDecl(self, ctx):
        return self._procedure(ctx.name.text, ctx)

    def visitParam(self, ctx):
        return S.VarDecl(self.visit(ctx.type_()), ctx.name.text, _pos(ctx))

    def visitIntType(self, ctx):
        return S.INT

    def visitUintType(self, ctx):
        return S.UINT

    def visitRealType(self, ctx):
        return S.REAL

    def visitBoolType(self, ctx):
        return S.BOOL

    def visitAddressType(self, ctx):
        return S.ADDRESS

    def visitMappingType(self, ctx):
        value = self.visit(ctx.type_())
        if isinstance(value, S.MapType):
            raise KindHMLError("nested mappings are not supported", _pos(ctx))
        return S.MapType(value)

    # ---------------------------------------------------------- statements

    def visitBlock(self, ctx):
        return self.visit(ctx.stmts()) if ctx.stmts() else S.Skip(_pos(ctx))

    def visitStmts(self, ctx):
        stmts = tuple(self.visit(s) for s in ctx.stmt())
        return stmts[0] if len(stmts) == 1 else S.Seq(stmts, _pos(ctx))

    def visitStmtBody(self, ctx):
        return self.visit(ctx.getChild(0))

    def visitSkipStmt(self, ctx):
        return S.Skip(_pos(ctx))

    def visitRequireStmt(self, ctx):
        return S.Require(self.visit(ctx.expr()), _pos(ctx))

    def visitIfStmt(self, ctx):
        orelse = self.visit(ctx.orelse) if ctx.orelse else S.Skip(_pos(ctx))
        return S.If(self.visit(ctx.expr()), self.visit(ctx.body), orelse, _pos(ctx))

    def visitAssignStmt(self, ctx):
        pos = _pos(ctx)
        target = ctx.target.text
        key = self.visit(ctx.key) if ctx.key else None
        value = self.visit(ctx.value)
        op = ctx.op.text
        if op != "=":
            current = S.Name(target, pos) if key is None else S.Index(S.Name(target, pos), key, pos)
            value = S.BinOp(op[0], current, value, pos)
        return S.Assign(target, key, value, pos)

    def visitCallStmt(self, ctx):
        pos = _pos(ctx)
        obj = self.visit(ctx.obj)
        args = self._exprs(ctx.exprs())
        method = ctx.method.text
        if method == "transfer" and ctx.value is None:
            if len(args) != 1:
                raise KindHMLError("transfer requires exactly one argument", pos)
            return S.Transfer(obj, args[0], pos)
        value = self.visit(ctx.value) if ctx.value else S.IntLit(0, pos)
        return S.Call(obj, method, args, value, pos)

    def visitBlockStmt(self, ctx):
        return self.visit(ctx.block())

    def visitParenStmt(self, ctx):
        return self.visit(ctx.stmts())

    # ---------------------------------------------------------- rules

    def visitRule_(self, ctx):
        return S.Rule(ctx.name.text, self.visit(ctx.expr()), self._groundtruth(ctx), _pos(ctx),
                      invariant=ctx.kind.text == "invariant")

    def _groundtruth(self, ctx) -> Optional[bool]:
        """The last `@groundtruth: True|False` comment right before the rule; otherwise
        the suffix `_true`/`_false` of the rule name (convention of the Solvent regressions)."""
        hidden = self.tokens.getHiddenTokensToLeft(ctx.start.tokenIndex) or []
        found = None
        for tok in hidden:
            m = GROUNDTRUTH_RE.search(tok.text)
            if m:
                found = m.group(1) == "True"
        if found is None:
            name = ctx.name.text
            if name.endswith("_true"):
                found = True
            elif name.endswith("_false"):
                found = False
        return found

    # ---------------------------------------------------------- expressions

    def _exprs(self, ctx):
        return tuple(self.visit(e) for e in ctx.expr()) if ctx else ()

    def visitParenExpr(self, ctx):
        return self.visit(ctx.expr())

    def visitIntLit(self, ctx):
        return S.IntLit(int(ctx.getText()), _pos(ctx))

    def visitRealLit(self, ctx):
        return S.RealLit(Fraction(ctx.getText()), _pos(ctx))

    def visitBoolLit(self, ctx):
        return S.BoolLit(ctx.getText() == "true", _pos(ctx))

    def visitNullLit(self, ctx):
        return S.NullLit(_pos(ctx))

    def visitPayableExpr(self, ctx):
        return self.visit(ctx.expr())

    def visitFunCallExpr(self, ctx):
        pos = _pos(ctx)
        fn = ctx.fn.text
        args = self._exprs(ctx.exprs())
        if fn == "old" and len(args) == 1:
            return S.Old(args[0], pos)
        if fn == "is_EOA" and len(args) == 1:
            return S.IsEOA(args[0], pos)
        if fn == "sum" and len(args) == 1:
            arg = args[0]
            if isinstance(arg, S.Name) and arg.name == "balance":
                arg = S.Balance(arg.pos)
            return S.SumMap(arg, pos)
        raise KindHMLError(f"unknown function '{fn}' with {len(args)} argument(s)", pos)

    def visitNameExpr(self, ctx):
        pos = _pos(ctx)
        name = ctx.getText()
        if name in ("lastReverted", "reverted"):
            return S.Reverted(pos)
        if name == "this":
            return S.Name("this", pos)
        return S.Name(name, pos)

    def visitMemberExpr(self, ctx):
        pos = _pos(ctx)
        obj = self.visit(ctx.expr())
        name = ctx.ID().getText()
        if isinstance(obj, S.Name):
            special = {("msg", "sender"): S.Sender, ("msg", "value"): S.Value,
                       ("block", "number"): S.BlockNum}.get((obj.name, name))
            if special:
                return special(pos)
        if name == "balance":
            return S.Index(S.Balance(pos), obj, pos)
        return S.Member(obj, name, pos)

    def visitIndexExpr(self, ctx):
        return S.Index(self.visit(ctx.expr(0)), self.visit(ctx.expr(1)), _pos(ctx))

    def visitUnaryExpr(self, ctx):
        arg = self.visit(ctx.expr())
        if ctx.op.text == "-" and isinstance(arg, S.IntLit):
            return S.IntLit(-arg.value, _pos(ctx))
        if ctx.op.text == "-" and isinstance(arg, S.RealLit):
            return S.RealLit(-arg.value, _pos(ctx))
        return S.UnOp(ctx.op.text, arg, _pos(ctx))

    def _binop(self, ctx, op=None):
        op = op or ctx.op.text
        op = {"and": "&&", "or": "||", "implies": "->"}.get(op, op)
        return S.BinOp(op, self.visit(ctx.expr(0)), self.visit(ctx.expr(1)), _pos(ctx))

    visitMulExpr = visitAddExpr = visitCmpExpr = visitEqExpr = _binop
    visitAndExpr = visitOrExpr = visitImpliesExpr = _binop

    def visitQuantExpr(self, ctx):
        pos = _pos(ctx)
        qv = ctx.qvars()
        tname = qv.qtype().getText()
        if tname not in QTYPES:
            raise KindHMLError(f"unknown quantifier type '{tname}'", _pos(qv.qtype()))
        body = self.visit(ctx.expr())
        for var in reversed(qv.ID()):
            body = S.Quant(ctx.q.text, var.getText(), QTYPES[tname], body, pos)
        return body

    def visitModalExpr(self, ctx):
        pos = _pos(ctx)
        exprs = ctx.expr()
        sender = self.visit(ctx.sender)
        # expr() lists sender, the actual parameters, the value and the block increase (if
        # any), the body.
        args = self._exprs(ctx.exprs())
        value = self.visit(ctx.value) if ctx.value else S.IntLit(0, pos)
        blocks = self.visit(ctx.blocks) if ctx.blocks else S.IntLit(0, pos)
        body = self.visit(exprs[-1])
        return S.Modal(sender, ctx.contractName.text, S.Name(ctx.proc.text, _pos(ctx.proc)),
                       args, value, blocks, body, pos)


def _parser(text: str, source: str = ""):
    """The token stream and the parser of `text`; `source` (a file name, possibly empty)
    goes in the positions."""
    stream = InputStream(text)
    stream.name = source
    lexer = KindHMLLexer(stream)
    lexer.removeErrorListeners()
    lexer.addErrorListener(_RaisingErrorListener(source))
    tokens = CommonTokenStream(lexer)
    parser = KindHMLParser(tokens)
    parser.removeErrorListeners()
    parser.addErrorListener(_RaisingErrorListener(source))
    return tokens, parser


def parse(text: str, source: str = "") -> S.Program:
    """Parse a KindHML source text into a raw AST. Raises KindHMLError."""
    tokens, parser = _parser(text, source)
    return _Builder(tokens).visit(parser.program())


def parse_spec(text: str, source: str = "") -> Tuple[S.Rule, ...]:
    """Parse a text of rules only (a spec file, see `verify.load`) into raw rules. Raises
    KindHMLError."""
    tokens, parser = _parser(text, source)
    builder = _Builder(tokens)
    return tuple(builder.visit(r) for r in parser.spec().rule_())


def parse_expr(text: str) -> S.Expr:
    """Parse a single expression (raw AST), e.g. a generated invariant. Raises KindHMLError."""
    tokens, parser = _parser(text)
    tree = parser.expr()
    if tokens.LA(1) != Token.EOF:
        raise KindHMLError(f"unexpected text after the expression in '{text}'")
    return _Builder(tokens).visit(tree)
