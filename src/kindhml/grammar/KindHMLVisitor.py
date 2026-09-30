# Generated from KindHML.g4 by ANTLR 4.13.2
from antlr4 import *
if "." in __name__:
    from .KindHMLParser import KindHMLParser
else:
    from KindHMLParser import KindHMLParser

# This class defines a complete generic visitor for a parse tree produced by KindHMLParser.

class KindHMLVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by KindHMLParser#program.
    def visitProgram(self, ctx:KindHMLParser.ProgramContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#contract.
    def visitContract(self, ctx:KindHMLParser.ContractContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#FieldDecl.
    def visitFieldDecl(self, ctx:KindHMLParser.FieldDeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#ConstructorDecl.
    def visitConstructorDecl(self, ctx:KindHMLParser.ConstructorDeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#FunctionDecl.
    def visitFunctionDecl(self, ctx:KindHMLParser.FunctionDeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#modifier.
    def visitModifier(self, ctx:KindHMLParser.ModifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#params.
    def visitParams(self, ctx:KindHMLParser.ParamsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#param.
    def visitParam(self, ctx:KindHMLParser.ParamContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#IntType.
    def visitIntType(self, ctx:KindHMLParser.IntTypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#UintType.
    def visitUintType(self, ctx:KindHMLParser.UintTypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#BoolType.
    def visitBoolType(self, ctx:KindHMLParser.BoolTypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#AddressType.
    def visitAddressType(self, ctx:KindHMLParser.AddressTypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#MappingType.
    def visitMappingType(self, ctx:KindHMLParser.MappingTypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#block.
    def visitBlock(self, ctx:KindHMLParser.BlockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#stmts.
    def visitStmts(self, ctx:KindHMLParser.StmtsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#SkipStmt.
    def visitSkipStmt(self, ctx:KindHMLParser.SkipStmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#RequireStmt.
    def visitRequireStmt(self, ctx:KindHMLParser.RequireStmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#IfStmt.
    def visitIfStmt(self, ctx:KindHMLParser.IfStmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#AssignStmt.
    def visitAssignStmt(self, ctx:KindHMLParser.AssignStmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#CallStmt.
    def visitCallStmt(self, ctx:KindHMLParser.CallStmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#BlockStmt.
    def visitBlockStmt(self, ctx:KindHMLParser.BlockStmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#ParenStmt.
    def visitParenStmt(self, ctx:KindHMLParser.ParenStmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#stmtBody.
    def visitStmtBody(self, ctx:KindHMLParser.StmtBodyContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#rule_.
    def visitRule_(self, ctx:KindHMLParser.Rule_Context):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#qtype.
    def visitQtype(self, ctx:KindHMLParser.QtypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#qvars.
    def visitQvars(self, ctx:KindHMLParser.QvarsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#MulExpr.
    def visitMulExpr(self, ctx:KindHMLParser.MulExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#AndExpr.
    def visitAndExpr(self, ctx:KindHMLParser.AndExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#NullLit.
    def visitNullLit(self, ctx:KindHMLParser.NullLitContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#ModalExpr.
    def visitModalExpr(self, ctx:KindHMLParser.ModalExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#PayableExpr.
    def visitPayableExpr(self, ctx:KindHMLParser.PayableExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#ImpliesExpr.
    def visitImpliesExpr(self, ctx:KindHMLParser.ImpliesExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#NameExpr.
    def visitNameExpr(self, ctx:KindHMLParser.NameExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#AddExpr.
    def visitAddExpr(self, ctx:KindHMLParser.AddExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#UnaryExpr.
    def visitUnaryExpr(self, ctx:KindHMLParser.UnaryExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#OrExpr.
    def visitOrExpr(self, ctx:KindHMLParser.OrExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#IndexExpr.
    def visitIndexExpr(self, ctx:KindHMLParser.IndexExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#MemberExpr.
    def visitMemberExpr(self, ctx:KindHMLParser.MemberExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#CmpExpr.
    def visitCmpExpr(self, ctx:KindHMLParser.CmpExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#EqExpr.
    def visitEqExpr(self, ctx:KindHMLParser.EqExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#FunCallExpr.
    def visitFunCallExpr(self, ctx:KindHMLParser.FunCallExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#ParenExpr.
    def visitParenExpr(self, ctx:KindHMLParser.ParenExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#IntLit.
    def visitIntLit(self, ctx:KindHMLParser.IntLitContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#QuantExpr.
    def visitQuantExpr(self, ctx:KindHMLParser.QuantExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#BoolLit.
    def visitBoolLit(self, ctx:KindHMLParser.BoolLitContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by KindHMLParser#exprs.
    def visitExprs(self, ctx:KindHMLParser.ExprsContext):
        return self.visitChildren(ctx)



del KindHMLParser