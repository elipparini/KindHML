# Generated from KindHML.g4 by ANTLR 4.13.2
# encoding: utf-8
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
	from typing import TextIO
else:
	from typing.io import TextIO

def serializedATN():
    return [
        4,1,65,309,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
        6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,2,13,7,13,
        2,14,7,14,2,15,7,15,2,16,7,16,1,0,5,0,36,8,0,10,0,12,0,39,9,0,1,
        0,4,0,42,8,0,11,0,12,0,43,1,0,5,0,47,8,0,10,0,12,0,50,9,0,1,0,1,
        0,1,1,1,1,1,1,1,1,3,1,58,8,1,1,2,1,2,1,2,1,2,5,2,64,8,2,10,2,12,
        2,67,9,2,1,2,1,2,1,3,1,3,1,3,3,3,74,8,3,1,3,1,3,1,3,3,3,79,8,3,1,
        3,1,3,5,3,83,8,3,10,3,12,3,86,9,3,1,3,1,3,1,3,1,3,1,3,3,3,93,8,3,
        1,3,1,3,5,3,97,8,3,10,3,12,3,100,9,3,1,3,3,3,103,8,3,1,4,1,4,1,5,
        1,5,1,5,5,5,110,8,5,10,5,12,5,113,9,5,1,6,1,6,1,6,1,7,1,7,1,7,1,
        7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,3,7,130,8,7,1,8,1,8,3,8,134,8,
        8,1,8,1,8,1,9,1,9,1,9,5,9,141,8,9,10,9,12,9,144,9,9,1,9,3,9,147,
        8,9,1,10,1,10,1,10,1,10,1,10,1,10,1,10,1,10,1,10,1,10,1,10,1,10,
        1,10,3,10,162,8,10,1,10,1,10,1,10,1,10,1,10,3,10,169,8,10,1,10,1,
        10,1,10,1,10,1,10,1,10,1,10,3,10,178,8,10,1,10,1,10,1,10,3,10,183,
        8,10,1,10,1,10,1,10,1,10,1,10,3,10,190,8,10,1,11,1,11,3,11,194,8,
        11,1,12,1,12,1,12,1,12,1,12,1,12,1,13,1,13,1,14,1,14,1,14,5,14,207,
        8,14,10,14,12,14,210,9,14,1,14,1,14,1,14,1,15,1,15,1,15,1,15,1,15,
        1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,3,15,
        232,8,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,
        1,15,1,15,1,15,1,15,1,15,1,15,3,15,251,8,15,1,15,1,15,1,15,3,15,
        256,8,15,1,15,1,15,3,15,260,8,15,1,15,1,15,1,15,3,15,265,8,15,1,
        15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,
        15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,15,1,
        15,1,15,1,15,5,15,296,8,15,10,15,12,15,299,9,15,1,16,1,16,1,16,5,
        16,304,8,16,10,16,12,16,307,9,16,1,16,0,1,30,17,0,2,4,6,8,10,12,
        14,16,18,20,22,24,26,28,30,32,0,13,1,0,10,12,1,0,27,29,2,0,14,18,
        62,62,1,0,34,35,1,0,37,38,1,0,55,56,1,0,39,41,2,0,38,38,42,42,1,
        0,43,46,1,0,47,48,1,0,49,50,1,0,51,52,1,0,53,54,348,0,37,1,0,0,0,
        2,53,1,0,0,0,4,59,1,0,0,0,6,102,1,0,0,0,8,104,1,0,0,0,10,106,1,0,
        0,0,12,114,1,0,0,0,14,129,1,0,0,0,16,131,1,0,0,0,18,137,1,0,0,0,
        20,189,1,0,0,0,22,193,1,0,0,0,24,195,1,0,0,0,26,201,1,0,0,0,28,203,
        1,0,0,0,30,264,1,0,0,0,32,300,1,0,0,0,34,36,3,2,1,0,35,34,1,0,0,
        0,36,39,1,0,0,0,37,35,1,0,0,0,37,38,1,0,0,0,38,41,1,0,0,0,39,37,
        1,0,0,0,40,42,3,4,2,0,41,40,1,0,0,0,42,43,1,0,0,0,43,41,1,0,0,0,
        43,44,1,0,0,0,44,48,1,0,0,0,45,47,3,24,12,0,46,45,1,0,0,0,47,50,
        1,0,0,0,48,46,1,0,0,0,48,49,1,0,0,0,49,51,1,0,0,0,50,48,1,0,0,0,
        51,52,5,0,0,1,52,1,1,0,0,0,53,54,5,1,0,0,54,55,5,62,0,0,55,57,3,
        14,7,0,56,58,5,2,0,0,57,56,1,0,0,0,57,58,1,0,0,0,58,3,1,0,0,0,59,
        60,5,3,0,0,60,61,5,62,0,0,61,65,5,4,0,0,62,64,3,6,3,0,63,62,1,0,
        0,0,64,67,1,0,0,0,65,63,1,0,0,0,65,66,1,0,0,0,66,68,1,0,0,0,67,65,
        1,0,0,0,68,69,5,5,0,0,69,5,1,0,0,0,70,71,3,14,7,0,71,73,5,62,0,0,
        72,74,5,2,0,0,73,72,1,0,0,0,73,74,1,0,0,0,74,103,1,0,0,0,75,76,5,
        6,0,0,76,78,5,7,0,0,77,79,3,10,5,0,78,77,1,0,0,0,78,79,1,0,0,0,79,
        80,1,0,0,0,80,84,5,8,0,0,81,83,3,8,4,0,82,81,1,0,0,0,83,86,1,0,0,
        0,84,82,1,0,0,0,84,85,1,0,0,0,85,87,1,0,0,0,86,84,1,0,0,0,87,103,
        3,16,8,0,88,89,5,9,0,0,89,90,5,62,0,0,90,92,5,7,0,0,91,93,3,10,5,
        0,92,91,1,0,0,0,92,93,1,0,0,0,93,94,1,0,0,0,94,98,5,8,0,0,95,97,
        3,8,4,0,96,95,1,0,0,0,97,100,1,0,0,0,98,96,1,0,0,0,98,99,1,0,0,0,
        99,101,1,0,0,0,100,98,1,0,0,0,101,103,3,16,8,0,102,70,1,0,0,0,102,
        75,1,0,0,0,102,88,1,0,0,0,103,7,1,0,0,0,104,105,7,0,0,0,105,9,1,
        0,0,0,106,111,3,12,6,0,107,108,5,13,0,0,108,110,3,12,6,0,109,107,
        1,0,0,0,110,113,1,0,0,0,111,109,1,0,0,0,111,112,1,0,0,0,112,11,1,
        0,0,0,113,111,1,0,0,0,114,115,3,14,7,0,115,116,5,62,0,0,116,13,1,
        0,0,0,117,130,5,14,0,0,118,130,5,15,0,0,119,130,5,16,0,0,120,130,
        5,17,0,0,121,130,5,18,0,0,122,123,5,19,0,0,123,124,5,7,0,0,124,125,
        5,18,0,0,125,126,5,20,0,0,126,127,3,14,7,0,127,128,5,8,0,0,128,130,
        1,0,0,0,129,117,1,0,0,0,129,118,1,0,0,0,129,119,1,0,0,0,129,120,
        1,0,0,0,129,121,1,0,0,0,129,122,1,0,0,0,130,15,1,0,0,0,131,133,5,
        4,0,0,132,134,3,18,9,0,133,132,1,0,0,0,133,134,1,0,0,0,134,135,1,
        0,0,0,135,136,5,5,0,0,136,17,1,0,0,0,137,142,3,20,10,0,138,139,5,
        2,0,0,139,141,3,20,10,0,140,138,1,0,0,0,141,144,1,0,0,0,142,140,
        1,0,0,0,142,143,1,0,0,0,143,146,1,0,0,0,144,142,1,0,0,0,145,147,
        5,2,0,0,146,145,1,0,0,0,146,147,1,0,0,0,147,19,1,0,0,0,148,190,5,
        21,0,0,149,150,5,22,0,0,150,151,5,7,0,0,151,152,3,30,15,0,152,153,
        5,8,0,0,153,190,1,0,0,0,154,155,5,23,0,0,155,156,5,7,0,0,156,157,
        3,30,15,0,157,158,5,8,0,0,158,161,3,22,11,0,159,160,5,24,0,0,160,
        162,3,22,11,0,161,159,1,0,0,0,161,162,1,0,0,0,162,190,1,0,0,0,163,
        168,5,62,0,0,164,165,5,25,0,0,165,166,3,30,15,0,166,167,5,26,0,0,
        167,169,1,0,0,0,168,164,1,0,0,0,168,169,1,0,0,0,169,170,1,0,0,0,
        170,171,7,1,0,0,171,190,3,30,15,0,172,173,3,30,15,0,173,174,5,30,
        0,0,174,175,5,62,0,0,175,177,5,7,0,0,176,178,3,32,16,0,177,176,1,
        0,0,0,177,178,1,0,0,0,178,179,1,0,0,0,179,182,5,8,0,0,180,181,5,
        31,0,0,181,183,3,30,15,0,182,180,1,0,0,0,182,183,1,0,0,0,183,190,
        1,0,0,0,184,190,3,16,8,0,185,186,5,7,0,0,186,187,3,18,9,0,187,188,
        5,8,0,0,188,190,1,0,0,0,189,148,1,0,0,0,189,149,1,0,0,0,189,154,
        1,0,0,0,189,163,1,0,0,0,189,172,1,0,0,0,189,184,1,0,0,0,189,185,
        1,0,0,0,190,21,1,0,0,0,191,194,3,16,8,0,192,194,3,20,10,0,193,191,
        1,0,0,0,193,192,1,0,0,0,194,23,1,0,0,0,195,196,5,32,0,0,196,197,
        5,62,0,0,197,198,5,4,0,0,198,199,3,30,15,0,199,200,5,5,0,0,200,25,
        1,0,0,0,201,202,7,2,0,0,202,27,1,0,0,0,203,208,5,62,0,0,204,205,
        5,13,0,0,205,207,5,62,0,0,206,204,1,0,0,0,207,210,1,0,0,0,208,206,
        1,0,0,0,208,209,1,0,0,0,209,211,1,0,0,0,210,208,1,0,0,0,211,212,
        5,33,0,0,212,213,3,26,13,0,213,29,1,0,0,0,214,215,6,15,-1,0,215,
        216,5,7,0,0,216,217,3,30,15,0,217,218,5,8,0,0,218,265,1,0,0,0,219,
        265,5,61,0,0,220,265,5,60,0,0,221,265,7,3,0,0,222,265,5,36,0,0,223,
        224,5,10,0,0,224,225,5,7,0,0,225,226,3,30,15,0,226,227,5,8,0,0,227,
        265,1,0,0,0,228,229,5,62,0,0,229,231,5,7,0,0,230,232,3,32,16,0,231,
        230,1,0,0,0,231,232,1,0,0,0,232,233,1,0,0,0,233,265,5,8,0,0,234,
        265,5,62,0,0,235,236,7,4,0,0,236,265,3,30,15,10,237,238,7,5,0,0,
        238,239,3,28,14,0,239,240,5,30,0,0,240,241,3,30,15,2,241,265,1,0,
        0,0,242,243,5,57,0,0,243,244,3,30,15,0,244,245,5,33,0,0,245,246,
        5,62,0,0,246,247,5,30,0,0,247,248,5,62,0,0,248,250,5,7,0,0,249,251,
        3,32,16,0,250,249,1,0,0,0,250,251,1,0,0,0,251,252,1,0,0,0,252,255,
        5,8,0,0,253,254,5,31,0,0,254,256,3,30,15,0,255,253,1,0,0,0,255,256,
        1,0,0,0,256,259,1,0,0,0,257,258,5,58,0,0,258,260,3,30,15,0,259,257,
        1,0,0,0,259,260,1,0,0,0,260,261,1,0,0,0,261,262,5,59,0,0,262,263,
        3,30,15,1,263,265,1,0,0,0,264,214,1,0,0,0,264,219,1,0,0,0,264,220,
        1,0,0,0,264,221,1,0,0,0,264,222,1,0,0,0,264,223,1,0,0,0,264,228,
        1,0,0,0,264,234,1,0,0,0,264,235,1,0,0,0,264,237,1,0,0,0,264,242,
        1,0,0,0,265,297,1,0,0,0,266,267,10,9,0,0,267,268,7,6,0,0,268,296,
        3,30,15,10,269,270,10,8,0,0,270,271,7,7,0,0,271,296,3,30,15,9,272,
        273,10,7,0,0,273,274,7,8,0,0,274,296,3,30,15,8,275,276,10,6,0,0,
        276,277,7,9,0,0,277,296,3,30,15,7,278,279,10,5,0,0,279,280,7,10,
        0,0,280,296,3,30,15,6,281,282,10,4,0,0,282,283,7,11,0,0,283,296,
        3,30,15,5,284,285,10,3,0,0,285,286,7,12,0,0,286,296,3,30,15,3,287,
        288,10,12,0,0,288,289,5,30,0,0,289,296,5,62,0,0,290,291,10,11,0,
        0,291,292,5,25,0,0,292,293,3,30,15,0,293,294,5,26,0,0,294,296,1,
        0,0,0,295,266,1,0,0,0,295,269,1,0,0,0,295,272,1,0,0,0,295,275,1,
        0,0,0,295,278,1,0,0,0,295,281,1,0,0,0,295,284,1,0,0,0,295,287,1,
        0,0,0,295,290,1,0,0,0,296,299,1,0,0,0,297,295,1,0,0,0,297,298,1,
        0,0,0,298,31,1,0,0,0,299,297,1,0,0,0,300,305,3,30,15,0,301,302,5,
        13,0,0,302,304,3,30,15,0,303,301,1,0,0,0,304,307,1,0,0,0,305,303,
        1,0,0,0,305,306,1,0,0,0,306,33,1,0,0,0,307,305,1,0,0,0,31,37,43,
        48,57,65,73,78,84,92,98,102,111,129,133,142,146,161,168,177,182,
        189,193,208,231,250,255,259,264,295,297,305
    ]

class KindHMLParser ( Parser ):

    grammarFileName = "KindHML.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'pragma'", "';'", "'contract'", "'{'", 
                     "'}'", "'constructor'", "'('", "')'", "'function'", 
                     "'payable'", "'public'", "'external'", "','", "'int'", 
                     "'uint'", "'real'", "'bool'", "'address'", "'mapping'", 
                     "'=>'", "'skip'", "'require'", "'if'", "'else'", "'['", 
                     "']'", "'='", "'+='", "'-='", "'.'", "'$'", "'rule'", 
                     "':'", "'true'", "'false'", "'null'", "'!'", "'-'", 
                     "'*'", "'/'", "'%'", "'+'", "'<'", "'<='", "'>'", "'>='", 
                     "'=='", "'!='", "'&&'", "'and'", "'||'", "'or'", "'->'", 
                     "'implies'", "'forall'", "'exists'", "'<<'", "'@'", 
                     "'>>'" ]

    symbolicNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "REAL", "INT", "ID", "LINE_COMMENT", "BLOCK_COMMENT", 
                      "WS" ]

    RULE_program = 0
    RULE_pragma = 1
    RULE_contract = 2
    RULE_member = 3
    RULE_modifier = 4
    RULE_params = 5
    RULE_param = 6
    RULE_type_ = 7
    RULE_block = 8
    RULE_stmts = 9
    RULE_stmt = 10
    RULE_stmtBody = 11
    RULE_rule_ = 12
    RULE_qtype = 13
    RULE_qvars = 14
    RULE_expr = 15
    RULE_exprs = 16

    ruleNames =  [ "program", "pragma", "contract", "member", "modifier", 
                   "params", "param", "type_", "block", "stmts", "stmt", 
                   "stmtBody", "rule_", "qtype", "qvars", "expr", "exprs" ]

    EOF = Token.EOF
    T__0=1
    T__1=2
    T__2=3
    T__3=4
    T__4=5
    T__5=6
    T__6=7
    T__7=8
    T__8=9
    T__9=10
    T__10=11
    T__11=12
    T__12=13
    T__13=14
    T__14=15
    T__15=16
    T__16=17
    T__17=18
    T__18=19
    T__19=20
    T__20=21
    T__21=22
    T__22=23
    T__23=24
    T__24=25
    T__25=26
    T__26=27
    T__27=28
    T__28=29
    T__29=30
    T__30=31
    T__31=32
    T__32=33
    T__33=34
    T__34=35
    T__35=36
    T__36=37
    T__37=38
    T__38=39
    T__39=40
    T__40=41
    T__41=42
    T__42=43
    T__43=44
    T__44=45
    T__45=46
    T__46=47
    T__47=48
    T__48=49
    T__49=50
    T__50=51
    T__51=52
    T__52=53
    T__53=54
    T__54=55
    T__55=56
    T__56=57
    T__57=58
    T__58=59
    REAL=60
    INT=61
    ID=62
    LINE_COMMENT=63
    BLOCK_COMMENT=64
    WS=65

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.2")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class ProgramContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def EOF(self):
            return self.getToken(KindHMLParser.EOF, 0)

        def pragma(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.PragmaContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.PragmaContext,i)


        def contract(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ContractContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ContractContext,i)


        def rule_(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.Rule_Context)
            else:
                return self.getTypedRuleContext(KindHMLParser.Rule_Context,i)


        def getRuleIndex(self):
            return KindHMLParser.RULE_program

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitProgram" ):
                return visitor.visitProgram(self)
            else:
                return visitor.visitChildren(self)




    def program(self):

        localctx = KindHMLParser.ProgramContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_program)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 37
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==1:
                self.state = 34
                self.pragma()
                self.state = 39
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 41 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 40
                self.contract()
                self.state = 43 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==3):
                    break

            self.state = 48
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==32:
                self.state = 45
                self.rule_()
                self.state = 50
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 51
            self.match(KindHMLParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class PragmaContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser
            self.key = None # Token

        def type_(self):
            return self.getTypedRuleContext(KindHMLParser.Type_Context,0)


        def ID(self):
            return self.getToken(KindHMLParser.ID, 0)

        def getRuleIndex(self):
            return KindHMLParser.RULE_pragma

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitPragma" ):
                return visitor.visitPragma(self)
            else:
                return visitor.visitChildren(self)




    def pragma(self):

        localctx = KindHMLParser.PragmaContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_pragma)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 53
            self.match(KindHMLParser.T__0)
            self.state = 54
            localctx.key = self.match(KindHMLParser.ID)
            self.state = 55
            self.type_()
            self.state = 57
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==2:
                self.state = 56
                self.match(KindHMLParser.T__1)


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ContractContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser
            self.name = None # Token

        def ID(self):
            return self.getToken(KindHMLParser.ID, 0)

        def member(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.MemberContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.MemberContext,i)


        def getRuleIndex(self):
            return KindHMLParser.RULE_contract

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitContract" ):
                return visitor.visitContract(self)
            else:
                return visitor.visitChildren(self)




    def contract(self):

        localctx = KindHMLParser.ContractContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_contract)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 59
            self.match(KindHMLParser.T__2)
            self.state = 60
            localctx.name = self.match(KindHMLParser.ID)
            self.state = 61
            self.match(KindHMLParser.T__3)
            self.state = 65
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while (((_la) & ~0x3f) == 0 and ((1 << _la) & 1032768) != 0):
                self.state = 62
                self.member()
                self.state = 67
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 68
            self.match(KindHMLParser.T__4)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class MemberContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return KindHMLParser.RULE_member

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)



    class FieldDeclContext(MemberContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.MemberContext
            super().__init__(parser)
            self.name = None # Token
            self.copyFrom(ctx)

        def type_(self):
            return self.getTypedRuleContext(KindHMLParser.Type_Context,0)

        def ID(self):
            return self.getToken(KindHMLParser.ID, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitFieldDecl" ):
                return visitor.visitFieldDecl(self)
            else:
                return visitor.visitChildren(self)


    class ConstructorDeclContext(MemberContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.MemberContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def block(self):
            return self.getTypedRuleContext(KindHMLParser.BlockContext,0)

        def params(self):
            return self.getTypedRuleContext(KindHMLParser.ParamsContext,0)

        def modifier(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ModifierContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ModifierContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitConstructorDecl" ):
                return visitor.visitConstructorDecl(self)
            else:
                return visitor.visitChildren(self)


    class FunctionDeclContext(MemberContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.MemberContext
            super().__init__(parser)
            self.name = None # Token
            self.copyFrom(ctx)

        def block(self):
            return self.getTypedRuleContext(KindHMLParser.BlockContext,0)

        def ID(self):
            return self.getToken(KindHMLParser.ID, 0)
        def params(self):
            return self.getTypedRuleContext(KindHMLParser.ParamsContext,0)

        def modifier(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ModifierContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ModifierContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitFunctionDecl" ):
                return visitor.visitFunctionDecl(self)
            else:
                return visitor.visitChildren(self)



    def member(self):

        localctx = KindHMLParser.MemberContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_member)
        self._la = 0 # Token type
        try:
            self.state = 102
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [14, 15, 16, 17, 18, 19]:
                localctx = KindHMLParser.FieldDeclContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 70
                self.type_()
                self.state = 71
                localctx.name = self.match(KindHMLParser.ID)
                self.state = 73
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==2:
                    self.state = 72
                    self.match(KindHMLParser.T__1)


                pass
            elif token in [6]:
                localctx = KindHMLParser.ConstructorDeclContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 75
                self.match(KindHMLParser.T__5)
                self.state = 76
                self.match(KindHMLParser.T__6)
                self.state = 78
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if (((_la) & ~0x3f) == 0 and ((1 << _la) & 1032192) != 0):
                    self.state = 77
                    self.params()


                self.state = 80
                self.match(KindHMLParser.T__7)
                self.state = 84
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                while (((_la) & ~0x3f) == 0 and ((1 << _la) & 7168) != 0):
                    self.state = 81
                    self.modifier()
                    self.state = 86
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)

                self.state = 87
                self.block()
                pass
            elif token in [9]:
                localctx = KindHMLParser.FunctionDeclContext(self, localctx)
                self.enterOuterAlt(localctx, 3)
                self.state = 88
                self.match(KindHMLParser.T__8)
                self.state = 89
                localctx.name = self.match(KindHMLParser.ID)
                self.state = 90
                self.match(KindHMLParser.T__6)
                self.state = 92
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if (((_la) & ~0x3f) == 0 and ((1 << _la) & 1032192) != 0):
                    self.state = 91
                    self.params()


                self.state = 94
                self.match(KindHMLParser.T__7)
                self.state = 98
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                while (((_la) & ~0x3f) == 0 and ((1 << _la) & 7168) != 0):
                    self.state = 95
                    self.modifier()
                    self.state = 100
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)

                self.state = 101
                self.block()
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ModifierContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return KindHMLParser.RULE_modifier

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitModifier" ):
                return visitor.visitModifier(self)
            else:
                return visitor.visitChildren(self)




    def modifier(self):

        localctx = KindHMLParser.ModifierContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_modifier)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 104
            _la = self._input.LA(1)
            if not((((_la) & ~0x3f) == 0 and ((1 << _la) & 7168) != 0)):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ParamsContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def param(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ParamContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ParamContext,i)


        def getRuleIndex(self):
            return KindHMLParser.RULE_params

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitParams" ):
                return visitor.visitParams(self)
            else:
                return visitor.visitChildren(self)




    def params(self):

        localctx = KindHMLParser.ParamsContext(self, self._ctx, self.state)
        self.enterRule(localctx, 10, self.RULE_params)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 106
            self.param()
            self.state = 111
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==13:
                self.state = 107
                self.match(KindHMLParser.T__12)
                self.state = 108
                self.param()
                self.state = 113
                self._errHandler.sync(self)
                _la = self._input.LA(1)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ParamContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser
            self.name = None # Token

        def type_(self):
            return self.getTypedRuleContext(KindHMLParser.Type_Context,0)


        def ID(self):
            return self.getToken(KindHMLParser.ID, 0)

        def getRuleIndex(self):
            return KindHMLParser.RULE_param

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitParam" ):
                return visitor.visitParam(self)
            else:
                return visitor.visitChildren(self)




    def param(self):

        localctx = KindHMLParser.ParamContext(self, self._ctx, self.state)
        self.enterRule(localctx, 12, self.RULE_param)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 114
            self.type_()
            self.state = 115
            localctx.name = self.match(KindHMLParser.ID)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Type_Context(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return KindHMLParser.RULE_type_

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)



    class MappingTypeContext(Type_Context):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.Type_Context
            super().__init__(parser)
            self.copyFrom(ctx)

        def type_(self):
            return self.getTypedRuleContext(KindHMLParser.Type_Context,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitMappingType" ):
                return visitor.visitMappingType(self)
            else:
                return visitor.visitChildren(self)


    class BoolTypeContext(Type_Context):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.Type_Context
            super().__init__(parser)
            self.copyFrom(ctx)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitBoolType" ):
                return visitor.visitBoolType(self)
            else:
                return visitor.visitChildren(self)


    class UintTypeContext(Type_Context):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.Type_Context
            super().__init__(parser)
            self.copyFrom(ctx)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitUintType" ):
                return visitor.visitUintType(self)
            else:
                return visitor.visitChildren(self)


    class AddressTypeContext(Type_Context):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.Type_Context
            super().__init__(parser)
            self.copyFrom(ctx)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitAddressType" ):
                return visitor.visitAddressType(self)
            else:
                return visitor.visitChildren(self)


    class RealTypeContext(Type_Context):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.Type_Context
            super().__init__(parser)
            self.copyFrom(ctx)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitRealType" ):
                return visitor.visitRealType(self)
            else:
                return visitor.visitChildren(self)


    class IntTypeContext(Type_Context):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.Type_Context
            super().__init__(parser)
            self.copyFrom(ctx)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitIntType" ):
                return visitor.visitIntType(self)
            else:
                return visitor.visitChildren(self)



    def type_(self):

        localctx = KindHMLParser.Type_Context(self, self._ctx, self.state)
        self.enterRule(localctx, 14, self.RULE_type_)
        try:
            self.state = 129
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [14]:
                localctx = KindHMLParser.IntTypeContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 117
                self.match(KindHMLParser.T__13)
                pass
            elif token in [15]:
                localctx = KindHMLParser.UintTypeContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 118
                self.match(KindHMLParser.T__14)
                pass
            elif token in [16]:
                localctx = KindHMLParser.RealTypeContext(self, localctx)
                self.enterOuterAlt(localctx, 3)
                self.state = 119
                self.match(KindHMLParser.T__15)
                pass
            elif token in [17]:
                localctx = KindHMLParser.BoolTypeContext(self, localctx)
                self.enterOuterAlt(localctx, 4)
                self.state = 120
                self.match(KindHMLParser.T__16)
                pass
            elif token in [18]:
                localctx = KindHMLParser.AddressTypeContext(self, localctx)
                self.enterOuterAlt(localctx, 5)
                self.state = 121
                self.match(KindHMLParser.T__17)
                pass
            elif token in [19]:
                localctx = KindHMLParser.MappingTypeContext(self, localctx)
                self.enterOuterAlt(localctx, 6)
                self.state = 122
                self.match(KindHMLParser.T__18)
                self.state = 123
                self.match(KindHMLParser.T__6)
                self.state = 124
                self.match(KindHMLParser.T__17)
                self.state = 125
                self.match(KindHMLParser.T__19)
                self.state = 126
                self.type_()
                self.state = 127
                self.match(KindHMLParser.T__7)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class BlockContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def stmts(self):
            return self.getTypedRuleContext(KindHMLParser.StmtsContext,0)


        def getRuleIndex(self):
            return KindHMLParser.RULE_block

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitBlock" ):
                return visitor.visitBlock(self)
            else:
                return visitor.visitChildren(self)




    def block(self):

        localctx = KindHMLParser.BlockContext(self, self._ctx, self.state)
        self.enterRule(localctx, 16, self.RULE_block)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 131
            self.match(KindHMLParser.T__3)
            self.state = 133
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if (((_la) & ~0x3f) == 0 and ((1 << _la) & 8322652643971302544) != 0):
                self.state = 132
                self.stmts()


            self.state = 135
            self.match(KindHMLParser.T__4)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class StmtsContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def stmt(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.StmtContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.StmtContext,i)


        def getRuleIndex(self):
            return KindHMLParser.RULE_stmts

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitStmts" ):
                return visitor.visitStmts(self)
            else:
                return visitor.visitChildren(self)




    def stmts(self):

        localctx = KindHMLParser.StmtsContext(self, self._ctx, self.state)
        self.enterRule(localctx, 18, self.RULE_stmts)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 137
            self.stmt()
            self.state = 142
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,14,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    self.state = 138
                    self.match(KindHMLParser.T__1)
                    self.state = 139
                    self.stmt() 
                self.state = 144
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,14,self._ctx)

            self.state = 146
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==2:
                self.state = 145
                self.match(KindHMLParser.T__1)


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class StmtContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return KindHMLParser.RULE_stmt

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)



    class IfStmtContext(StmtContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.StmtContext
            super().__init__(parser)
            self.body = None # StmtBodyContext
            self.orelse = None # StmtBodyContext
            self.copyFrom(ctx)

        def expr(self):
            return self.getTypedRuleContext(KindHMLParser.ExprContext,0)

        def stmtBody(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.StmtBodyContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.StmtBodyContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitIfStmt" ):
                return visitor.visitIfStmt(self)
            else:
                return visitor.visitChildren(self)


    class AssignStmtContext(StmtContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.StmtContext
            super().__init__(parser)
            self.target = None # Token
            self.key = None # ExprContext
            self.op = None # Token
            self.value = None # ExprContext
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(KindHMLParser.ID, 0)
        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ExprContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ExprContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitAssignStmt" ):
                return visitor.visitAssignStmt(self)
            else:
                return visitor.visitChildren(self)


    class BlockStmtContext(StmtContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.StmtContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def block(self):
            return self.getTypedRuleContext(KindHMLParser.BlockContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitBlockStmt" ):
                return visitor.visitBlockStmt(self)
            else:
                return visitor.visitChildren(self)


    class ParenStmtContext(StmtContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.StmtContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def stmts(self):
            return self.getTypedRuleContext(KindHMLParser.StmtsContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitParenStmt" ):
                return visitor.visitParenStmt(self)
            else:
                return visitor.visitChildren(self)


    class CallStmtContext(StmtContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.StmtContext
            super().__init__(parser)
            self.obj = None # ExprContext
            self.method = None # Token
            self.value = None # ExprContext
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ExprContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ExprContext,i)

        def ID(self):
            return self.getToken(KindHMLParser.ID, 0)
        def exprs(self):
            return self.getTypedRuleContext(KindHMLParser.ExprsContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitCallStmt" ):
                return visitor.visitCallStmt(self)
            else:
                return visitor.visitChildren(self)


    class RequireStmtContext(StmtContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.StmtContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self):
            return self.getTypedRuleContext(KindHMLParser.ExprContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitRequireStmt" ):
                return visitor.visitRequireStmt(self)
            else:
                return visitor.visitChildren(self)


    class SkipStmtContext(StmtContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.StmtContext
            super().__init__(parser)
            self.copyFrom(ctx)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitSkipStmt" ):
                return visitor.visitSkipStmt(self)
            else:
                return visitor.visitChildren(self)



    def stmt(self):

        localctx = KindHMLParser.StmtContext(self, self._ctx, self.state)
        self.enterRule(localctx, 20, self.RULE_stmt)
        self._la = 0 # Token type
        try:
            self.state = 189
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,20,self._ctx)
            if la_ == 1:
                localctx = KindHMLParser.SkipStmtContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 148
                self.match(KindHMLParser.T__20)
                pass

            elif la_ == 2:
                localctx = KindHMLParser.RequireStmtContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 149
                self.match(KindHMLParser.T__21)
                self.state = 150
                self.match(KindHMLParser.T__6)
                self.state = 151
                self.expr(0)
                self.state = 152
                self.match(KindHMLParser.T__7)
                pass

            elif la_ == 3:
                localctx = KindHMLParser.IfStmtContext(self, localctx)
                self.enterOuterAlt(localctx, 3)
                self.state = 154
                self.match(KindHMLParser.T__22)
                self.state = 155
                self.match(KindHMLParser.T__6)
                self.state = 156
                self.expr(0)
                self.state = 157
                self.match(KindHMLParser.T__7)
                self.state = 158
                localctx.body = self.stmtBody()
                self.state = 161
                self._errHandler.sync(self)
                la_ = self._interp.adaptivePredict(self._input,16,self._ctx)
                if la_ == 1:
                    self.state = 159
                    self.match(KindHMLParser.T__23)
                    self.state = 160
                    localctx.orelse = self.stmtBody()


                pass

            elif la_ == 4:
                localctx = KindHMLParser.AssignStmtContext(self, localctx)
                self.enterOuterAlt(localctx, 4)
                self.state = 163
                localctx.target = self.match(KindHMLParser.ID)
                self.state = 168
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==25:
                    self.state = 164
                    self.match(KindHMLParser.T__24)
                    self.state = 165
                    localctx.key = self.expr(0)
                    self.state = 166
                    self.match(KindHMLParser.T__25)


                self.state = 170
                localctx.op = self._input.LT(1)
                _la = self._input.LA(1)
                if not((((_la) & ~0x3f) == 0 and ((1 << _la) & 939524096) != 0)):
                    localctx.op = self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 171
                localctx.value = self.expr(0)
                pass

            elif la_ == 5:
                localctx = KindHMLParser.CallStmtContext(self, localctx)
                self.enterOuterAlt(localctx, 5)
                self.state = 172
                localctx.obj = self.expr(0)
                self.state = 173
                self.match(KindHMLParser.T__29)
                self.state = 174
                localctx.method = self.match(KindHMLParser.ID)
                self.state = 175
                self.match(KindHMLParser.T__6)
                self.state = 177
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if (((_la) & ~0x3f) == 0 and ((1 << _la) & 8322652643956622464) != 0):
                    self.state = 176
                    self.exprs()


                self.state = 179
                self.match(KindHMLParser.T__7)
                self.state = 182
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==31:
                    self.state = 180
                    self.match(KindHMLParser.T__30)
                    self.state = 181
                    localctx.value = self.expr(0)


                pass

            elif la_ == 6:
                localctx = KindHMLParser.BlockStmtContext(self, localctx)
                self.enterOuterAlt(localctx, 6)
                self.state = 184
                self.block()
                pass

            elif la_ == 7:
                localctx = KindHMLParser.ParenStmtContext(self, localctx)
                self.enterOuterAlt(localctx, 7)
                self.state = 185
                self.match(KindHMLParser.T__6)
                self.state = 186
                self.stmts()
                self.state = 187
                self.match(KindHMLParser.T__7)
                pass


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class StmtBodyContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def block(self):
            return self.getTypedRuleContext(KindHMLParser.BlockContext,0)


        def stmt(self):
            return self.getTypedRuleContext(KindHMLParser.StmtContext,0)


        def getRuleIndex(self):
            return KindHMLParser.RULE_stmtBody

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitStmtBody" ):
                return visitor.visitStmtBody(self)
            else:
                return visitor.visitChildren(self)




    def stmtBody(self):

        localctx = KindHMLParser.StmtBodyContext(self, self._ctx, self.state)
        self.enterRule(localctx, 22, self.RULE_stmtBody)
        try:
            self.state = 193
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,21,self._ctx)
            if la_ == 1:
                self.enterOuterAlt(localctx, 1)
                self.state = 191
                self.block()
                pass

            elif la_ == 2:
                self.enterOuterAlt(localctx, 2)
                self.state = 192
                self.stmt()
                pass


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Rule_Context(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser
            self.name = None # Token

        def expr(self):
            return self.getTypedRuleContext(KindHMLParser.ExprContext,0)


        def ID(self):
            return self.getToken(KindHMLParser.ID, 0)

        def getRuleIndex(self):
            return KindHMLParser.RULE_rule_

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitRule_" ):
                return visitor.visitRule_(self)
            else:
                return visitor.visitChildren(self)




    def rule_(self):

        localctx = KindHMLParser.Rule_Context(self, self._ctx, self.state)
        self.enterRule(localctx, 24, self.RULE_rule_)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 195
            self.match(KindHMLParser.T__31)
            self.state = 196
            localctx.name = self.match(KindHMLParser.ID)
            self.state = 197
            self.match(KindHMLParser.T__3)
            self.state = 198
            self.expr(0)
            self.state = 199
            self.match(KindHMLParser.T__4)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class QtypeContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self):
            return self.getToken(KindHMLParser.ID, 0)

        def getRuleIndex(self):
            return KindHMLParser.RULE_qtype

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitQtype" ):
                return visitor.visitQtype(self)
            else:
                return visitor.visitChildren(self)




    def qtype(self):

        localctx = KindHMLParser.QtypeContext(self, self._ctx, self.state)
        self.enterRule(localctx, 26, self.RULE_qtype)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 201
            _la = self._input.LA(1)
            if not((((_la) & ~0x3f) == 0 and ((1 << _la) & 4611686018427895808) != 0)):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class QvarsContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(KindHMLParser.ID)
            else:
                return self.getToken(KindHMLParser.ID, i)

        def qtype(self):
            return self.getTypedRuleContext(KindHMLParser.QtypeContext,0)


        def getRuleIndex(self):
            return KindHMLParser.RULE_qvars

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitQvars" ):
                return visitor.visitQvars(self)
            else:
                return visitor.visitChildren(self)




    def qvars(self):

        localctx = KindHMLParser.QvarsContext(self, self._ctx, self.state)
        self.enterRule(localctx, 28, self.RULE_qvars)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 203
            self.match(KindHMLParser.ID)
            self.state = 208
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==13:
                self.state = 204
                self.match(KindHMLParser.T__12)
                self.state = 205
                self.match(KindHMLParser.ID)
                self.state = 210
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 211
            self.match(KindHMLParser.T__32)
            self.state = 212
            self.qtype()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return KindHMLParser.RULE_expr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class MulExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ExprContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ExprContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitMulExpr" ):
                return visitor.visitMulExpr(self)
            else:
                return visitor.visitChildren(self)


    class AndExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ExprContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ExprContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitAndExpr" ):
                return visitor.visitAndExpr(self)
            else:
                return visitor.visitChildren(self)


    class NullLitContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitNullLit" ):
                return visitor.visitNullLit(self)
            else:
                return visitor.visitChildren(self)


    class ModalExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.sender = None # ExprContext
            self.contractName = None # Token
            self.proc = None # Token
            self.value = None # ExprContext
            self.blocks = None # ExprContext
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ExprContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ExprContext,i)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(KindHMLParser.ID)
            else:
                return self.getToken(KindHMLParser.ID, i)
        def exprs(self):
            return self.getTypedRuleContext(KindHMLParser.ExprsContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitModalExpr" ):
                return visitor.visitModalExpr(self)
            else:
                return visitor.visitChildren(self)


    class PayableExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self):
            return self.getTypedRuleContext(KindHMLParser.ExprContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitPayableExpr" ):
                return visitor.visitPayableExpr(self)
            else:
                return visitor.visitChildren(self)


    class ImpliesExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ExprContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ExprContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitImpliesExpr" ):
                return visitor.visitImpliesExpr(self)
            else:
                return visitor.visitChildren(self)


    class NameExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(KindHMLParser.ID, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitNameExpr" ):
                return visitor.visitNameExpr(self)
            else:
                return visitor.visitChildren(self)


    class AddExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ExprContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ExprContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitAddExpr" ):
                return visitor.visitAddExpr(self)
            else:
                return visitor.visitChildren(self)


    class UnaryExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def expr(self):
            return self.getTypedRuleContext(KindHMLParser.ExprContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitUnaryExpr" ):
                return visitor.visitUnaryExpr(self)
            else:
                return visitor.visitChildren(self)


    class OrExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ExprContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ExprContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitOrExpr" ):
                return visitor.visitOrExpr(self)
            else:
                return visitor.visitChildren(self)


    class IndexExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ExprContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ExprContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitIndexExpr" ):
                return visitor.visitIndexExpr(self)
            else:
                return visitor.visitChildren(self)


    class MemberExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self):
            return self.getTypedRuleContext(KindHMLParser.ExprContext,0)

        def ID(self):
            return self.getToken(KindHMLParser.ID, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitMemberExpr" ):
                return visitor.visitMemberExpr(self)
            else:
                return visitor.visitChildren(self)


    class CmpExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ExprContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ExprContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitCmpExpr" ):
                return visitor.visitCmpExpr(self)
            else:
                return visitor.visitChildren(self)


    class EqExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ExprContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ExprContext,i)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitEqExpr" ):
                return visitor.visitEqExpr(self)
            else:
                return visitor.visitChildren(self)


    class RealLitContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def REAL(self):
            return self.getToken(KindHMLParser.REAL, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitRealLit" ):
                return visitor.visitRealLit(self)
            else:
                return visitor.visitChildren(self)


    class FunCallExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.fn = None # Token
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(KindHMLParser.ID, 0)
        def exprs(self):
            return self.getTypedRuleContext(KindHMLParser.ExprsContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitFunCallExpr" ):
                return visitor.visitFunCallExpr(self)
            else:
                return visitor.visitChildren(self)


    class ParenExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self):
            return self.getTypedRuleContext(KindHMLParser.ExprContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitParenExpr" ):
                return visitor.visitParenExpr(self)
            else:
                return visitor.visitChildren(self)


    class IntLitContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def INT(self):
            return self.getToken(KindHMLParser.INT, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitIntLit" ):
                return visitor.visitIntLit(self)
            else:
                return visitor.visitChildren(self)


    class QuantExprContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.q = None # Token
            self.copyFrom(ctx)

        def qvars(self):
            return self.getTypedRuleContext(KindHMLParser.QvarsContext,0)

        def expr(self):
            return self.getTypedRuleContext(KindHMLParser.ExprContext,0)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitQuantExpr" ):
                return visitor.visitQuantExpr(self)
            else:
                return visitor.visitChildren(self)


    class BoolLitContext(ExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a KindHMLParser.ExprContext
            super().__init__(parser)
            self.copyFrom(ctx)


        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitBoolLit" ):
                return visitor.visitBoolLit(self)
            else:
                return visitor.visitChildren(self)



    def expr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = KindHMLParser.ExprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 30
        self.enterRecursionRule(localctx, 30, self.RULE_expr, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 264
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,27,self._ctx)
            if la_ == 1:
                localctx = KindHMLParser.ParenExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 215
                self.match(KindHMLParser.T__6)
                self.state = 216
                self.expr(0)
                self.state = 217
                self.match(KindHMLParser.T__7)
                pass

            elif la_ == 2:
                localctx = KindHMLParser.IntLitContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 219
                self.match(KindHMLParser.INT)
                pass

            elif la_ == 3:
                localctx = KindHMLParser.RealLitContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 220
                self.match(KindHMLParser.REAL)
                pass

            elif la_ == 4:
                localctx = KindHMLParser.BoolLitContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 221
                _la = self._input.LA(1)
                if not(_la==34 or _la==35):
                    self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                pass

            elif la_ == 5:
                localctx = KindHMLParser.NullLitContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 222
                self.match(KindHMLParser.T__35)
                pass

            elif la_ == 6:
                localctx = KindHMLParser.PayableExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 223
                self.match(KindHMLParser.T__9)
                self.state = 224
                self.match(KindHMLParser.T__6)
                self.state = 225
                self.expr(0)
                self.state = 226
                self.match(KindHMLParser.T__7)
                pass

            elif la_ == 7:
                localctx = KindHMLParser.FunCallExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 228
                localctx.fn = self.match(KindHMLParser.ID)
                self.state = 229
                self.match(KindHMLParser.T__6)
                self.state = 231
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if (((_la) & ~0x3f) == 0 and ((1 << _la) & 8322652643956622464) != 0):
                    self.state = 230
                    self.exprs()


                self.state = 233
                self.match(KindHMLParser.T__7)
                pass

            elif la_ == 8:
                localctx = KindHMLParser.NameExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 234
                self.match(KindHMLParser.ID)
                pass

            elif la_ == 9:
                localctx = KindHMLParser.UnaryExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 235
                localctx.op = self._input.LT(1)
                _la = self._input.LA(1)
                if not(_la==37 or _la==38):
                    localctx.op = self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 236
                self.expr(10)
                pass

            elif la_ == 10:
                localctx = KindHMLParser.QuantExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 237
                localctx.q = self._input.LT(1)
                _la = self._input.LA(1)
                if not(_la==55 or _la==56):
                    localctx.q = self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 238
                self.qvars()
                self.state = 239
                self.match(KindHMLParser.T__29)
                self.state = 240
                self.expr(2)
                pass

            elif la_ == 11:
                localctx = KindHMLParser.ModalExprContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 242
                self.match(KindHMLParser.T__56)
                self.state = 243
                localctx.sender = self.expr(0)
                self.state = 244
                self.match(KindHMLParser.T__32)
                self.state = 245
                localctx.contractName = self.match(KindHMLParser.ID)
                self.state = 246
                self.match(KindHMLParser.T__29)
                self.state = 247
                localctx.proc = self.match(KindHMLParser.ID)
                self.state = 248
                self.match(KindHMLParser.T__6)
                self.state = 250
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if (((_la) & ~0x3f) == 0 and ((1 << _la) & 8322652643956622464) != 0):
                    self.state = 249
                    self.exprs()


                self.state = 252
                self.match(KindHMLParser.T__7)
                self.state = 255
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==31:
                    self.state = 253
                    self.match(KindHMLParser.T__30)
                    self.state = 254
                    localctx.value = self.expr(0)


                self.state = 259
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if _la==58:
                    self.state = 257
                    self.match(KindHMLParser.T__57)
                    self.state = 258
                    localctx.blocks = self.expr(0)


                self.state = 261
                self.match(KindHMLParser.T__58)
                self.state = 262
                self.expr(1)
                pass


            self._ctx.stop = self._input.LT(-1)
            self.state = 297
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,29,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 295
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,28,self._ctx)
                    if la_ == 1:
                        localctx = KindHMLParser.MulExprContext(self, KindHMLParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 266
                        if not self.precpred(self._ctx, 9):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 9)")
                        self.state = 267
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not((((_la) & ~0x3f) == 0 and ((1 << _la) & 3848290697216) != 0)):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 268
                        self.expr(10)
                        pass

                    elif la_ == 2:
                        localctx = KindHMLParser.AddExprContext(self, KindHMLParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 269
                        if not self.precpred(self._ctx, 8):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 8)")
                        self.state = 270
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(_la==38 or _la==42):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 271
                        self.expr(9)
                        pass

                    elif la_ == 3:
                        localctx = KindHMLParser.CmpExprContext(self, KindHMLParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 272
                        if not self.precpred(self._ctx, 7):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 7)")
                        self.state = 273
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not((((_la) & ~0x3f) == 0 and ((1 << _la) & 131941395333120) != 0)):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 274
                        self.expr(8)
                        pass

                    elif la_ == 4:
                        localctx = KindHMLParser.EqExprContext(self, KindHMLParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 275
                        if not self.precpred(self._ctx, 6):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 6)")
                        self.state = 276
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(_la==47 or _la==48):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 277
                        self.expr(7)
                        pass

                    elif la_ == 5:
                        localctx = KindHMLParser.AndExprContext(self, KindHMLParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 278
                        if not self.precpred(self._ctx, 5):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 5)")
                        self.state = 279
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(_la==49 or _la==50):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 280
                        self.expr(6)
                        pass

                    elif la_ == 6:
                        localctx = KindHMLParser.OrExprContext(self, KindHMLParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 281
                        if not self.precpred(self._ctx, 4):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 4)")
                        self.state = 282
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(_la==51 or _la==52):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 283
                        self.expr(5)
                        pass

                    elif la_ == 7:
                        localctx = KindHMLParser.ImpliesExprContext(self, KindHMLParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 284
                        if not self.precpred(self._ctx, 3):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                        self.state = 285
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(_la==53 or _la==54):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 286
                        self.expr(3)
                        pass

                    elif la_ == 8:
                        localctx = KindHMLParser.MemberExprContext(self, KindHMLParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 287
                        if not self.precpred(self._ctx, 12):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 12)")
                        self.state = 288
                        self.match(KindHMLParser.T__29)
                        self.state = 289
                        self.match(KindHMLParser.ID)
                        pass

                    elif la_ == 9:
                        localctx = KindHMLParser.IndexExprContext(self, KindHMLParser.ExprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 290
                        if not self.precpred(self._ctx, 11):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 11)")
                        self.state = 291
                        self.match(KindHMLParser.T__24)
                        self.state = 292
                        self.expr(0)
                        self.state = 293
                        self.match(KindHMLParser.T__25)
                        pass

             
                self.state = 299
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,29,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class ExprsContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(KindHMLParser.ExprContext)
            else:
                return self.getTypedRuleContext(KindHMLParser.ExprContext,i)


        def getRuleIndex(self):
            return KindHMLParser.RULE_exprs

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitExprs" ):
                return visitor.visitExprs(self)
            else:
                return visitor.visitChildren(self)




    def exprs(self):

        localctx = KindHMLParser.ExprsContext(self, self._ctx, self.state)
        self.enterRule(localctx, 32, self.RULE_exprs)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 300
            self.expr(0)
            self.state = 305
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==13:
                self.state = 301
                self.match(KindHMLParser.T__12)
                self.state = 302
                self.expr(0)
                self.state = 307
                self._errHandler.sync(self)
                _la = self._input.LA(1)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx



    def sempred(self, localctx:RuleContext, ruleIndex:int, predIndex:int):
        if self._predicates == None:
            self._predicates = dict()
        self._predicates[15] = self.expr_sempred
        pred = self._predicates.get(ruleIndex, None)
        if pred is None:
            raise Exception("No predicate with index:" + str(ruleIndex))
        else:
            return pred(localctx, predIndex)

    def expr_sempred(self, localctx:ExprContext, predIndex:int):
            if predIndex == 0:
                return self.precpred(self._ctx, 9)
         

            if predIndex == 1:
                return self.precpred(self._ctx, 8)
         

            if predIndex == 2:
                return self.precpred(self._ctx, 7)
         

            if predIndex == 3:
                return self.precpred(self._ctx, 6)
         

            if predIndex == 4:
                return self.precpred(self._ctx, 5)
         

            if predIndex == 5:
                return self.precpred(self._ctx, 4)
         

            if predIndex == 6:
                return self.precpred(self._ctx, 3)
         

            if predIndex == 7:
                return self.precpred(self._ctx, 12)
         

            if predIndex == 8:
                return self.precpred(self._ctx, 11)
         




