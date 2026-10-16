// Grammar of KindHML input files: one or more contracts followed by properties (`program`), or
// only properties (`spec`: the shared properties of a benchmark family, see contracts/README.md).
// Contract expressions and property formulas share the rule `expr`; the type checker
// restricts which constructs may occur in each context. Reserved names such as
// `msg.sender`, `balance`, `this`, `lastReverted`, `old(e)`, `is_EOA(e)` are
// ordinary identifiers here and are resolved by the AST builder.

grammar KindHML;

program : pragma* contract+ property_* EOF ;

spec : property_* EOF ;

// `pragma balance real;` makes balances, values and amounts real (default: int). The key is
// an identifier (`balance` must remain one); the builder checks it.
pragma : 'pragma' key=ID type_ ';'? ;

// ---------------------------------------------------------------- contracts

contract : 'contract' name=ID '{' member* '}' ;

member
    : type_ name=ID ';'?                                          # FieldDecl
    | 'constructor' '(' params? ')' modifier* block               # ConstructorDecl
    | 'function' name=ID '(' params? ')' modifier* block          # FunctionDecl
    ;

modifier : 'payable' | 'public' | 'external' ;

params : param (',' param)* ;
param  : type_ name=ID ;

type_
    : 'int'                                                       # IntType
    | 'uint'                                                      # UintType
    | 'real'                                                      # RealType
    | 'bool'                                                      # BoolType
    | 'address'                                                   # AddressType
    | 'mapping' '(' 'address' '=>' type_ ')'                      # MappingType
    ;

block : '{' stmts? '}' ;

// Statements are separated by ';'; a trailing ';' is allowed.
stmts : stmt (';' stmt)* ';'? ;

stmt
    : 'skip'                                                      # SkipStmt
    | 'require' '(' expr ')'                                      # RequireStmt
    | 'if' '(' expr ')' body=stmtBody ('else' orelse=stmtBody)?   # IfStmt
    | target=ID ('[' key=expr ']')? op=('=' | '+=' | '-=') value=expr   # AssignStmt
    | obj=expr '.' method=ID '(' exprs? ')' ('$' value=expr)?     # CallStmt
    | block                                                       # BlockStmt
    | '(' stmts ')'                                               # ParenStmt
    ;

stmtBody : block | stmt ;

// ---------------------------------------------------------------- properties

// An `invariant` is a property without modalities that the tool proves inductive and then
// assumes when it checks the other properties (DESIGN.md, "Invariants").
property_ : kind=('property' | 'invariant') name=ID '{' expr '}' ;

// `method`/`proc` and `calldataargs`/`args` are identifiers (`args` is a common
// variable name); the builder checks them.
qtype : 'int' | 'uint' | 'real' | 'bool' | 'address' | ID ;

qvars : ID (',' ID)* ':' qtype ;

// ---------------------------------------------------------------- expressions
// ANTLR gives higher precedence to earlier alternatives. Quantifiers and
// modalities come last: their body extends as far to the right as possible.

expr
    : '(' expr ')'                                                # ParenExpr
    | INT                                                         # IntLit
    | REAL                                                        # RealLit
    | ('true' | 'false')                                          # BoolLit
    | 'null'                                                      # NullLit
    | 'payable' '(' expr ')'                                      # PayableExpr
    | fn=ID '(' exprs? ')'                                        # FunCallExpr
    | ID                                                          # NameExpr
    | expr '.' ID                                                 # MemberExpr
    | expr '[' expr ']'                                           # IndexExpr
    | op=('!' | '-') expr                                         # UnaryExpr
    | expr op=('*' | '/' | '%') expr                              # MulExpr
    | expr op=('+' | '-') expr                                    # AddExpr
    | expr op=('<' | '<=' | '>' | '>=') expr                      # CmpExpr
    | expr op=('==' | '!=') expr                                  # EqExpr
    | expr op=('&&' | 'and') expr                                 # AndExpr
    | expr op=('||' | 'or') expr                                  # OrExpr
    | <assoc=right> expr op=('->' | 'implies') expr               # ImpliesExpr
    | q=('forall' | 'exists') qvars '.' expr                      # QuantExpr
    | '<<' sender=expr ':' contractName=ID '.' proc=ID
          '(' exprs? ')' ('$' value=expr)? ('@' blocks=expr)? '>>' expr   # ModalExpr
    ;

exprs : expr (',' expr)* ;

// ---------------------------------------------------------------- lexer

REAL : [0-9]+ '.' [0-9]+ ;
INT : [0-9]+ ;
ID  : [a-zA-Z_] [a-zA-Z_0-9]* ;

LINE_COMMENT  : '//' ~[\r\n]* -> channel(HIDDEN) ;
BLOCK_COMMENT : '/*' .*? '*/' -> channel(HIDDEN) ;
WS : [ \t\r\n]+ -> skip ;
