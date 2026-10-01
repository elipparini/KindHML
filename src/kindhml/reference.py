"""Reference interpreter of the operational semantics (for testing only).

This module implements the semantics of Sect. `sec:contracts` (Figs. `fig:semanticsExpr`,
`fig:semanticsSt`, and the transaction rule) directly on the resolved AST, independently of
`desugar.py` and of the encoding. The premises of the transaction rule are those of the paper
plus assumption A5 and the extensions of DESIGN.md, Sect. 4:

* the sender is neither `null` nor the called contract;
* the constructor is called exactly once, before any other procedure;
* a non-payable procedure requires value 0; a payable one transfers the value, which must
  be nonnegative and covered by the sender's balance;
* `uint` parameters must be nonnegative, and so must values assigned to `uint` fields;
* a transfer requires 0 <= amount <= balance of the contract and a recipient different
  from the contract;
* division by zero reverts; division is Euclidean, as in SMT-LIB (`div`, `mod`);
* the transaction sets `block_num` to its block number.

A flagged state is represented by a `State` (with `revert` as the flag b).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Tuple

from . import syntax as S
from .model import NULL, System


class Revert(Exception):
    pass


def smt_div(a: int, b: int) -> int:
    """SMT-LIB integer division: a = b*q + r with 0 <= r < |b|."""
    q = a // b if b > 0 else -((-a) // b)
    if a - b * q < 0:
        q += 1 if b < 0 else -1
    return q


def smt_mod(a: int, b: int) -> int:
    return a - b * smt_div(a, b)


@dataclass
class State:
    balance: Dict[str, int]
    constructed: Dict[str, bool]
    fields: Dict[Tuple[str, str], object]        # map fields are dicts address -> value
    block_num: int = 0
    revert: bool = False

    def copy(self) -> "State":
        return State(dict(self.balance), dict(self.constructed),
                     {k: (dict(v) if isinstance(v, dict) else v) for k, v in self.fields.items()},
                     self.block_num, self.revert)


@dataclass(frozen=True)
class Tx:
    sender: str
    contract: str                                # the called address (cx)
    method: Tuple[str, str]                      # (contract, procedure) (fx)
    args: Dict[str, object] = field(default_factory=dict)   # parameter name -> value
    value: int = 0
    block_num: int = 0


def default(t: S.AnyType, system: System):
    if isinstance(t, S.MapType):
        return {a: default(t.value, system) for a in system.addresses}
    return {S.INT: 0, S.UINT: 0, S.BOOL: False, S.ADDRESS: NULL}[t]


def initial_state(system: System, user_balances: Dict[str, int]) -> State:
    contracts = {c.name for c in system.contracts}
    return State(
        balance={a: (0 if a in contracts else user_balances.get(a, 0)) for a in system.addresses},
        constructed={c.name: False for c in system.contracts},
        fields={(c.name, f.name): default(f.type, system)
                for c in system.contracts for f in c.fields})


class Interpreter:
    def __init__(self, system: System):
        self.system = system

    # ------------------------------------------------------------ transactions

    def step(self, state: State, tx: Tx) -> State:
        """The flagged transition (σ, b) ↦_T (σ', 0), or (σ, 1) if T is not valid in σ."""
        try:
            out = self.transaction(state.copy(), tx)
            out.revert = False
            return out
        except Revert:
            out = state.copy()
            out.revert = True
            return out

    def transaction(self, st: State, tx: Tx) -> State:
        c = self.system.program.contract(tx.contract)
        if c is None or tx.method[0] != c.name:
            raise Revert
        p = c.proc(tx.method[1])
        if tx.sender in (NULL, c.name):
            raise Revert
        if self.system.uses_block_num:
            st.block_num = tx.block_num
        if p.payable:
            self.send(st, tx.sender, c.name, tx.value)
        elif tx.value != 0:
            raise Revert
        if p.name == S.CONSTRUCTOR:
            if st.constructed[c.name]:
                raise Revert
            st.constructed[c.name] = True
        elif not st.constructed[c.name]:
            raise Revert
        env = {"sender": tx.sender, "value": tx.value, "this": c.name, "args": dict(tx.args)}
        for x in p.params:
            if x.type == S.UINT and tx.args[x.name] < 0:
                raise Revert
        self.exec(p.body, st, env)
        return st

    @staticmethod
    def send(st: State, src: str, dst: str, amount: int):
        if not (st.balance[src] >= amount >= 0 and src != dst):
            raise Revert
        st.balance[src] -= amount
        st.balance[dst] += amount

    # ------------------------------------------------------------ statements

    def exec(self, s: S.Stmt, st: State, env) -> None:
        if isinstance(s, S.Skip):
            return
        if isinstance(s, S.Require):
            if not self.eval(s.cond, st, env):
                raise Revert
            return
        if isinstance(s, S.Seq):
            for x in s.stmts:
                self.exec(x, st, env)
            return
        if isinstance(s, S.If):
            self.exec(s.then if self.eval(s.cond, st, env) else s.orelse, st, env)
            return
        if isinstance(s, S.Assign):
            c = env["this"]
            t = self.system.field_type(c, s.target)
            vt = t.value if isinstance(t, S.MapType) else t
            key = self.eval(s.key, st, env) if s.key is not None else None
            v = self.eval(s.value, st, env)
            if vt == S.UINT and v < 0:
                raise Revert
            if key is None:
                st.fields[(c, s.target)] = v
            else:
                st.fields[(c, s.target)][key] = v
            return
        if isinstance(s, S.Transfer):
            to = self.eval(s.to, st, env)
            amount = self.eval(s.amount, st, env)
            self.send(st, env["this"], to, amount)
            return
        if isinstance(s, S.Call):
            # Contract call: the actual parameters and the value are evaluated first; the
            # call is valid under the premises of a transaction except those on the sender.
            c = self.system.program.contract(s.callee.contract)
            p = c.proc(s.proc)
            args = {x.name: self.eval(a, st, env) for x, a in zip(p.params, s.args)}
            value = self.eval(s.value, st, env)
            caller = env["this"]
            if p.payable:
                self.send(st, caller, c.name, value)
            elif value != 0:
                raise Revert
            if not st.constructed[c.name]:
                raise Revert
            if any(x.type == S.UINT and args[x.name] < 0 for x in p.params):
                raise Revert
            self.exec(p.body, st, {"sender": caller, "value": value, "this": c.name,
                                   "args": args})
            return
        raise NotImplementedError(f"statement {s!r}")

    # ------------------------------------------------------------ expressions

    def eval(self, e: S.Expr, st: State, env):
        if isinstance(e, (S.IntLit, S.BoolLit)):
            return e.value
        if isinstance(e, S.NullLit):
            return NULL
        if isinstance(e, S.ContractAddr):
            return e.contract
        if isinstance(e, S.Field):
            return st.fields[(e.contract, e.name)]
        if isinstance(e, S.Param):
            return env["args"][e.name]
        if isinstance(e, S.Index):
            key = self.eval(e.key, st, env)
            if isinstance(e.map, S.Balance):
                return st.balance[key]
            return st.fields[(e.map.contract, e.map.name)][key]
        if isinstance(e, S.Sender):
            return env["sender"]
        if isinstance(e, S.Value):
            return env["value"]
        if isinstance(e, S.BlockNum):
            return st.block_num
        if isinstance(e, S.IsEOA):
            return self.eval(e.arg, st, env) in self.system.users
        if isinstance(e, S.UnOp):
            v = self.eval(e.arg, st, env)
            return (not v) if e.op == "!" else -v
        if isinstance(e, S.BinOp):
            # Strict evaluation: a division by zero anywhere in e makes e undefined
            # (def(e) of Appendix `app:correctness:transition`).
            op = e.op
            a, b = self.eval(e.left, st, env), self.eval(e.right, st, env)
            if op == "&&":
                return a and b
            if op == "||":
                return a or b
            if op == "->":
                return (not a) or b
            if op in ("/", "%"):
                if b == 0:
                    raise Revert
                return smt_div(a, b) if op == "/" else smt_mod(a, b)
            return {"+": lambda: a + b, "-": lambda: a - b, "*": lambda: a * b,
                    "<": lambda: a < b, "<=": lambda: a <= b, ">": lambda: a > b,
                    ">=": lambda: a >= b, "==": lambda: a == b, "!=": lambda: a != b}[op]()
        raise NotImplementedError(f"expression {e!r}")


# ---------------------------------------------------------------- formulae

class FormulaEvaluator:
    """Bounded evaluation of formulae (Fig. `fig:logSem`) over a sequence of flagged states,
    head first. Quantified integers range over `int_domain`; the other domains are those of
    DESIGN.md: addresses but null, methods but constructors, args as records over ParamVars.
    For tests only: with an unbounded domain the result may differ."""

    def __init__(self, system: System, int_domain):
        self.system = system
        self.interp = Interpreter(system)
        self.ints = list(int_domain)

    def values(self, t: S.Type, quantifier: bool = True):
        if t == S.INT:
            return self.ints
        if t == S.UINT:
            return [v for v in self.ints if v >= 0]
        if t == S.BOOL:
            return [False, True]
        if t == S.ADDRESS:
            return [a for a in self.system.addresses if a != NULL or not quantifier]
        if t == S.METHOD:
            return [(c.name, p.name) for c, p in self.system.methods if p.name != S.CONSTRUCTOR]
        raise ValueError(t)

    def records(self, params):
        """All assignments of the given parameters (ParamVar list)."""
        out = [{}]
        for v in params:
            out = [{**r, (v.contract, v.proc, v.name): x} for r in out
                   for x in self.values(v.type, quantifier=False)]
        return out

    def holds(self, e: S.Expr, seq, env=None) -> bool:
        return bool(self.eval(e, seq, env or {}))

    def eval(self, e: S.Expr, seq, env):
        st = seq[0]
        ev = lambda x: self.eval(x, seq, env)
        if isinstance(e, (S.IntLit, S.BoolLit)):
            return e.value
        if isinstance(e, S.NullLit):
            return NULL
        if isinstance(e, S.ContractAddr):
            return e.contract
        if isinstance(e, S.ProcConst):
            return (e.contract, e.proc)
        if isinstance(e, S.QVar):
            return env[e.name]
        if isinstance(e, S.Field):
            return st.fields[(e.contract, e.name)]
        if isinstance(e, S.Index):
            key = ev(e.key)
            if isinstance(e.map, S.Balance):
                return st.balance[key]
            return st.fields[(e.map.contract, e.map.name)][key]
        if isinstance(e, S.BlockNum):
            return st.block_num
        if isinstance(e, S.Reverted):
            return st.revert
        if isinstance(e, S.Old):
            return self.eval(e.arg, seq[1:], env)
        if isinstance(e, S.IsEOA):
            return ev(e.arg) in self.system.users
        if isinstance(e, S.UnOp):
            v = ev(e.arg)
            return (not v) if e.op == "!" else -v
        if isinstance(e, S.BinOp):
            a, b = ev(e.left), ev(e.right)
            op = e.op
            if op in ("/", "%"):
                if b == 0:
                    return 0                   # unspecified, as in lustre_eval
                return smt_div(a, b) if op == "/" else smt_mod(a, b)
            return {"&&": lambda: a and b, "||": lambda: a or b, "->": lambda: (not a) or b,
                    "+": lambda: a + b, "-": lambda: a - b, "*": lambda: a * b,
                    "<": lambda: a < b, "<=": lambda: a <= b, ">": lambda: a > b,
                    ">=": lambda: a >= b, "==": lambda: a == b, "!=": lambda: a != b}[op]()
        if isinstance(e, S.Quant):
            if e.type == S.ARGS:
                domain = self.records(self.system.param_vars)
            else:
                domain = self.values(e.type)
            results = (self.eval(e.body, seq, {**env, e.var: v}) for v in domain)
            return all(results) if e.kind == "forall" else any(results)
        if isinstance(e, S.Modal):
            return self.modal(e, seq, env)
        raise NotImplementedError(f"formula {e!r}")

    def modal(self, e: S.Modal, seq, env) -> bool:
        st = seq[0]
        ev = lambda x: self.eval(x, seq, env)
        sender, value = ev(e.sender), ev(e.value)
        method = ev(e.proc)
        params = self.system.params_of(*method)
        if isinstance(e.proc, S.ProcConst):
            arg_choices = [{v.name: ev(a) for v, a in zip(params, e.args)}]
        elif e.args:
            record = env[e.args[0].name]
            arg_choices = [{v.name: record[(v.contract, v.proc, v.name)] for v in params}]
        else:                                    # h(): parameters existentially quantified
            arg_choices = [{k[2]: x for k, x in r.items()} for r in self.records(params)]
        blocks = ([b for b in self.ints if b >= st.block_num] if self.system.uses_block_num
                  else [0])
        for args in arg_choices:
            for blk in blocks:
                nxt = self.interp.step(st, Tx(sender, e.contract, method, args, value, blk))
                if self.eval(e.body, [nxt] + list(seq), env):
                    return True
        return False
