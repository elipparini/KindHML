"""The finite system being verified (assumption A1): addresses, methods, variables.

Addresses are `null`, one address per contract (named as the contract), and the user
addresses `u1, ..., un` (EOAs).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Tuple

from . import syntax as S
from .errors import KindHMLError

NULL = "null"


def _uses_block_num(program: S.Program) -> bool:
    """Whether `block.number` occurs, or a modality increases the block number (`@ e` with
    `e` not the literal 0: a negative increase reverts, so it matters also then)."""
    found = False

    def visit(x):
        nonlocal found
        if isinstance(x, S.BlockNum):
            found = True
        elif isinstance(x, S.Modal) and not (isinstance(x.blocks, S.IntLit)
                                             and x.blocks.value == 0):
            found = True
            visit(x.body)
        elif isinstance(x, tuple):
            for y in x:
                visit(y)
        elif hasattr(x, "__dataclass_fields__"):
            for name in x.__dataclass_fields__:
                visit(getattr(x, name))

    visit(program)
    return found


@dataclass(frozen=True)
class ParamVar:
    """A transition variable for a formal parameter (the set ParamVars of the paper)."""
    contract: str
    proc: str
    name: str
    type: S.Type


@dataclass(frozen=True)
class System:
    program: S.Program               # resolved
    n_users: int
    uses_block_num: bool
    ghost_sums: bool = False         # sum(m) is a state variable (parameterized mode)

    @staticmethod
    def make(program: S.Program, n_users: int, ghost_sums: bool = False) -> "System":
        if n_users < 1:
            raise KindHMLError("the number of participants must be at least 1")
        users = {f"u{i}" for i in range(1, n_users + 1)}
        for c in program.contracts:
            if c.name in users or c.name == NULL:
                raise KindHMLError(f"contract name '{c.name}' clashes with an address name", c.pos)
        return System(program, n_users, _uses_block_num(program), ghost_sums)

    @property
    def contracts(self) -> Tuple[S.Contract, ...]:
        return self.program.contracts

    @property
    def users(self) -> List[str]:
        return [f"u{i}" for i in range(1, self.n_users + 1)]

    @property
    def addresses(self) -> List[str]:
        return [NULL] + [c.name for c in self.contracts] + self.users

    @property
    def methods(self) -> List[Tuple[S.Contract, S.Procedure]]:
        return [(c, p) for c in self.contracts for p in c.procs]

    @property
    def param_vars(self) -> List[ParamVar]:
        return [ParamVar(c.name, p.name, x.name, x.type)
                for c, p in self.methods for x in p.params]

    def params_of(self, contract: str, proc: str) -> List[ParamVar]:
        return [v for v in self.param_vars if (v.contract, v.proc) == (contract, proc)]

    def field_type(self, contract: str, name: str) -> S.AnyType:
        return self.program.contract(contract).field_decl(name).type
