"""The verification pipeline: source file -> Lustre -> Kind 2 -> verdict."""

from __future__ import annotations

import os
import time
from dataclasses import dataclass
from typing import List, Optional

from . import kind2
from .builder import parse
from .encode_formula import FormulaEncoder
from .encode_trans import Encoder
from .errors import KindHMLError
from .model import System
from .typecheck import check
from . import syntax as S


def load(path: str):
    """Parse and type-check a file. Returns the resolved program and the warnings."""
    with open(path) as f:
        text = f.read()
    return check(parse(text))


DEFAULT_MODE = "inline"
AUTO_ORDER = tuple(os.environ.get("KINDHML_AUTO_ORDER", "cvc5,z3").split(","))
DEFAULT_EXPAND = ("address", "method")


def lustre_for(program: S.Program, rule: S.Rule, n_users: int, mode: str = DEFAULT_MODE,
               expand=DEFAULT_EXPAND) -> str:
    """The Lustre program checking `rule`: the transition system (Init, Trans) and the
    property (∧_C constructed_C) → Φ(φ)."""
    enc = Encoder(System.make(program, n_users))
    prog, main = enc.program()
    main.properties.append((rule.name, FormulaEncoder(enc, mode, tuple(expand)).rule(rule)))
    return prog.render()


@dataclass
class Outcome:
    rule: S.Rule
    result: Optional[kind2.PropertyResult]
    errors: List[str]
    solver: str = ""

    @property
    def status(self) -> str:
        return self.result.status if self.result else "error"

    def groundtruth_check(self) -> str:
        gt = self.rule.groundtruth
        if gt is None:
            return "no ground truth"
        if self.status == "valid":
            return "OK" if gt else "NOT OK"
        if self.status == "invalid":
            return "NOT OK" if gt else "OK"
        if self.result and self.result.true_up_to is not None and gt:
            return f"OK-up to {self.result.true_up_to}"
        return "unknown"

    def describe(self) -> str:
        what = self.result.describe() if self.result else "; ".join(self.errors) or "no result"
        solver = f" [{self.solver}]" if self.solver else ""
        return f"{self.rule.name}: {what}{solver} (ground truth: {self.groundtruth_check()})"


def verify(program: S.Program, rule: S.Rule, n_users: int, timeout: float,
           mode: str = DEFAULT_MODE, expand=DEFAULT_EXPAND, lus_path: Optional[str] = None,
           extra_args: Optional[List[str]] = None, solver: str = "auto") -> Outcome:
    """Check one rule. Solver "auto" runs Kind 2 with AUTO_ORDER[0] for at most half of the
    time and, if that gives no verdict, with AUTO_ORDER[1] for the remaining time."""
    lustre = lustre_for(program, rule, n_users, mode, expand)
    if lus_path:
        with open(lus_path, "w") as f:
            f.write(lustre)
    solvers = list(AUTO_ORDER) if solver == "auto" else [solver]
    outcome = None
    deadline = time.time() + timeout
    for i, s in enumerate(solvers):
        left = deadline - time.time()
        budget = left / 2 if i < len(solvers) - 1 else left
        out = kind2.run(lustre, max(budget, 1), extra_args=extra_args, solver=s)
        result = next((p for p in out.properties if p.name == rule.name), None)
        outcome = Outcome(rule, result, out.errors, s)
        if outcome.status in ("valid", "invalid"):
            break
    return outcome


def select_rules(program: S.Program, name: str) -> List[S.Rule]:
    if name == "ALL":
        return list(program.rules)
    rule = program.rule(name)
    if rule is None:
        raise KindHMLError(f"no rule named '{name}' (rules: "
                           f"{', '.join(r.name for r in program.rules)})")
    return [rule]


def stem(path: str) -> str:
    return os.path.splitext(os.path.basename(path))[0]
