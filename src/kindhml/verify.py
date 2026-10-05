"""The verification pipeline: source file -> Lustre -> Kind 2 -> verdict."""

from __future__ import annotations

import os
import time
from dataclasses import dataclass
from typing import Dict, List, Optional

from . import kind2
from . import lustre as L
from .builder import parse
from .encode_formula import FormulaEncoder
from .encode_trans import Encoder
from .errors import KindHMLError
from .invariants import Checks, describe_state, state_values
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


LEMMAS = os.environ.get("KINDHML_LEMMAS", "1") != "0"


def lustre_for(program: S.Program, rule: S.Rule, n_users: int, mode: str = DEFAULT_MODE,
               expand=DEFAULT_EXPAND, lemmas: bool = LEMMAS) -> str:
    """The Lustre program checking `rule`: the transition system (Init, Trans) and the
    property (∧_C constructed_C) → Φ(φ). With `lemmas`, also quantifier-free invariants of
    every system (balances are nonnegative), which Kind 2 proves first and then uses to
    strengthen the induction for the rule (its invariant generator does not work on
    quantified properties)."""
    enc = Encoder(System.make(program, n_users))
    prog, main = enc.program()
    if lemmas:
        main.properties += enc.lemmas()
    fenc = FormulaEncoder(enc, mode, tuple(expand))
    prop = fenc.state_formula(rule.formula, L.Var("s")) if rule.invariant else fenc.rule(rule)
    main.properties.append((rule.name, prop))
    return prog.render()


@dataclass
class Outcome:
    rule: S.Rule
    result: Optional[kind2.PropertyResult]
    errors: List[str]
    solver: str = ""
    method: str = ""                 # kind2 | invariants | inductive | reach (see verify)
    cti: str = ""                    # a free state refuting the rule, possibly unreachable
    memory_killed: bool = False

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
        how = "/".join(x for x in (self.method, self.solver) if x)
        how = f" [{how}]" if how else ""
        line = f"{self.rule.name}: {what}{how} (ground truth: {self.groundtruth_check()})"
        if self.cti and self.status not in ("valid", "invalid"):
            line += (f"\n    counterexample to induction (possibly unreachable; consider"
                     f" stronger invariants): {self.cti}")
        return line


STRATEGIES = ("portfolio", "kind2")
FIRST_BUDGET = 4.0                  # seconds per task in the first round; doubled each round
KIND2_SHARE = 4                     # without a time limit, Kind 2 gets 4 budgets per round
LIGHT_ENGINES = ["--enable", "BMC", "--enable", "IND"]
FREE_SOLVERS = ("z3", "cvc5")       # z3 first: nlsat for nonlinear real queries


def verify(program: S.Program, rule: S.Rule, n_users: int, timeout: Optional[float],
           mode: str = DEFAULT_MODE, expand=DEFAULT_EXPAND, lus_path: Optional[str] = None,
           extra_args: Optional[List[str]] = None, solver: str = "auto",
           cex: bool = False, strategy: str = "portfolio",
           context: Optional[dict] = None) -> Outcome:
    """Check one rule within `timeout` seconds (None or 0: no limit, the search goes on until
    there is a verdict). With `cex`, an invalid rule comes with a counterexample (slower).

    Strategy "kind2": Kind 2 on (Init, Trans) and Φ(φ) (`kind2_search`).
    Strategy "portfolio" (default): rounds of the following tasks, one Kind 2 job at a time,
    each with the round's budget (FIRST_BUDGET, doubled at each round; task 4 gets
    KIND2_SHARE budgets, or, with a time limit, all the time left):
      1. prove the invariants of the program (`invariants.py`; shared by the rules of a
         run through `context`);
      2. "invariants": check the rule on a free state satisfying them; a counterexample s*
         ends this task and starts task 3;
      3. "reach": BMC search for s* in the transition system (a counterexample of the rule);
      4. "kind2": `kind2_search`, with BMC and k-induction only after the memory limit
         killed a solver.
    An invariant proved inductive (task 1) is valid ("inductive")."""
    lustre = lustre_for(program, rule, n_users, mode, expand)
    if lus_path:
        with open(lus_path, "w") as f:
            f.write(lustre)
    deadline = time.time() + timeout if timeout else None
    if strategy == "kind2":
        return kind2_search(rule, lustre, timeout or None, extra_args, solver, cex)
    if context is None:
        context = {}
    key = (id(program), n_users, mode, tuple(expand))
    if key not in context:
        context[key] = _Invariants(Checks(program, n_users, mode, expand))
    invs = context[key]
    start, budget = time.time(), FIRST_BUDGET
    proof_open, target, engines = True, None, extra_args
    last = Outcome(rule, kind2.PropertyResult(rule.name, "unknown"), [])
    while True:
        for task in ("invariants", "proof", "reach", "kind2"):
            # the conditions are evaluated in turn: a counterexample found by "proof" is
            # searched for by "reach" in the same round
            if task == "invariants" and invs.proved is not None:
                if rule.invariant and rule.name in invs.proved:
                    return _valid(rule, "inductive", time.time() - start)
                continue
            if task == "proof" and (invs.proved is None or not proof_open):
                continue
            if task == "reach" and not target:
                continue
            left = None if deadline is None else deadline - time.time()
            if left is not None and left <= 0:
                return last
            b = budget if left is None else min(budget, left)
            if task == "kind2":
                # With a time limit, Kind 2 gets all the time left: it restarts from scratch
                # at each run, and the other tasks succeed in seconds or not at all.
                b = KIND2_SHARE * budget if left is None else left
            if task == "invariants":
                invs.attempt(b)
                if invs.proved is not None and rule.invariant and rule.name in invs.proved:
                    return _valid(rule, "inductive", time.time() - start)
            elif task == "proof":
                lus = invs.checks.rule_check(rule, invs.proved)
                status, out, s = _free_run(lus, rule.name, b)
                if status == "valid":
                    return _valid(rule, "invariants", time.time() - start, s)
                if status == "invalid":
                    proof_open = False
                    out = kind2.run(lus, b, solver=s, extra_args=LIGHT_ENGINES, cex=True)
                    res = next((p for p in out.properties if p.name == rule.name), None)
                    target = state_values(res.counterexample) if res else {}
                    last.cti = describe_state(target)
            elif task == "reach":
                lus = invs.checks.reach_check(target)
                out = kind2.run(lus, b, solver="z3", extra_args=["--enable", "BMC"], cex=cex)
                res = next((p for p in out.properties if p.name == "unreachable"), None)
                if res and res.status == "invalid":
                    res.name, res.time = rule.name, time.time() - start
                    return Outcome(rule, res, out.errors, "z3", "reach", last.cti)
            else:
                o = kind2_search(rule, lustre, b, engines, solver, cex)
                if o.status in ("valid", "invalid"):
                    o.method = "kind2"
                    return o
                if o.memory_killed and engines is None:
                    engines = LIGHT_ENGINES
                o.method, o.cti = "kind2", last.cti
                last = o
        budget *= 2


def kind2_search(rule: S.Rule, lustre: str, timeout: Optional[float],
                 extra_args: Optional[List[str]] = None, solver: str = "auto",
                 cex: bool = False) -> Outcome:
    """Kind 2 on the transition system. Solver "auto" runs Kind 2 with AUTO_ORDER[0] for at
    most half of the time and, if that gives no verdict, with AUTO_ORDER[1] for the rest
    (without a time limit, only AUTO_ORDER[0])."""
    solvers = list(AUTO_ORDER) if solver == "auto" else [solver]
    if timeout is None:
        solvers = solvers[:1]
    outcome, killed = None, False
    deadline = time.time() + timeout if timeout else None
    for i, s in enumerate(solvers):
        if deadline is None:
            budget = None
        else:
            left = deadline - time.time()
            budget = max(left / 2 if i < len(solvers) - 1 else left, 1)
        out = kind2.run(lustre, budget, extra_args=extra_args, solver=s, cex=cex)
        killed = killed or out.memory_killed
        result = next((p for p in out.properties if p.name == rule.name), None)
        outcome = Outcome(rule, result, out.errors, s, "kind2")
        if outcome.status in ("valid", "invalid"):
            break
    outcome.memory_killed = killed
    return outcome


def _valid(rule: S.Rule, method: str, elapsed: float, solver: str = "") -> Outcome:
    return Outcome(rule, kind2.PropertyResult(rule.name, "valid", None, method, elapsed), [],
                   solver, method)


def _free_run(lustre: str, name: str, budget: float):
    """A check on free values with FREE_SOLVERS (half of the budget each, unless the first
    decides). Returns (status of property `name`, Kind 2 output, solver)."""
    status, out, used = "unknown", None, ""
    deadline = time.time() + budget
    for i, s in enumerate(FREE_SOLVERS):
        left = deadline - time.time()
        b = max(left / 2 if i < len(FREE_SOLVERS) - 1 else left, 1)
        out = kind2.run(lustre, b, solver=s, extra_args=LIGHT_ENGINES)
        res = next((p for p in out.properties if p.name == name), None)
        status, used = (res.status if res else "error"), s
        if status in ("valid", "invalid"):
            break
    return status, out, used


class _Invariants:
    """The candidate invariants of a program and, once known, the largest inductive subset
    found by Houdini (`proved`); `dropped` maps a refuted candidate to the failed check."""

    def __init__(self, checks: Checks):
        self.checks = checks
        self.candidates = [n for n in checks.candidates if n not in checks.axioms]
        self.proved: Optional[List[str]] = None if self.candidates else list(checks.axioms)
        self.dropped: Dict[str, str] = {}

    def attempt(self, budget: float):
        """One Houdini pass within `budget`: drop the refuted candidates; `proved` (with the
        axioms) is set if the remaining ones are all proved."""
        deadline = time.time() + budget
        while True:
            names = self.candidates
            if not names:
                self.proved = list(self.checks.axioms)
                return
            decided = {}
            for label, lus in (("init", self.checks.init_check(names)),
                               ("step", self.checks.step_check(names))):
                left = deadline - time.time()
                if left <= 0:
                    return
                for s in FREE_SOLVERS:
                    out = kind2.run(lus, max(left / 2, 1), solver=s, extra_args=LIGHT_ENGINES)
                    for p in out.properties:
                        if p.status in ("valid", "invalid"):
                            decided.setdefault(p.name, p.status)
                    if all(f"{label}_{n}" in decided for n in names):
                        break
            refuted = [n for n in names if "invalid" in (decided.get(f"init_{n}"),
                                                         decided.get(f"step_{n}"))]
            if refuted:
                for n in refuted:
                    self.dropped[n] = ("initial state" if decided.get(f"init_{n}") == "invalid"
                                       else "inductive step")
                self.candidates = [n for n in names if n not in refuted]
                continue
            if all(decided.get(f"{lbl}_{n}") == "valid" for n in names
                   for lbl in ("init", "step")):
                self.proved = self.checks.axioms + names
            return


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
