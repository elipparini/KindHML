"""The verification pipeline: source file -> Lustre -> Kind 2 -> verdict."""

from __future__ import annotations

import csv
import os
import time
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Dict, List, Optional, Tuple

from . import kind2
from . import lustre as L
from . import pretty
from .builder import parse, parse_spec
from .encode_formula import FormulaEncoder
from .encode_trans import BALANCE, Encoder, param_var, proc_const, summed_maps
from .errors import KindHMLError
from .concrete import (describe_tx, python_value, state_from_values, state_literal,
                       state_paths)
from .cutoff import Cutoff, Scanner, idle_users
from .fuzz import Fuzzer
from .invariants import Checks, describe_state, final_values, python_constant, state_values
from .invgen import (candidates as invariant_templates, generate as generate_invariants,
                     minimize as minimize_invariants)
from .model import System
from .typecheck import check
from . import syntax as S


# The files of a benchmark family (a directory of contracts with shared rules; see
# contracts/README.md).
SPEC = "spec.hml"
LEMMAS_FILE = "lemmas.hml"
GROUNDTRUTH = "groundtruth.csv"
EXPECTED = {"true": True, "false": False, "unknown": None}


def load(path: str, lemmas: bool = True):
    """Parse and type-check a contract file. Returns the resolved program and the warnings.

    A file outside a family holds its rules, with the ground truth in `@groundtruth`
    comments. In a family, the contract file holds no rules: they are those of spec.hml,
    then those of <stem>.hml (if present), which replace the rules of the same name; with
    `lemmas`, the invariants of lemmas.hml (if present) follow. The ground truth of the
    rules comes from groundtruth.csv."""
    with open(path) as f:
        program = parse(f.read())
    folder = os.path.dirname(path)
    if os.path.exists(os.path.join(folder, SPEC)):
        if program.rules:
            raise KindHMLError(f"{path}: a contract of a family has no rules (they are in"
                               f" {SPEC})")
        program = replace(program, rules=family_rules(path, lemmas))
    return check(program)


def family_rules(path: str, lemmas: bool = True) -> Tuple[S.Rule, ...]:
    """The raw rules of the contract `path` of a family (see `load`)."""
    folder = os.path.dirname(path)
    rules = {r.name: r for r in _spec(os.path.join(folder, SPEC))}
    override = os.path.join(folder, stem(path) + ".hml")
    if os.path.exists(override):
        rules.update((r.name, r) for r in _spec(override))
    expected = groundtruth(folder).get(os.path.basename(path), {})
    out = [replace(r, groundtruth=expected.get(r.name)) for r in rules.values()]
    lemma_file = os.path.join(folder, LEMMAS_FILE)
    if lemmas and os.path.exists(lemma_file):
        for r in _spec(lemma_file):
            if not r.invariant:
                raise KindHMLError(f"{r.name} is not an invariant (a lemma is)", r.pos)
            out.append(replace(r, groundtruth=None, lemma=True))
    return tuple(out)


def _spec(path: str) -> Tuple[S.Rule, ...]:
    with open(path) as f:
        return parse_spec(f.read(), path)


def groundtruth(folder: str) -> Dict[str, Dict[str, Optional[bool]]]:
    """The ground truth of a family: contract file -> rule -> expected verdict (None:
    unknown), from groundtruth.csv (columns contract, property, expected, note)."""
    out: Dict[str, Dict[str, Optional[bool]]] = {}
    path = os.path.join(folder, GROUNDTRUTH)
    if not os.path.exists(path):
        return out
    with open(path, newline="") as f:
        for n, row in enumerate(csv.DictReader(f), start=2):
            if row["expected"] not in EXPECTED:
                raise KindHMLError(f"{path}, line {n}: expected must be one of"
                                   f" {', '.join(EXPECTED)}")
            out.setdefault(row["contract"], {})[row["property"]] = EXPECTED[row["expected"]]
    return out


def tasks(program: S.Program) -> List[S.Rule]:
    """The rules to verify: all of them but the lemmas."""
    return [r for r in program.rules if not r.lemma]


DEFAULT_MODE = "inline"
AUTO_ORDER = tuple(os.environ.get("KINDHML_AUTO_ORDER", "cvc5,z3").split(","))
DEFAULT_EXPAND = ("address", "method")


LEMMAS = os.environ.get("KINDHML_LEMMAS", "1") != "0"


def lustre_for(program: S.Program, rule: S.Rule, n_users: int, mode: str = DEFAULT_MODE,
               expand=DEFAULT_EXPAND, lemmas: bool = LEMMAS, ghost_sums: bool = False) -> str:
    """The Lustre program checking `rule`: the transition system (Init, Trans) and the
    property (∧_C constructed_C) → Φ(φ). With `lemmas`, also quantifier-free invariants of
    every system (balances are nonnegative), which Kind 2 proves first and then uses to
    strengthen the induction for the rule (its invariant generator does not work on
    quantified properties). With `ghost_sums`, sum(m) is a state variable."""
    if rule not in program.rules:
        program = replace(program, rules=program.rules + (rule,))   # for its sums
    enc = Encoder(System.make(program, n_users, ghost_sums))
    prog, main = enc.program()
    if lemmas:
        main.properties += enc.lemmas()
    main.properties.append((rule.name, FormulaEncoder(enc, mode, tuple(expand)).rule(rule)))
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
    trace: str = ""                  # method fuzz: the transactions reaching the counterexample
    scope: str = ""                  # parameterized mode: the numbers of users of the verdict

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
        scope = f" ({self.scope})" if self.scope else ""
        line = (f"{self.rule.name}: {what}{how}{scope} (ground truth:"
                f" {self.groundtruth_check()})")
        if self.trace:
            line += f"\n    counterexample reached by: {self.trace}"
        if self.cti and self.status not in ("valid", "invalid"):
            line += (f"\n    counterexample to induction (possibly unreachable; consider"
                     f" stronger invariants): {self.cti}")
        return line


STRATEGIES = ("portfolio", "kind2")
FIRST_BUDGET = 4.0                  # seconds per task in the first round; doubled each round
KIND2_SHARE = 4                     # without a time limit, Kind 2 gets 4 budgets per round
INVGEN_SECONDS = 2.0                # random testing that filters the generated invariants
STUCK_AFTER = 16.0                  # Houdini drops generated candidates undecided after this
LIGHT_ENGINES = ["--enable", "BMC", "--enable", "IND"]
FREE_SOLVERS = ("z3", "cvc5")       # z3 first: nlsat for nonlinear real queries
# parameterized mode: the budget of each step confirming that a counterexample found extends
# to more users (its final state, its check with other balances), even after the time limit
CONFIRM_SECONDS = 10.0


def verify(program: S.Program, rule: S.Rule, n_users: int, timeout: Optional[float],
           mode: str = DEFAULT_MODE, expand=DEFAULT_EXPAND, lus_path: Optional[str] = None,
           extra_args: Optional[List[str]] = None, solver: str = "auto",
           cex: bool = False, strategy: str = "portfolio",
           context: Optional[dict] = None, invgen: bool = True,
           user_invariants: bool = True, parameterized: bool = False) -> Outcome:
    """Check one rule within `timeout` seconds (None or 0: no limit, the search goes on until
    there is a verdict). With `cex`, an invalid rule comes with a counterexample (slower).

    Strategy "kind2": Kind 2 on (Init, Trans) and Φ(φ) (`kind2_search`).
    Strategy "portfolio" (default): rounds of the following tasks, one Kind 2 job at a time,
    each with the round's budget (FIRST_BUDGET, doubled at each round; task 5 gets
    KIND2_SHARE budgets, or, with a time limit and linear arithmetic, all the time left):
      1. prove the invariants (`invariants.py`; shared by the rules of a run through
         `context`): those of the file (unless `user_invariants` is false) and, with
         `invgen`, the generated candidates (`invgen.py`);
      2. "invariants": check the rule on a free state satisfying them; a counterexample s*
         ends this task and starts task 3;
      3. "reach": BMC search for s* in the transition system (a counterexample of the rule);
      4. "fuzz": random testing, confirmed exactly (`fuzz.py`);
      5. "kind2": `kind2_search`, with BMC and k-induction only after the memory limit
         killed a solver.
    An invariant proved inductive (task 1) is valid ("inductive").

    With `parameterized` (strategy "portfolio"; DESIGN.md, Sect. 7), if the rule has a
    cutoff N = max(c_H, c_R) <= n_users (`effective_users`), sums are state variables and
    each task uses its own number of users: each step of Houdini its cutoff (the invariants
    then hold for every n >= c_H, the largest of them, `_Invariants.users`); the check of
    the rule on a free state the cutoff u of its premises (the rule then holds for every
    n >= max(c_H, u)); the searches for counterexamples and Kind 2, N users. A
    counterexample holds for every n >= its number of users if the rule has no address
    variable universal in its negation (`Scanner.dual`; the other users stay idle);
    otherwise it says nothing about more users, and the outcome is unknown. A proof of task
    5 holds only for N users, and is ignored if N < n_users. A counterexample of a rule
    with such a variable holds for every n >= its number of users if its final state has
    enough idle users (Lemma 7.6, `Scanner.idle_needed`, `idle_users`)."""
    if context is None:
        context = {}
    users, ghost, cut = (effective_users(context, program, n_users, mode, expand, invgen,
                                         user_invariants, rule)
                         if parameterized and strategy == "portfolio" else (n_users, False, None))
    reduced = users < n_users
    lustre = lustre_for(program, rule, users, mode, expand, ghost_sums=ghost)
    if lus_path:
        with open(lus_path, "w") as f:
            f.write(lustre)
    deadline = time.time() + timeout if timeout else None
    if strategy == "kind2":
        return kind2_search(rule, lustre, timeout or None, extra_args, solver, cex)
    # parameterized mode: the idle users a counterexample needs to extend to more users
    need = Scanner(System.make(program, users)).idle_needed(rule.formula) if ghost else 0
    dual = need > 0
    # the added users have the balance of the idle ones; 0 if a sum of the balances matters
    balance_sum = BALANCE in summed_maps(S.Program(program.contracts, (rule,),
                                                   program.balance_type))

    # whether a transaction can read the balance of a user that takes no part in it
    code_sums_balance = BALANCE in summed_maps(S.Program(program.contracts, (),
                                                         program.balance_type))

    def idle(final: Optional[Dict[str, object]], m: int) -> int:
        """The largest number of idle users with the same balance in the final state of a
        counterexample with m users (Lemma 7.6)."""
        if final is None:
            return 0
        groups = idle_users(final, System.make(program, m))
        return max((len(us) for b, us in groups.items() if b == 0 or not balance_sum),
                   default=0)

    def normalized(final: Optional[Dict[str, object]], participants: Optional[set],
                   m: int) -> Optional[Dict[str, object]]:
        """The final state of the same counterexample in which the users that take no part
        in its transactions (not a sender, a called address or an argument; the address
        fields only hold such users) have initial balance 0: no transaction reads or
        changes their balances (unless the contracts sum the balances), so it is the final
        state with their balances set to 0. None if the rule is not false there (exact
        check), or nothing changes."""
        if final is None or participants is None or code_sums_balance:
            return None
        system = System.make(program, m)
        zero = 0 if program.balance_type != S.REAL else Fraction(0)
        moved = {u for u in system.users if u not in participants
                 and final.get(f"s.balance.k_{u}") != zero}
        if not moved:
            return None
        out = dict(final)
        out.update({f"s.balance.k_{u}": zero for u in moved})
        checks = invs.checks_for(m)
        lus = checks.concrete_check(rule, state_literal(state_from_values(out, system,
                                                                          checks.enc),
                                                        system, checks.enc))
        return out if _free_run(lus, [rule.name], CONFIRM_SECONDS)[0] == "invalid" else None

    def extends(final: Optional[Dict[str, object]], participants: Optional[set],
                m: int) -> Optional[str]:
        """Why a counterexample with m users holds for every n >= m (Lemmas 7.5 and 7.6),
        or None."""
        if not dual:
            return ""
        if idle(final, m) >= need:
            return f" ({idle(final, m)} idle users, {need} needed)"
        moved = normalized(final, participants, m)
        if moved is not None and idle(moved, m) >= need:
            return (f" ({idle(moved, m)} idle users, with initial balance 0, {need}"
                    f" needed)")
        return None

    notes: List[str] = []           # counterexamples that do not extend

    def scoped(o: Outcome, low: int, checked: Optional[int] = None,
               final: Optional[Dict[str, object]] = None,
               participants: Optional[set] = None) -> Outcome:
        """The outcome with the numbers of users for which it holds (parameterized mode):
        a proof by tasks 1-2 for every n >= low; a counterexample with low users, whose
        final state is `final` (by path) and whose transactions name `participants`."""
        if cut is None:
            return o
        if not ghost:
            c = cut.of_rule(rule.name)
            why = (f"cutoff {c} > {n_users}" if c is not None
                   else f"no cutoff: {cut.outside.get(rule.name) or cut.reason}")
            o.scope = f"with {_n(users)}; {why}"
            return o
        if o.status == "valid":
            o.scope = (f"for every n >= {_n(low)}" if o.method in ("inductive", "invariants")
                       else f"for {_n(low)}")
            if checked is not None and checked != low:
                o.scope += f"; rule checked with {_n(checked)}"
        elif o.status == "invalid" and (why := extends(final, participants, low)) is not None:
            o.scope = f"counterexample with {_n(low)}, for every n >= {low}{why}"
        elif o.status == "invalid" and low < n_users:
            notes.append(f"a counterexample with {_n(low)} does not extend to {_n(n_users)}:"
                         f" {idle(final, low)} idle users, {need} needed")
            o = Outcome(rule, kind2.PropertyResult(rule.name, "unknown"), o.errors, o.solver,
                        o.method, o.cti, trace=o.trace, scope=notes[-1])
        else:
            o.scope = "; ".join([f"with {_n(low)}"] + notes[-1:])
        return o

    # Houdini once per file: with the cutoffs of its steps in parameterized mode
    invs = _entry(context, program, cut.steps if ghost else users, mode, expand, invgen,
                  user_invariants, ghost)
    nonlinear = is_nonlinear(program)
    start, budget = time.time(), FIRST_BUDGET
    proof_open, target, engines, kind2_open = True, None, extra_args, True
    target_users = users                # the users of the counterexample to induction
    premises: List[List[str]] = []
    attempts: Optional[List[tuple]] = None
    last = Outcome(rule, kind2.PropertyResult(rule.name, "unknown"), [])
    while True:
        for task in ("invariants", "proof", "reach", "fuzz", "kind2"):
            # the conditions are evaluated in turn: a counterexample found by "proof" is
            # searched for by "reach" in the same round
            if task == "invariants" and invs.proved is not None:
                if rule.invariant and rule.name in invs.proved:
                    return scoped(_valid(rule, "inductive", time.time() - start), invs.users)
                continue
            if task == "proof" and (invs.proved is None or not proof_open):
                continue
            if task == "reach" and not target:
                continue
            if task == "kind2" and not kind2_open:
                continue
            left = None if deadline is None else deadline - time.time()
            if left is not None and left <= 0:
                return scoped(last, users)
            b = budget if left is None else min(budget, left)
            if task == "kind2":
                # With a time limit and linear arithmetic, Kind 2 gets all the time left: it
                # restarts from scratch at each run, and the other tasks succeed in seconds
                # or not at all. With nonlinear arithmetic, Kind 2 rarely concludes, and the
                # rounds go on.
                b = KIND2_SHARE * budget
                if left is not None:
                    b = min(b, left) if nonlinear else left
            if task == "invariants":
                invs.attempt(b)
                if invs.proved is not None and rule.invariant and rule.name in invs.proved:
                    return scoped(_valid(rule, "inductive", time.time() - start), invs.users)
            elif task == "proof":
                # forms to try: for each premise, from the smallest, the rule as one property
                # and split into cases; a counterexample under the last premise (the
                # strongest) is the state searched for by "reach"
                if attempts is None:
                    premises = invs.checks.premises(rule, invs.assumed())
                    attempts = [(i, split) for i in range(len(premises))
                                for split in (False, True)]
                for i, split in list(attempts):
                    if (i, split) not in attempts:
                        continue
                    left = None if deadline is None else deadline - time.time()
                    if left is not None and left <= 1:
                        break
                    b = budget if left is None else min(budget, left)
                    # parameterized mode: the cutoff of this check, with these premises
                    u = max(1, invs.checks.rule_count(premises[i], rule)) if ghost else users
                    lus, names = invs.checks_for(u).rule_check(rule, premises[i], split)
                    status, refuted, s = _free_run(lus, names, b)
                    if status == "valid":
                        return scoped(_valid(rule, "invariants", time.time() - start, s),
                                      max(invs.users, u), u)
                    if status == "invalid":
                        attempts = [a for a in attempts if a[0] != i]
                        if i == len(premises) - 1:
                            proof_open = False
                            left = None if deadline is None else deadline - time.time()
                            out = kind2.run(lus, b if left is None else max(min(b, left), 1),
                                            solver=s, extra_args=LIGHT_ENGINES, cex=True)
                            res = next((p for p in out.properties if p.name == refuted),
                                       None)
                            target = state_values(res.counterexample) if res else {}
                            target_users = u
                            last.cti = describe_state(target)
                            break
            elif task == "fuzz":
                deadline_fuzz = time.time() + b
                checks = invs.checks_for(users)
                for txs, st in invs.fuzzer_for(users).candidates(rule, b / 2):
                    left = deadline_fuzz - time.time()
                    if left <= 1:
                        break
                    lus = checks.concrete_check(
                        rule, state_literal(st, checks.enc.system, checks.enc))
                    status, _, s = _free_run(lus, [rule.name], left)
                    if status == "invalid":
                        res = kind2.PropertyResult(rule.name, "invalid", len(txs), "fuzz",
                                                   time.time() - start)
                        named = {x for tx in txs for x in [tx.sender, tx.contract]
                                 + [v for v in tx.args.values() if isinstance(v, str)]}
                        o = scoped(Outcome(rule, res, [], s, "fuzz",
                                           trace="; ".join(describe_tx(tx) for tx in txs)),
                                   users, final=state_paths(st, checks.enc.system),
                                   participants=named)
                        if o.status == "invalid":
                            return o
                        o.cti, last = last.cti, o       # it does not extend: go on
            elif task == "reach":
                lus = invs.checks_for(target_users).reach_check(target)
                # a rule that needs idle users needs the whole final state (the target may
                # leave out values, e.g. balances that the property does not read)
                out = kind2.run(lus, b, solver="z3", extra_args=["--enable", "BMC"],
                                cex=cex or dual)
                res = next((p for p in out.properties if p.name == "unreachable"), None)
                if res and res.status == "invalid":
                    res.name, res.time = rule.name, time.time() - start
                    final = (final_values(res.counterexample) if res.counterexample
                             else {p: python_constant(v) for p, v in target.items()})
                    o = scoped(Outcome(rule, res, out.errors, "z3", "reach", last.cti),
                               target_users, final=final,
                               participants=(_participants(res.counterexample,
                                                           invs.checks_for(target_users)
                                                           .enc.system)
                                             if res.counterexample else None))
                    if o.status == "invalid":
                        return o
                    target, last = None, o              # it does not extend: go on
            else:
                o = kind2_search(rule, lustre, b, engines, solver, cex)
                if o.status == "valid" and reduced:
                    # a proof for `users` users only (Kind 2's invariants name the users)
                    kind2_open = False
                    continue
                if o.status in ("valid", "invalid"):
                    o.method = "kind2"
                    final, named = None, None
                    if o.status == "invalid" and dual:
                        # without the lemmas, which BMC cannot prove: Kind 2 then stops at
                        # the counterexample instead of the time limit
                        bare = lustre_for(program, rule, users, mode, expand, lemmas=False,
                                          ghost_sums=ghost)
                        final, named = _final_state(o, bare, b, deadline,
                                                    System.make(program, users))
                    cti = o.cti or last.cti
                    o = scoped(o, users, final=final, participants=named)
                    if o.status in ("valid", "invalid"):
                        return o
                    # it does not extend, and BMC would find it again: go on without Kind 2
                    o.cti, last, kind2_open = cti, o, False
                    continue
                if o.memory_killed and engines is None:
                    engines = LIGHT_ENGINES
                o.method, o.cti = "kind2", last.cti
                last = o
        budget *= 2


def _participants(counterexample: list, system: System) -> set:
    """The users named by the transactions of a counterexample of the transition system:
    at each step but the last (whose transaction is not taken), the sender, the called
    address and the address arguments of the procedure called."""
    t: Dict[str, Dict[int, object]] = {}
    last = 0
    for block in counterexample or []:
        for stream in block.get("streams", []):
            values = dict((int(k), v) for k, v in stream.get("instantValues", []))
            last = max([last] + list(values))
            if stream["name"].startswith("t."):
                t[stream["name"][2:]] = values
    procs = {proc_const(c.name, p.name): (c, p) for c, p in system.methods}
    out = set()
    for i in range(last):
        named = [t.get("sender", {}).get(i), t.get("cx", {}).get(i)]
        c, p = procs.get(t.get("fx", {}).get(i), (None, None))
        if p is not None:
            named += [t.get(param_var(c.name, p.name, x.name), {}).get(i)
                      for x in p.params if x.type == S.ADDRESS]
        out |= {python_value(v) for v in named if isinstance(v, str)}
    return out


def _final_state(o: Outcome, lustre: str, budget: float, deadline: Optional[float],
                 system: System) -> Tuple[Optional[Dict[str, object]], Optional[set]]:
    """The final state of the counterexample of a refuted rule (Kind 2 on the transition
    system), by path, and the users its transactions name: from its counterexample if it
    has one, else from a run of BMC with counterexamples (z3, with the budget, but at least
    CONFIRM_SECONDS, also after the deadline); None if there is none."""
    cex = o.result.counterexample if o.result else None
    if not cex:
        left = None if deadline is None else deadline - time.time()
        out = kind2.run(lustre, max(budget if left is None else min(budget, left),
                                    CONFIRM_SECONDS),
                        solver="z3", extra_args=["--enable", "BMC"], cex=True)
        res = next((p for p in out.properties if p.name == o.rule.name), None)
        cex = res.counterexample if res and res.status == "invalid" else None
    return (final_values(cex), _participants(cex, system)) if cex else (None, None)


def _n(users: int) -> str:
    return f"{users} user" if users == 1 else f"{users} users"


def _entry(context: dict, program: S.Program, n_users: int, mode: str, expand,
           invgen: bool, user_invariants: bool, ghost_sums: bool = False) -> "_Invariants":
    """The invariants of `program` in `context` (created on first use)."""
    key = (id(program), n_users, mode, tuple(expand), invgen, user_invariants, ghost_sums)
    if key not in context:
        context[key] = _Invariants.make(program, n_users, mode, expand, invgen,
                                        user_invariants, ghost_sums)
    return context[key]


def effective_users(context: dict, program: S.Program, n_users: int, mode: str, expand,
                    invgen: bool, user_invariants: bool,
                    rule: Optional[S.Rule] = None) -> Tuple[int, bool, Cutoff]:
    """Parameterized mode: a number of users c, whether sums are state variables, and the
    cutoffs of the checks on free values (`Checks.cutoff`, with all the templates of `invgen`
    and the invariants of the file as candidates: those that survive give smaller cutoffs).
    c is the cutoff of the steps of Houdini c_H or, for `rule`, max(c_H, its cutoff c_R).
    If c <= n_users: c, with sums as state variables; otherwise (or without a cutoff):
    n_users, as without parameterized mode."""
    key = ("cutoff", id(program), invgen, user_invariants)
    if key not in context:
        rules = [r for r in program.rules if user_invariants or not r.invariant]
        templates = invariant_templates(program) if invgen else []
        extended = S.Program(program.contracts, tuple(rules) + tuple(templates),
                             program.balance_type)
        context[key] = Checks(extended, 1, mode, expand, ghost_sums=True).cutoff(tasks(program))
    cut = context[key]
    c = cut.steps if rule is None else cut.of_rule(rule.name)
    if c is None or n_users < c:
        return n_users, False, cut
    return c, True, cut


def prove_invariants(program: S.Program, n_users: int, timeout: Optional[float],
                     context: dict, mode: str = DEFAULT_MODE, expand=DEFAULT_EXPAND,
                     invgen: bool = True, user_invariants: bool = True,
                     parameterized: bool = False) -> "_Invariants":
    """The invariant phase of a file, before its rules, with its own time limit (None: no
    limit): candidates (declared and generated) and Houdini, in passes with doubling
    budgets, until the inductive subset is found. The rules of the file then use it through
    `context`; if the phase does not finish, `verify` goes on with it in its rounds. Without
    a separate phase, Houdini shared the time of each rule with the other tasks, and on the
    lending protocol it did not finish within the 11 rules of 60 s. With `parameterized`,
    with the number of users of `effective_users`."""
    cut, ghost = None, False
    if parameterized:
        n_users, ghost, cut = effective_users(context, program, n_users, mode, expand, invgen,
                                              user_invariants)
    invs = _entry(context, program, n_users, mode, expand, invgen, user_invariants, ghost)
    invs.cutoff = cut
    deadline = time.time() + timeout if timeout else None
    b = FIRST_BUDGET
    while invs.proved is None:
        left = None if deadline is None else deadline - time.time()
        if left is not None and left <= 1:
            break
        invs.attempt(b if left is None else min(b, left))
        b *= 2
    return invs


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


def is_nonlinear(program: S.Program) -> bool:
    """Whether a contract multiplies two non-constant terms or divides by one."""
    def constant(e):
        return isinstance(e, (S.IntLit, S.RealLit)) or (
            isinstance(e, S.ToReal) and constant(e.arg))

    def visit(x) -> bool:
        if isinstance(x, S.BinOp) and (
                (x.op == "*" and not constant(x.left) and not constant(x.right))
                or (x.op in ("/", "%") and not constant(x.right))):
            return True
        if isinstance(x, tuple):
            return any(visit(y) for y in x)
        if hasattr(x, "__dataclass_fields__"):
            return any(visit(getattr(x, n)) for n in x.__dataclass_fields__)
        return False
    return visit(program.contracts)


def _valid(rule: S.Rule, method: str, elapsed: float, solver: str = "") -> Outcome:
    return Outcome(rule, kind2.PropertyResult(rule.name, "valid", None, method, elapsed), [],
                   solver, method)


def _free_run(lustre: str, names: List[str], budget: float):
    """A check on free values, with properties `names` (the cases of a rule), with
    FREE_SOLVERS (3/4 of the budget for the first, which usually decides or gives up fast,
    the rest for the second). Returns ("valid" if all
    cases are valid, "invalid" if one is, else "unknown"; the refuted case; the solver)."""
    deadline = time.time() + budget
    valid: set = set()
    for i, s in enumerate(FREE_SOLVERS):
        left = deadline - time.time()
        b = max(left * 3 / 4 if i < len(FREE_SOLVERS) - 1 else left, 1)
        out = kind2.run(lustre, b, solver=s, extra_args=LIGHT_ENGINES)
        for p in out.properties:
            if p.name in names and p.status == "invalid":
                return "invalid", p.name, s
            if p.status == "valid":
                valid.add(p.name)
        if valid >= set(names):
            return "valid", None, s
    return "unknown", None, ""


def _free_run_cex(lustre: str, name: str, budget: float):
    """A check on free values with one property, with FREE_SOLVERS (3/4 of the budget for
    the first): (status, the property's result with its counterexample, solver, whether the
    memory limit killed a process)."""
    deadline = time.time() + budget
    status, res, used, killed = "unknown", None, "", False
    for i, s in enumerate(FREE_SOLVERS):
        left = deadline - time.time()
        b = max(left * 3 / 4 if i < len(FREE_SOLVERS) - 1 else left, 1)
        out = kind2.run(lustre, b, solver=s, extra_args=LIGHT_ENGINES, cex=True)
        killed = killed or out.memory_killed
        res = next((p for p in out.properties if p.name == name), None)
        status, used = (res.status if res else "unknown"), s
        if status in ("valid", "invalid"):
            break
    return status, res, used, killed


def _free_run_all(lustre: str, budget: float):
    """A check on free values with several properties: (the decided ones, by name; whether
    the memory limit killed a process)."""
    deadline = time.time() + budget
    decided: Dict[str, str] = {}
    names: set = set()
    killed = False
    for i, s in enumerate(FREE_SOLVERS):
        left = deadline - time.time()
        b = max(left * 3 / 4 if i < len(FREE_SOLVERS) - 1 else left, 1)
        out = kind2.run(lustre, b, solver=s, extra_args=LIGHT_ENGINES)
        killed = killed or out.memory_killed
        names |= {p.name for p in out.properties}
        for p in out.properties:
            if p.status in ("valid", "invalid"):
                decided.setdefault(p.name, p.status)
        if names and names <= set(decided):
            break
    return decided, killed


class _Invariants:
    """The candidate invariants of a program and, once known, the largest inductive subset
    found by Houdini (`proved`); `dropped` maps a refuted candidate to the failed check."""

    def __init__(self, checks: Checks, generated: Optional[set] = None):
        self.checks = checks
        self.generated = generated or set()     # names of the generated candidates
        self.keys: Dict[str, tuple] = {}        # their template keys (invgen.minimize)
        self.fuzzer = Fuzzer(checks.enc.system)
        self.cutoff: Optional[Cutoff] = None       # parameterized mode (`effective_users`)
        self.parameterized = checks.enc.system.ghost_sums
        size = checks.enc.system.n_users
        self._checks: Dict[int, Checks] = {size: checks}   # the checks for other numbers
        self._fuzzers: Dict[int, Fuzzer] = {size: self.fuzzer}     # of users
        self.candidates = [n for n in checks.candidates if n not in checks.axioms]
        self.proved: Optional[List[str]] = None if self.candidates else list(checks.axioms)
        # once proved: in parameterized mode, the proved invariants hold for every number of
        # users >= users (the largest cutoff of the steps); otherwise, for n_users
        self.users: Optional[int] = None if self.candidates else self._proved_users([])
        self.dropped: Dict[str, str] = {}
        # for the current candidates: the step programs (one per procedure), and the
        # procedures whose step is proved
        self._for: Optional[List[str]] = None
        self._programs: List[tuple] = []
        self._done: set = set()

    def checks_for(self, n_users: int) -> Checks:
        """The checks of the same candidates with `n_users` users."""
        if n_users not in self._checks:
            c = self.checks
            self._checks[n_users] = Checks(c.program, n_users, c.mode, c.expand,
                                           c.enc.system.ghost_sums)
        return self._checks[n_users]

    def fuzzer_for(self, n_users: int) -> Fuzzer:
        if n_users not in self._fuzzers:
            self._fuzzers[n_users] = Fuzzer(self.checks_for(n_users).enc.system)
        return self._fuzzers[n_users]

    def _steps(self, names: List[str]) -> List[tuple]:
        """The step programs of Houdini for the candidates `names`, one per procedure, with
        their checks: in parameterized mode, each with the cutoff of its step for these
        candidates (`Checks.step_count`)."""
        if not self.parameterized:
            return [(lus, c, p, self.checks) for lus, c, p in self.checks.step_conj_checks(names)]
        out = []
        for c, p in self.checks.enc.system.methods:
            checks = self.checks_for(max(1, self.checks.step_count(names, c, p)))
            out += [(lus, c, p, checks)
                    for lus, c, p in checks.step_conj_checks(names, only=(c, p))]
        return out

    def _proved_users(self, programs: List[tuple]) -> int:
        if not self.parameterized:
            return self.checks.enc.system.n_users
        return max([1] + [checks.enc.system.n_users for *_, checks in programs])

    @staticmethod
    def make(program: S.Program, n_users: int, mode: str, expand, invgen: bool = True,
             user_invariants: bool = True, ghost_sums: bool = False) -> "_Invariants":
        """The candidates: the invariants of the file (if `user_invariants`) and, with
        `invgen`, the generated ones that hold in the reachable states of the fuzzer."""
        rules = [r for r in program.rules if user_invariants or not r.invariant]
        generated: List[S.Rule] = []
        keys: Dict[str, tuple] = {}
        if invgen:
            generated, _, keys = generate_invariants(
                program, Fuzzer(System.make(program, n_users)), INVGEN_SECONDS)
        extended = S.Program(program.contracts, tuple(rules) + tuple(generated),
                             program.balance_type)
        invs = _Invariants(Checks(extended, n_users, mode, expand, ghost_sums),
                           {r.name for r in generated})
        invs.keys = {r.name: keys[r.name] for r in generated}
        return invs

    def assumed(self) -> List[str]:
        """The proved invariants that the checks of the rules assume: all of them, but the
        generated ones implied by other proved ones (`invgen.minimize`); fewer, stronger
        premises are faster for the solvers."""
        proved = self.proved or []
        gen = [n for n in proved if n in self.keys]
        kept = set(minimize_invariants([self.keys[n] for n in gen]))
        return [n for n in proved if n not in self.keys or self.keys[n] in kept]

    def attempt(self, budget: float):
        """A Houdini pass within `budget`, which goes on from the previous one.

        Initiation holds trivially: candidates are required where all contracts are
        constructed, and none is in the initial states; the constructor's step establishes
        them. For each procedure not yet done, the conjunction step (`step_conj_checks`)
        gets the time left, at most `budget` (z3 3/4, cvc5 the rest; a program starts only
        with at least min(budget, FIRST_BUDGET) seconds left, since a program cut short says
        nothing):
        * valid: the procedure is done for the current candidates;
        * invalid: the candidates false after the call of its counterexample are refuted;
        * otherwise, or if the counterexample identifies none, the step is checked with one
          property per candidate (`step_check`): the refuted ones are refuted, and generated
          candidates still undecided after at least STUCK_AFTER seconds are dropped
          (generated candidates are best effort; those of the user wait for more time).
        The candidates refuted in a pass are dropped together (a candidate not inductive
        relative to the current candidates is not inductive relative to fewer), and the
        procedures are checked again; `proved` (with the axioms) is set when all are done."""
        deadline = time.time() + budget
        while True:
            names = self.candidates
            if not names:
                self.proved = list(self.checks.axioms)
                self.users = self._proved_users([])
                return
            if self._for != names:
                self._for, self._done = list(names), set()
                self._programs = self._steps(names)
            refuted: Dict[str, str] = {}
            killed = False
            for i, (lus, c, p, checks) in enumerate(self._programs):
                if i in self._done:
                    continue
                left = deadline - time.time()
                if left < min(budget, FIRST_BUDGET):
                    break
                given = min(left, budget)
                status, res, solver, killed = _free_run_cex(lus, "step", given)
                if status == "valid":
                    self._done.add(i)
                    continue
                found = set()
                if status == "invalid" and res is not None:
                    found = checks.refuted_after(res.counterexample, names, c, p)
                if found:
                    refuted.update({n: f"inductive step ({p.name})" for n in found})
                    continue
                if killed:
                    # the memory limit killed a run: it says nothing about the candidates
                    # (under memory pressure, all the AMM candidates were dropped as
                    # undecided); stop the pass, a later one tries again
                    break
                # localise with one property per candidate
                left = deadline - time.time()
                if left < min(budget, FIRST_BUDGET):
                    break
                given = min(left, budget)
                lus1, about = checks.step_check(names, only=(c, p))
                decided, killed = _free_run_all(lus1, given)
                refuted.update({about[q]: f"inductive step ({p.name})"
                                for q, st in decided.items() if st == "invalid"})
                if killed:
                    break
                if given >= STUCK_AFTER:
                    refuted.update({n: "undecided" for q, n in about.items()
                                    if q not in decided and n in self.generated
                                    and n not in refuted})
            if killed and not refuted:
                return
            if refuted:
                self.dropped.update(refuted)
                self.candidates = [n for n in names if n not in refuted]
                if deadline - time.time() <= 1:
                    return
                continue
            if len(self._done) == len(self._programs):
                self.proved = self.checks.axioms + names
                self.users = self._proved_users(self._programs)
            return


def invariant_summary(invs: "_Invariants") -> str:
    """One line: how many candidates (declared, generated) were proved, and dropped; in
    parameterized mode, also the cutoff and the number of users of the checks."""
    users = ""
    if invs.cutoff is not None:
        users = f"; {invs.cutoff.describe()}"
        if invs.parameterized and invs.proved is not None:
            users += f"; invariants for every n >= {_n(invs.users)}"
    if invs.proved is None:
        return (f"invariants: not proved within the time ({len(invs.candidates)} candidates"
                f" left, {len(invs.dropped)} dropped){users}")
    proved = [n for n in invs.proved if n not in invs.checks.axioms]
    gen = sum(1 for n in proved if n in invs.generated)
    return (f"invariants: {len(proved)} proved ({len(proved) - gen} declared, {gen}"
            f" generated), {len(invs.dropped)} dropped{users}")


def invariant_report(context: dict) -> List[str]:
    """The invariants proved for the programs of a run (generated or declared), and the
    number of candidates dropped."""
    lines = []
    for invs in context.values():
        if not isinstance(invs, _Invariants):
            continue                        # a cutoff (`effective_users`)
        if invs.proved is None:
            lines.append("invariants: not proved within the time")
            continue
        for n in invs.proved:
            if n not in invs.checks.axioms:
                kind = "generated" if n in invs.generated else "declared"
                lines.append(f"{kind} invariant {n}: "
                             f"{pretty.expr(invs.checks.program.rule(n).formula)}")
        lines.append(f"candidates dropped by Houdini: {len(invs.dropped)}")
    return lines


def select_rules(program: S.Program, name: str) -> List[S.Rule]:
    if name == "ALL":
        return tasks(program)
    rule = program.rule(name)
    if rule is None:
        raise KindHMLError(f"no rule named '{name}' (rules: "
                           f"{', '.join(r.name for r in program.rules)})")
    return [rule]


def stem(path: str) -> str:
    return os.path.splitext(os.path.basename(path))[0]
