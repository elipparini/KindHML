"""The verification pipeline: source file -> Lustre -> Kind 2 -> verdict."""

from __future__ import annotations

import csv
import os
import time
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Callable, Dict, Generator, List, Optional, Tuple, Union

from . import kind2
from .colors import PLAIN, Palette
from . import lustre as L
from . import pretty
from .builder import parse, parse_spec
from .encode_formula import FormulaEncoder
from .encode_trans import BALANCE, Encoder, param_var, proc_const, summed_maps
from .errors import KindHMLError
from .concrete import (describe_tx, python_value, state_from_values, state_literal,
                       state_paths)
from .cutoff import Cutoff, OutOfFragment, Scanner, idle_users
from .fuzz import Fuzzer, locations
from .invariants import Checks, describe_state, final_values, python_constant, state_values
from .invgen import (candidates as invariant_templates, generate as generate_invariants,
                     minimize as minimize_invariants)
from .model import System
from .typecheck import check
from . import syntax as S


# The files of a benchmark family (a directory of contracts with shared properties; see
# contracts/README.md).
SPEC = "spec.hml"
LEMMAS_FILE = "lemmas.hml"
GROUNDTRUTH = "groundtruth.csv"
EXPECTED = {"true": True, "false": False, "unknown": None}


def load(path: str, lemmas: bool = True):
    """Parse and type-check a contract file. Returns the resolved program and the warnings.

    A file outside a family holds its properties, with the ground truth in `@groundtruth`
    comments. In a family, the contract file holds no properties: they are those of spec.hml,
    then those of <stem>.hml (if present), which replace the properties of the same name; with
    `lemmas`, the invariants of lemmas.hml (if present) follow. The ground truth of the
    properties comes from groundtruth.csv."""
    with open(path) as f:
        program = parse(f.read())
    folder = os.path.dirname(path)
    if os.path.exists(os.path.join(folder, SPEC)):
        if program.properties:
            raise KindHMLError(f"{path}: a contract of a family has no properties (they are in"
                               f" {SPEC})")
        program = replace(program, properties=family_properties(path, lemmas))
    return check(program)


def family_properties(path: str, lemmas: bool = True) -> Tuple[S.Property, ...]:
    """The raw properties of the contract `path` of a family (see `load`)."""
    folder = os.path.dirname(path)
    properties = {r.name: r for r in _spec(os.path.join(folder, SPEC))}
    override = os.path.join(folder, stem(path) + ".hml")
    if os.path.exists(override):
        properties.update((r.name, r) for r in _spec(override))
    expected = groundtruth(folder).get(os.path.basename(path), {})
    out = [replace(r, groundtruth=expected.get(r.name)) for r in properties.values()]
    lemma_file = os.path.join(folder, LEMMAS_FILE)
    if lemmas and os.path.exists(lemma_file):
        for r in _spec(lemma_file):
            if not r.invariant:
                raise KindHMLError(f"{r.name} is not an invariant (a lemma is)", r.pos)
            out.append(replace(r, groundtruth=None, lemma=True))
    return tuple(out)


def _spec(path: str) -> Tuple[S.Property, ...]:
    with open(path) as f:
        return parse_spec(f.read(), path)


def groundtruth(folder: str) -> Dict[str, Dict[str, Optional[bool]]]:
    """The ground truth of a family: contract file -> property -> expected verdict (None:
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


def tasks(program: S.Program) -> List[S.Property]:
    """The properties to verify: all of them but the lemmas."""
    return [r for r in program.properties if not r.lemma]


DEFAULT_MODE = "inline"
AUTO_ORDER = tuple(os.environ.get("KINDHML_AUTO_ORDER", "cvc5,z3").split(","))
DEFAULT_EXPAND = ("address", "method")


LEMMAS = os.environ.get("KINDHML_LEMMAS", "1") != "0"


def lustre_for(program: S.Program, prop: S.Property, n_users: int, mode: str = DEFAULT_MODE,
               expand=DEFAULT_EXPAND, lemmas: bool = LEMMAS, ghost_sums: bool = False) -> str:
    """The Lustre program checking `prop`: the transition system (Init, Trans) and the
    property (∧_C constructed_C) → Φ(φ). With `lemmas`, also quantifier-free invariants of
    every system (balances are nonnegative), which Kind 2 proves first and then uses to
    strengthen the induction for the property (its invariant generator does not work on
    quantified properties). With `ghost_sums`, sum(m) is a state variable."""
    if prop not in program.properties:
        program = replace(program, properties=program.properties + (prop,))   # for its sums
    enc = Encoder(System.make(program, n_users, ghost_sums))
    prog, main = enc.program()
    if lemmas:
        main.properties += enc.lemmas()
    main.properties.append((prop.name, FormulaEncoder(enc, mode, tuple(expand)).prop(prop)))
    return prog.render()


@dataclass
class Outcome:
    prop: S.Property
    result: Optional[kind2.PropertyResult]
    errors: List[str]
    solver: str = ""
    method: str = ""                 # kind2 | invariants | inductive | reach (see verify)
    cti: str = ""                    # a free state refuting the property, possibly unreachable
    memory_killed: bool = False
    trace: str = ""                  # method fuzz: the transactions reaching the counterexample
    scope: str = ""                  # the numbers of users of the verdict, or what the run
                                     # established without one (Sect. 7.6)
    true_for: str = ""               # no verdict: the numbers of users of the proofs
                                     # ("up to 2 users and for every n >= 4 users")
    users_from: Optional[int] = None    # parameterized mode: the verdict holds for every
                                        # number of users from this one on

    @property
    def status(self) -> str:
        return self.result.status if self.result else "error"

    def groundtruth_check(self) -> str:
        gt = self.prop.groundtruth
        if gt is None:
            return "no ground truth"
        if self.status == "valid":
            return "OK" if gt else "NOT OK"
        if self.status == "invalid":
            return "NOT OK" if gt else "OK"
        if self.true_for and gt and self.status != "error":
            return f"OK-{self.true_for}"
        if self.result and self.result.true_up_to is not None and gt:
            return f"OK-up to {self.result.true_up_to}"
        return "unknown"

    def describe(self, c: Palette = PLAIN) -> str:
        """One line on the verdict (and its traces); `c` colors it for a terminal."""
        what = (self.result.describe(c) if self.result
                else c.magenta("; ".join(self.errors) or "no result"))
        if self.true_for and f"true {self.true_for}" not in self.scope:
            what += f", true {self.true_for}"
        how = "/".join(x for x in (self.method, self.solver) if x)
        how = c.dim(f" [{how}]") if how else ""
        scope = f" ({self.scope})" if self.scope else ""
        line = (f"{c.bold(self.prop.name)}: {what}{how}{scope} (ground truth:"
                f" {c.groundtruth(self.groundtruth_check())})")
        if self.trace:
            line += f"\n    {c.cyan('counterexample reached by:')} {self.trace}"
        if self.cti and self.status not in ("valid", "invalid"):
            line += (f"\n    {c.cyan('counterexample to induction')} (possibly unreachable;"
                     f" consider stronger invariants): {self.cti}")
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


# The numbers of users of a check (DESIGN.md, Sect. 7.6): "exact", the number n asked for;
# "parameterized", the cutoff of each check if it is at most n (the verdicts then hold for
# every number of users from the cutoff on); "combined" (default), both, in alternating rounds,
# until a verdict for n. The number of users ANY asks for a verdict for every n >= 1.
USERS_MODES = ("combined", "exact", "parameterized")
DEFAULT_USERS_MODE = "combined"
ANY = "any"
Users = Union[int, str]


def parse_users(text: str) -> Users:
    """A number of users (at least 1) or ANY. Raises ValueError."""
    if text == ANY:
        return ANY
    n = int(text)
    if n < 1:
        raise ValueError(f"the number of users must be at least 1, or {ANY}")
    return n


def users_mode_of(users_mode: Optional[str], parameterized: bool = False) -> str:
    """The users mode asked for: `users_mode`, else "parameterized" if `parameterized` (the
    former option), else the default."""
    mode = users_mode or ("parameterized" if parameterized else DEFAULT_USERS_MODE)
    if mode not in USERS_MODES:
        raise KindHMLError(f"unknown users mode '{mode}' (one of {', '.join(USERS_MODES)})")
    return mode


@dataclass
class _Side:
    """One number of users of the check of a property (DESIGN.md, Sect. 7.6), run in rounds
    by the generator `_rounds`."""
    users: int                       # the users of the check (the cutoff, with ghost sums)
    ghost: bool                      # sums as state variables (parameterized mode)
    goal: Optional[int]              # the users the verdict is about; None: every n >= 1
    climb: bool = False              # after a proof by Kind 2 with fewer users than goal, Kind 2
                                     # goes on with one more user (parameterized mode only)
    kind2: bool = True               # whether the side runs Kind 2 on the transition system
    search: bool = True              # whether it searches for counterexamples (reach, fuzz)
    alone: Callable[[], bool] = lambda: True    # whether Kind 2 may get all the time left
    gen: Optional[Generator] = None
    outcome: Optional[Outcome] = None


def verify(program: S.Program, prop: S.Property, n_users: Users, timeout: Optional[float],
           mode: str = DEFAULT_MODE, expand=DEFAULT_EXPAND, lus_path: Optional[str] = None,
           extra_args: Optional[List[str]] = None, solver: str = "auto",
           cex: bool = False, strategy: str = "portfolio",
           context: Optional[dict] = None, invgen: bool = True,
           user_invariants: bool = True, parameterized: bool = False,
           users_mode: Optional[str] = None) -> Outcome:
    """Check one property within `timeout` seconds (None or 0: no limit, the search goes on until
    there is a verdict), for `n_users` users, or for every number of users if `n_users` is
    ANY. With `cex`, an invalid property comes with a counterexample (slower).

    Strategy "kind2": Kind 2 on (Init, Trans) and Φ(φ) with n_users users (`kind2_search`).
    Strategy "portfolio" (default): the sides of the users mode (`users_mode_of`), each one
    number of users run by `_rounds`, advanced one round at a time in turn (`_drive_one`,
    `_drive_combined`, `_drive_any`)."""
    if context is None:
        context = {}
    users_mode = users_mode_of(users_mode, parameterized)
    if n_users == ANY and (strategy == "kind2" or users_mode == "parameterized"):
        raise KindHMLError(f"{ANY} number of users needs strategy portfolio and users mode"
                           " combined or exact")
    start = time.time()
    deadline = start + timeout if timeout else None
    if lus_path:
        users, ghost = kind2_target(context, program, prop, n_users, users_mode, mode, expand,
                                    invgen, user_invariants)
        with open(lus_path, "w") as f:
            f.write(lustre_for(program, prop, users, mode, expand, ghost_sums=ghost))
    if strategy == "kind2":
        return kind2_search(prop, lustre_for(program, prop, n_users, mode, expand),
                            timeout or None, extra_args, solver, cex)

    def side(users: int, ghost: bool, goal: Optional[int], cut: Optional[Cutoff],
             **flags) -> _Side:
        s = _Side(users, ghost, goal, **flags)
        s.gen = _rounds(program, prop, s, cut, context, start, deadline, mode, expand,
                        extra_args, solver, cex, invgen, user_invariants)
        return s

    if users_mode == "exact" and n_users != ANY:
        return _drive_one(side(n_users, False, n_users, None))
    cut = cutoff_of(context, program, mode, expand, invgen, user_invariants)
    c = cut.of_property(prop.name)
    if users_mode == "parameterized":
        ghost = c is not None and c <= n_users
        return _drive_one(side(c if ghost else n_users, ghost, n_users, cut, climb=True))
    if n_users == ANY:
        return _drive_any(program, prop, cut, c if users_mode == "combined" else None,
                          side, deadline)
    if c is None or c > n_users:
        return _drive_combined(None, side(n_users, False, n_users, None),
                               _why_exact(cut, prop, n_users))
    param = side(c, True, n_users, cut, kind2=False, search=False)
    exact = side(n_users, False, n_users, None, alone=lambda: param.outcome is not None)
    return _drive_combined(param, exact, "")


def kind2_target(context: dict, program: S.Program, prop: S.Property, n_users: Users,
                 users_mode: str, mode: str = DEFAULT_MODE, expand=DEFAULT_EXPAND,
                 invgen: bool = True, user_invariants: bool = True) -> Tuple[int, bool]:
    """The users and the ghost sums of the transition system on which Kind 2 runs first: n
    users, or the cutoff in parameterized mode, or 1 user for ANY."""
    if n_users == ANY:
        return 1, False
    if users_mode == "parameterized":
        return effective_users(context, program, n_users, mode, expand, invgen,
                               user_invariants, prop)[:2]
    return n_users, False


def _why_exact(cut: Cutoff, prop: S.Property, n_users: int) -> str:
    """Why a property is checked with n_users users only, without its cutoff: the cutoff is
    larger, or there is none."""
    c = cut.of_property(prop.name)
    return (f"cutoff {c} > {n_users}" if c is not None
            else "no cutoff: " + (cut.outside.get(prop.name) or cut.reason
                                  or "the property has no count"))


def _exact_scope(o: Outcome, n_users: int, why: str) -> str:
    """The scope of an outcome with n_users users only: a proof holds for them only (with
    the reason, if the cutoff was not used); a counterexample has n_users users; without a
    verdict, the reason."""
    if o.status == "valid":
        return f"only for {_n(n_users)}" + (f" ({why})" if why else "")
    if o.status == "invalid":
        return f"counterexample with {_n(n_users)}"
    return why


def _step(side: _Side) -> bool:
    """One round of a side; whether it has ended (its outcome is then set)."""
    try:
        next(side.gen)
        return False
    except StopIteration as e:
        side.outcome = e.value
        return True


def _decided(o: Outcome) -> bool:
    return o.status in ("valid", "invalid")


def _drive_one(side: _Side) -> Outcome:
    while not _step(side):
        pass
    return side.outcome


def _drive_combined(param: Optional[_Side], exact: _Side, why: str) -> Outcome:
    """Combined mode, n users: the parameterized side (if the property has a cutoff at most n)
    and the exact side, one round each in turn, until a verdict for n users. The
    parameterized side only proves (Houdini and the check on a free state): it ends when that
    check is refuted, and the exact side, which searches for counterexamples with n users, then
    runs alone. A proof of the parameterized side holds for n (Prop. 7.9); without a verdict,
    the outcome of the exact side."""
    sides = [s for s in (param, exact) if s is not None]
    while any(s.outcome is None for s in sides):
        for s in sides:
            if s.outcome is None and _step(s) and _decided(s.outcome):
                for t in sides:
                    if t.outcome is None:
                        t.gen.close()
                if s is exact:
                    s.outcome.scope = _exact_scope(s.outcome, exact.users, why)
                return s.outcome
    o = exact.outcome
    o.scope = why
    if param is not None:
        o.scope = f"no verdict with {_n(exact.users)}, nor with the cutoff {param.users}"
        o.cti = o.cti or param.outcome.cti
    return o


def _drive_any(program: S.Program, prop: S.Property, cut: Cutoff, c: Optional[int],
               side: Callable[..., _Side], deadline: Optional[float]) -> Outcome:
    """Every number of users n >= 1 (DESIGN.md, Sect. 7.6). The sides: with a cutoff c, the
    parameterized side P (its proofs hold for every n >= L, with L <= c) and the exact sides
    for m = 1, ..., c - 1; without a cutoff, the exact side for 1 user. While P has not proved
    the property, when all the exact sides have ended before the deadline, the exact side
    with one more user starts (best effort, for counterexamples with more users). A
    counterexample with any m users refutes the property. The property is valid if P proves
    it for every n >= L and each m < L is proved: by the exact side with m users, or, if no
    address variable is universal in the negation of the property, by any proof with M >= m
    users, P's included (Cor. 7.8). After P's proof, the exact sides with m >= L stop."""
    sides: List[_Side] = []
    exact: Dict[int, _Side] = {}
    # the numbers of users m proved, each with the users M of its proof: M = m, or M > m by
    # Cor. 7.8 (for m >= L, covered by the proof of P, M = m)
    proved: Dict[int, int] = {}
    try:
        downward = Scanner(System.make(program, 1)).idle_needed(prop.formula) == 0
    except OutOfFragment:
        downward = False

    def alone() -> bool:
        return sum(1 for s in sides if s.outcome is None) == 1

    def add(m: int):
        exact[m] = side(m, False, None, None, alone=alone)
        sides.append(exact[m])

    def cover(ms, users: Optional[int], o: Outcome) -> None:
        """The numbers of users ms are proved by `o`, a proof with `users` users (None: each
        with its own number); their exact sides stop."""
        for m in ms:
            proved.setdefault(m, m if users is None else users)
            if exact.get(m) is not None and exact[m].outcome is None:
                exact[m].gen.close()
                exact[m].outcome = o

    param = side(c, True, None, cut, kind2=False, alone=alone) if c is not None else None
    if param is not None:
        sides.append(param)
    for m in range(1, c if c is not None else 2):
        add(m)
    low = None                          # P proved every n >= low

    def close() -> None:
        for s in sides:
            if s.outcome is None:
                s.gen.close()

    while True:
        for s in [s for s in sides if s.outcome is None]:
            if s.outcome is not None or not _step(s):
                continue
            o = s.outcome
            if o.status == "invalid":
                close()
                if s is not param:
                    o.scope = f"counterexample with {_n(s.users)}"
                return o
            if o.status != "valid":
                continue
            if s is param:
                # P runs without Kind 2: its proofs, by invariants, hold from users_from on
                assert o.users_from is not None, o.describe()
                low = o.users_from
                cover([m for m in exact if m >= low], None, o)
                if downward:
                    cover(range(1, low), low, o)
            else:
                cover(range(1, s.users + 1) if downward else [s.users], s.users, o)
            if low is not None and all(m in proved for m in range(1, low)):
                close()
                v = param.outcome
                v.scope = f"n >= {low} by invariants"
                more = sorted({proved[m] for m in range(1, low) if proved[m] != m})
                own = [m for m in range(1, low) if proved[m] == m and m not in more]
                if not more:
                    v.scope += f", n < {low} one by one" if low > 1 else ""
                else:
                    v.scope += (f", n < {low} by " + (f"{_proofs(own)}, and by " if own else "")
                                + _proofs(more) + (", which holds" if len(more) == 1
                                                   else ", which hold") + " for fewer users")
                return v
        if (low is None and all(s.outcome is not None for s in exact.values())
                and (deadline is None or time.time() < deadline)):
            # the next number of users (best effort, for counterexamples with more users)
            add(max(exact, default=(c or 1) - 1) + 1)
        elif all(s.outcome is not None for s in sides):
            break
    k = 0
    while k + 1 in proved:
        k += 1
    others = [m for m in sorted(proved) if m > k and (low is None or m < low)]
    parts = (([f"up to {_n(k)}"] if k else [])
             + ([f"for {_users_list(others)}"] if others else [])
             + ([f"for every n >= {_n(low)}"] if low else []))
    # an error (of Kind 2) of a side still needed is the outcome, as with n users; not one of
    # a side covered by another proof, or of a side from the cutoff on (only best effort)
    bound = low or c
    failed = [s.outcome for m, s in exact.items() if s.outcome.status == "error"
              and m not in proved and (bound is None or m < bound)]
    errors = list(dict.fromkeys(e for f in failed for e in f.errors))
    o = Outcome(prop, None if failed else kind2.PropertyResult(prop.name, "unknown"), errors,
                true_for=" and ".join(parts))
    o.cti = next((s.outcome.cti for s in sides if s.outcome.cti), "")
    unproved = [m for m in sorted(exact) if m not in proved]
    open_ = ([f"with {_users_list(unproved)}"] if unproved else []) + \
        ([f"with the cutoff {c}"] if param is not None and low is None else [])
    o.scope = "; ".join(([f"true {o.true_for}"] if o.true_for else [])
                        + ([f"no verdict {', nor '.join(open_)}"] if open_ else []))
    return o


def _proofs(ms: List[int]) -> str:
    """"the proof with 1 user", "the proofs with 1, 3 users"."""
    return f"the proof{'' if len(ms) == 1 else 's'} with {_users_list(ms)}"


def _users_list(ms: List[int]) -> str:
    """The numbers of users ms (increasing, not empty) as ranges: "1-3, 5 users"."""
    runs: List[List[int]] = []
    for m in ms:
        if runs and m == runs[-1][-1] + 1:
            runs[-1].append(m)
        else:
            runs.append([m])
    text = ", ".join(str(r[0]) if len(r) == 1 else f"{r[0]}-{r[-1]}" for r in runs)
    return f"{text} user" if ms == [1] else f"{text} users"


def _rounds(program: S.Program, prop: S.Property, side: _Side, cut: Optional[Cutoff],
            context: dict, start: float, deadline: Optional[float], mode: str, expand,
            extra_args: Optional[List[str]], solver: str, cex: bool, invgen: bool,
            user_invariants: bool) -> Generator[None, None, Outcome]:
    """The check of a property with the users of `side`, in rounds: a generator that yields
    after each round and returns the outcome.

    Rounds of the following tasks, one Kind 2 job at a time,
    each with the round's budget (FIRST_BUDGET, doubled at each round; task 5 gets
    KIND2_SHARE budgets, or, with a time limit and linear arithmetic, all the time left):
      1. prove the invariants (`invariants.py`; shared by the properties of a run through
         `context`): those of the file (unless `user_invariants` is false) and, with
         `invgen`, the generated candidates (`invgen.py`);
      2. "invariants": check the property on a free state satisfying them; a counterexample s*
         ends this task and starts task 3;
      3. "reach": BMC search for s* in the transition system (a counterexample of the property);
      4. "fuzz": random testing, guided by s* if any, then unguided, confirmed exactly
         (`fuzz.py`);
      5. "kind2": `kind2_search`, with BMC and k-induction only after the memory limit
         killed a solver.
    An invariant proved inductive (task 1) is valid ("inductive"). Task 5 runs only if
    `side.kind2`; it gets all the time left only if `side.alone()`.

    With ghost sums (parameterized mode; DESIGN.md, Sect. 7), the side has N = max(c_H, c_R)
    users, the cutoff of the property (`effective_users`), and each task uses its own
    number of users: each step of Houdini its cutoff (the invariants then hold for every
    n >= c_H, the largest of them, `_Invariants.users`); the check of the property on a free
    state the cutoff u of its premises (the property then holds for every n >= max(c_H, u));
    the searches for counterexamples and Kind 2, N users. A counterexample holds for every
    n >= its number of users if the property has no address variable universal in its
    negation (`Scanner.dual`; the other users stay idle), or if its final state has enough
    idle users (Lemma 7.6, `Scanner.idle_needed`, `idle_users`); otherwise it says nothing
    about the `side.goal` users, and the outcome is unknown (with goal None, every n >= 1,
    any counterexample is a verdict). A proof of task 5 holds for its number of users m, and
    for every n <= m if the property has no such variable (Cor. 7.8). With `side.climb`, if
    m < goal, Kind 2 goes on with m + 1 users, up to goal, and the outcome is unknown, true
    for the numbers of users proved, until a verdict for goal; the other searches for
    counterexamples stop, since none found would extend to goal, and the check stops when
    only Kind 2 is left and it stops."""
    users, ghost, goal = side.users, side.ghost, side.goal
    # parameterized mode: the idle users a counterexample needs to extend to more users
    need = Scanner(System.make(program, users)).idle_needed(prop.formula) if ghost else 0
    dual = need > 0
    # the added users have the balance of the idle ones; 0 if a sum of the balances matters
    balance_sum = BALANCE in summed_maps(S.Program(program.contracts, (prop,),
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
        state with their balances set to 0. None if the property is not false there (exact
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
        lus = checks.concrete_check(prop, state_literal(state_from_values(out, system,
                                                                          checks.enc),
                                                        system, checks.enc))
        return out if _free_run(lus, [prop.name], CONFIRM_SECONDS)[0] == "invalid" else None

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

    def proved_for(m: int) -> str:
        """The numbers of users for which the proofs by Kind 2 with users, ..., m users hold:
        every n <= m if the property has no address variable universal in its negation (Cor.
        7.8)."""
        if not dual:
            return f"up to {_n(m)}"
        return f"for {_n(m)}" if m == users else f"for {users} to {_n(m)}"

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
            o.scope = _exact_scope(o, users, _why_exact(cut, prop, users))
            return o
        if o.status == "valid":
            if o.method in ("inductive", "invariants"):
                o.scope, o.users_from = f"for every n >= {_n(low)}", low
            else:
                o.scope = proved_for(low)
            if checked is not None and checked != low:
                o.scope += f"; property checked with {_n(checked)}"
        elif o.status == "invalid" and (why := extends(final, participants, low)) is not None:
            o.scope = f"counterexample with {_n(low)}, for every n >= {low}{why}"
            o.users_from = low
        elif o.status == "invalid" and goal is None:
            o.scope = f"counterexample with {_n(low)}"      # every n >= 1: a verdict
        elif o.status == "invalid" and low < goal:
            notes.append(f"a counterexample with {_n(low)} does not extend to {_n(goal)}:"
                         f" {idle(final, low)} idle users, {need} needed")
            o = Outcome(prop, kind2.PropertyResult(prop.name, "unknown"), o.errors, o.solver,
                        o.method, o.cti, trace=o.trace, scope=notes[-1])
        elif o.status == "invalid":
            o.scope = f"counterexample with {_n(low)}"      # low == goal: a verdict for goal
        else:
            # an outcome true for fewer users (Kind 2): what the run with more users gave
            head = (([k2_note] if k2_note else []) if o.true_for
                    else [f"no verdict with the cutoff {low}"])
            o.scope = "; ".join(head + notes[-1:])
        return o

    # Houdini once per file: with the cutoffs of its steps in parameterized mode
    invs = _entry(context, program, cut.steps if ghost else users, mode, expand, invgen,
                  user_invariants, ghost)
    nonlinear = is_nonlinear(program)
    budget = FIRST_BUDGET
    proof_open, target, engines, kind2_open = True, None, extra_args, side.kind2
    searching = side.search             # false after a proof by Kind 2 with users < goal
    k2_users = users                    # Kind 2: one more user after each such proof
    k2_lustre: Optional[str] = None     # its program, made at its first run
    k2_note = ""                        # the last run of Kind 2 after such a proof, if undecided
    target_users = users                # the users of the counterexample to induction
    guide: Optional[Dict[tuple, object]] = None     # its known values, for the fuzzer
    premises: List[List[str]] = []
    attempts: Optional[List[tuple]] = None
    last = Outcome(prop, kind2.PropertyResult(prop.name, "unknown"), [])
    while True:
        for task in ("invariants", "proof", "reach", "fuzz", "kind2"):
            # the conditions are evaluated in turn: a counterexample found by "proof" is
            # searched for by "reach" in the same round
            if not (searching or kind2_open) and invs.proved is not None and not proof_open:
                return scoped(last, users)          # no task can decide for goal
            if task == "invariants" and invs.proved is not None:
                if prop.invariant and prop.name in invs.proved:
                    return scoped(_valid(prop, "inductive", time.time() - start), invs.users)
                continue
            if task == "proof" and (invs.proved is None or not proof_open):
                continue
            if task == "reach" and not (target and searching):
                continue
            if task == "fuzz" and not searching:
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
                # rounds go on; so do they if other sides have their rounds.
                b = KIND2_SHARE * budget
                if left is not None:
                    b = min(b, left) if nonlinear or not side.alone() else left
            if task == "invariants":
                invs.attempt(b)
                if invs.proved is not None and prop.invariant and prop.name in invs.proved:
                    return scoped(_valid(prop, "inductive", time.time() - start), invs.users)
            elif task == "proof":
                # forms to try: for each premise, from the smallest, the property as one
                # Kind 2 property
                # and split into cases; a counterexample under the last premise (the
                # strongest) is the state searched for by "reach"
                if attempts is None:
                    premises = invs.checks.premises(prop, invs.assumed())
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
                    u = max(1, invs.checks.property_count(premises[i], prop)) if ghost else users
                    lus, names = invs.checks_for(u).property_check(prop, premises[i], split)
                    status, refuted, s = _free_run(lus, names, b)
                    if status == "valid":
                        return scoped(_valid(prop, "invariants", time.time() - start, s),
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
                            known: set = set()
                            enc = invs.checks_for(u).enc
                            st = state_from_values({p: python_constant(v)
                                                    for p, v in target.items()},
                                                   enc.system, enc, known=known)
                            have = locations(st)
                            guide = {loc: have[loc] for loc in known if loc in have} or None
                            break
            elif task == "fuzz":
                deadline_fuzz = time.time() + b
                # first towards the counterexample to induction, if any, then at random; each
                # search gets half of the time left, its confirmations the rest
                searches = ([(target_users, lambda f, t: f.guided(prop, guide, t))]
                            if guide else []) + [(users, lambda f, t: f.candidates(prop, t))]
                for m, search in searches:
                    checks = invs.checks_for(m)
                    share = (deadline_fuzz - time.time()) / 2
                    for txs, st in search(invs.fuzzer_for(m), share):
                        left = deadline_fuzz - time.time()
                        if left <= 1:
                            break
                        lus = checks.concrete_check(
                            prop, state_literal(st, checks.enc.system, checks.enc))
                        status, _, s = _free_run(lus, [prop.name], left)
                        if status == "invalid":
                            res = kind2.PropertyResult(prop.name, "invalid", len(txs), "fuzz",
                                                       time.time() - start)
                            named = {x for tx in txs for x in [tx.sender, tx.contract]
                                     + [v for v in tx.args.values() if isinstance(v, str)]}
                            o = scoped(Outcome(prop, res, [], s, "fuzz",
                                               trace="; ".join(describe_tx(tx) for tx in txs)),
                                       m, final=state_paths(st, checks.enc.system),
                                       participants=named)
                            if o.status == "invalid":
                                return o
                            o.cti, last = last.cti, o       # it does not extend: go on
            elif task == "reach":
                lus = invs.checks_for(target_users).reach_check(target)
                # a property that needs idle users needs the whole final state (the target may
                # leave out values, e.g. balances that the property does not read)
                out = kind2.run(lus, b, solver="z3", extra_args=["--enable", "BMC"],
                                cex=cex or dual)
                res = next((p for p in out.properties if p.name == "unreachable"), None)
                if res and res.status == "invalid":
                    res.name, res.time = prop.name, time.time() - start
                    final = (final_values(res.counterexample) if res.counterexample
                             else {p: python_constant(v) for p, v in target.items()})
                    o = scoped(Outcome(prop, res, out.errors, "z3", "reach", last.cti),
                               target_users, final=final,
                               participants=(_participants(res.counterexample,
                                                           invs.checks_for(target_users)
                                                           .enc.system)
                                             if res.counterexample else None))
                    if o.status == "invalid":
                        return o
                    target, last = None, o              # it does not extend: go on
            else:
                if k2_lustre is None:
                    k2_lustre = lustre_for(program, prop, k2_users, mode, expand,
                                           ghost_sums=ghost)
                o = kind2_search(prop, k2_lustre, b, engines, solver, cex)
                if o.status == "valid" and side.climb and k2_users < goal:
                    # a proof for k2_users users, not for goal (Kind 2's invariants name
                    # the users): Kind 2 goes on with one more user. No counterexample with
                    # at most k2_users users extends to goal (it would extend to
                    # k2_users), so the other searches stop
                    searching, k2_note = False, ""
                    last = Outcome(prop, kind2.PropertyResult(prop.name, "unknown"),
                                   o.errors, o.solver, "kind2", last.cti,
                                   true_for=proved_for(k2_users))
                    k2_users += 1
                    k2_lustre = lustre_for(program, prop, k2_users, mode, expand,
                                           ghost_sums=ghost)
                    continue
                if o.status in ("valid", "invalid"):
                    o.method = "kind2"
                    final, named = None, None
                    if o.status == "invalid" and dual:
                        # without the lemmas, which BMC cannot prove: Kind 2 then stops at
                        # the counterexample instead of the time limit
                        bare = lustre_for(program, prop, k2_users, mode, expand,
                                          lemmas=False, ghost_sums=ghost)
                        final, named = _final_state(o, bare, b, deadline,
                                                    System.make(program, k2_users))
                    cti = o.cti or last.cti
                    o = scoped(o, k2_users, final=final, participants=named)
                    if o.status == "invalid" and last.true_for:
                        o.scope += f"; true {last.true_for}"   # the proofs with fewer users
                    if o.status in ("valid", "invalid"):
                        return o
                    # it does not extend, and BMC would find it again: go on without Kind 2
                    o.cti, o.true_for, last, kind2_open = cti, last.true_for, o, False
                    continue
                if o.memory_killed and engines is None:
                    engines = LIGHT_ENGINES
                if last.true_for:
                    # the proofs with fewer users are kept; this run is in the scope
                    up_to = o.result.true_up_to if o.result else None
                    k2_note = (f"with {_n(k2_users)}: " + ("no verdict" if up_to is None
                               else f"true up to {up_to} steps"))
                    continue
                o.method, o.cti = "kind2", last.cti
                last = o
        yield                               # the end of a round: the other sides go on
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
    """The final state of the counterexample of a refuted property (Kind 2 on the transition
    system), by path, and the users its transactions name: from its counterexample if it
    has one, else from a run of BMC with counterexamples (z3, with the budget, but at least
    CONFIRM_SECONDS, also after the deadline); None if there is none."""
    cex = o.result.counterexample if o.result else None
    if not cex:
        left = None if deadline is None else deadline - time.time()
        out = kind2.run(lustre, max(budget if left is None else min(budget, left),
                                    CONFIRM_SECONDS),
                        solver="z3", extra_args=["--enable", "BMC"], cex=True)
        res = next((p for p in out.properties if p.name == o.prop.name), None)
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
                    prop: Optional[S.Property] = None) -> Tuple[int, bool, Cutoff]:
    """Parameterized mode: a number of users c, whether sums are state variables, and the
    cutoffs of the checks on free values (`Checks.cutoff`, with all the templates of `invgen`
    and the invariants of the file as candidates: those that survive give smaller cutoffs).
    c is the cutoff of the steps of Houdini c_H or, for `prop`, max(c_H, its cutoff c_R).
    If c <= n_users: c, with sums as state variables; otherwise (or without a cutoff):
    n_users, as without parameterized mode."""
    cut = cutoff_of(context, program, mode, expand, invgen, user_invariants)
    c = cut.steps if prop is None else cut.of_property(prop.name)
    if c is None or n_users < c:
        return n_users, False, cut
    return c, True, cut


def cutoff_of(context: dict, program: S.Program, mode: str, expand, invgen: bool,
              user_invariants: bool) -> Cutoff:
    """The cutoffs of the checks of `program` on free values (`effective_users`), computed once
    per run (in `context`)."""
    key = ("cutoff", id(program), invgen, user_invariants)
    if key not in context:
        templates = invariant_templates(program) if invgen else []
        extended = S.Program(program.contracts,
                             _with_candidates(program, user_invariants) + tuple(templates),
                             program.balance_type)
        # every property, also the lemmas and the invariants, which can be checked by name
        context[key] = Checks(extended, 1, mode, expand,
                              ghost_sums=True).cutoff(list(program.properties))
    return context[key]


def _with_candidates(program: S.Program, user_invariants: bool) -> Tuple[S.Property, ...]:
    """The properties of `program`; without `user_invariants`, its invariants as properties,
    which are then no candidates of Houdini, but still in the program of the encoder (their
    sums have state variables, in parameterized mode)."""
    return tuple(r if user_invariants or not r.invariant else replace(r, invariant=False)
                 for r in program.properties)


def prove_invariants(program: S.Program, n_users: Users, timeout: Optional[float],
                     context: dict, mode: str = DEFAULT_MODE, expand=DEFAULT_EXPAND,
                     invgen: bool = True, user_invariants: bool = True,
                     parameterized: bool = False,
                     users_mode: Optional[str] = None) -> List["_Invariants"]:
    """The invariant phase of a file, before its properties, with its own time limit (None: no
    limit): candidates (declared and generated) and Houdini, in passes with doubling
    budgets, until the inductive subset is found. The properties of the file then use it through
    `context`; if the phase does not finish, `verify` goes on with it in its rounds. Without
    a separate phase, Houdini shared the time of each property with the other tasks, and on the
    lending protocol it did not finish within the 11 properties of 60 s.

    One Houdini for each number of users of the users mode (`users_mode_of`), its passes in
    turn, parameterized first: exact, n users; parameterized, the cutoff of the steps c_H if
    at most n (`effective_users`), else n; combined, both (the cutoff if at most n); ANY, the
    cutoff and 1, ..., c_H - 1 users (1 without a cutoff; `verify` makes the others)."""
    users_mode = users_mode_of(users_mode, parameterized)
    entries: List[_Invariants] = []

    def add(users: int, ghost: bool, cut: Optional[Cutoff] = None):
        invs = _entry(context, program, users, mode, expand, invgen, user_invariants, ghost)
        invs.cutoff = cut
        entries.append(invs)

    if users_mode == "exact" and n_users != ANY:
        add(n_users, False)
    else:
        cut = cutoff_of(context, program, mode, expand, invgen, user_invariants)
        c = cut.steps
        ghost = (c is not None and users_mode != "exact"
                 and (n_users == ANY or c <= n_users))
        if ghost:
            add(c, True, cut)
        if n_users == ANY:
            for m in range(1, c if ghost else 2):
                add(m, False)
        elif users_mode == "combined" or not ghost:
            add(n_users, False, None if ghost or users_mode == "combined" else cut)
    deadline = time.time() + timeout if timeout else None
    b = FIRST_BUDGET
    pending = list(entries)
    while pending:
        for invs in pending:
            left = None if deadline is None else deadline - time.time()
            if left is not None and left <= 1:
                return entries
            invs.attempt(b if left is None else min(b, left))
        pending = [invs for invs in pending if invs.proved is None]
        b *= 2
    return entries


def kind2_search(prop: S.Property, lustre: str, timeout: Optional[float],
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
        result = next((p for p in out.properties if p.name == prop.name), None)
        if result is None and (out.timed_out or out.memory_killed):
            # Kind 2 stopped at a limit before reporting on the property (e.g. at its time
            # limit while parsing a large program): no verdict, not an error
            result = kind2.PropertyResult(prop.name, "unknown")
        outcome = Outcome(prop, result, out.errors, s, "kind2")
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


def _valid(prop: S.Property, method: str, elapsed: float, solver: str = "") -> Outcome:
    return Outcome(prop, kind2.PropertyResult(prop.name, "valid", None, method, elapsed), [],
                   solver, method)


def _free_run(lustre: str, names: List[str], budget: float):
    """A check on free values, with properties `names` (the cases of a property), with
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
        generated: List[S.Property] = []
        keys: Dict[str, tuple] = {}
        if invgen:
            generated, _, keys = generate_invariants(
                program, Fuzzer(System.make(program, n_users)), INVGEN_SECONDS)
        extended = S.Program(program.contracts,
                             _with_candidates(program, user_invariants) + tuple(generated),
                             program.balance_type)
        invs = _Invariants(Checks(extended, n_users, mode, expand, ghost_sums),
                           {r.name for r in generated})
        invs.keys = {r.name: keys[r.name] for r in generated}
        return invs

    def assumed(self) -> List[str]:
        """The proved invariants that the checks of the properties assume: all of them, but the
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
        with more than 1 s left, as the checks of `verify`):
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
                if left <= 1:
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
                if left <= 1:
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


def invariant_summary(invs: "_Invariants", c: Palette = PLAIN) -> str:
    """One line: how many candidates (declared, generated) were proved, and dropped; in
    parameterized mode, also the cutoff and the number of users of the checks."""
    users = ""
    if invs.cutoff is not None:
        users = f"; {invs.cutoff.describe()}"
        if invs.parameterized and invs.proved is not None:
            users += f"; invariants for every n >= {_n(invs.users)}"
    if invs.proved is None:
        return (f"invariants: {c.yellow('not proved within the time')}"
                f" ({len(invs.candidates)} candidates"
                f" left, {len(invs.dropped)} dropped){users}")
    proved = [n for n in invs.proved if n not in invs.checks.axioms]
    gen = sum(1 for n in proved if n in invs.generated)
    return (f"invariants: {c.green(f'{len(proved)} proved')} ({len(proved) - gen} declared, {gen}"
            f" generated), {len(invs.dropped)} dropped{users}")


def invariant_label(invs: "_Invariants") -> str:
    """The numbers of users of a Houdini: "parameterized" (from its cutoff on), or n users."""
    return "parameterized" if invs.parameterized else f"with {_n(invs.checks.enc.system.n_users)}"


def invariant_report(context: dict) -> List[str]:
    """The invariants proved for the programs of a run (generated or declared), and the
    number of candidates dropped; with several numbers of users, each line is labelled."""
    entries = [invs for invs in context.values() if isinstance(invs, _Invariants)]
    lines = []
    for invs in entries:
        head = f"({invariant_label(invs)}) " if len(entries) > 1 else ""
        if invs.proved is None:
            lines.append(f"{head}invariants: not proved within the time")
            continue
        for n in invs.proved:
            if n not in invs.checks.axioms:
                kind = "generated" if n in invs.generated else "declared"
                lines.append(f"{head}{kind} invariant {n}: "
                             f"{pretty.expr(invs.checks.program.prop(n).formula)}")
        lines.append(f"{head}candidates dropped by Houdini: {len(invs.dropped)}")
    return lines


def select_properties(program: S.Program, name: str) -> List[S.Property]:
    if name == "ALL":
        return tasks(program)
    prop = program.prop(name)
    if prop is None:
        raise KindHMLError(f"no property named '{name}' (properties: "
                           f"{', '.join(r.name for r in program.properties)})")
    return [prop]


def stem(path: str) -> str:
    return os.path.splitext(os.path.basename(path))[0]
