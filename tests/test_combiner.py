"""The serial drivers of the sides against the drivers before the combiners (2026-11-06, kept
here as the reference): the same outcomes and the same sides on random scripts (no Kind 2)."""

import random
from typing import Callable, Dict, List, Optional

import pytest

from kindhml import kind2
from kindhml import verify as V
from test_users_modes import CAPPED, EXISTENTIAL, PROGRAM, UNIVERSAL, make, outcome


# ------------------------------------------------------------------ the drivers before

def old_drive_combined(param: Optional[V._Side], exact: V._Side, why: str) -> V.Outcome:
    """Combined mode, n users: the parameterized side (if the property has a cutoff at most n)
    and the exact side, one round each in turn, until a verdict for n users. The
    parameterized side only proves (Houdini and the check on a free state): it ends when that
    check is refuted, and the exact side, which searches for counterexamples with n users, then
    runs alone. A proof of the parameterized side holds for n (Prop. 7.9); without a verdict,
    the outcome of the exact side."""
    sides = [s for s in (param, exact) if s is not None]
    while any(s.outcome is None for s in sides):
        for s in sides:
            if s.outcome is None and V._step(s) and V._decided(s.outcome):
                for t in sides:
                    if t.outcome is None:
                        t.gen.close()
                if s is exact:
                    s.outcome.scope = V._exact_scope(s.outcome, exact.users, why)
                return s.outcome
    o = exact.outcome
    o.scope = why
    if param is not None:
        o.scope = f"no verdict with {V._n(exact.users)}, nor with the cutoff {param.users}"
        o.cti = o.cti or param.outcome.cti
    return o


def old_drive_any(program, prop, cut, c: Optional[int],
               side: Callable[..., V._Side], deadline: Optional[float],
               wit: Optional[V._Side] = None) -> V.Outcome:
    """Every number of users n >= 1 (DESIGN.md, Sect. 7.6). The sides: with a cutoff c, the
    parameterized side P (its proofs hold for every n >= L, with L <= c) and the exact sides
    for m = 1, ..., c - 1; without a cutoff, the exact side for 1 user. While P has not proved
    the property, when all the exact sides have ended before the deadline, the exact side
    with one more user starts (best effort, for counterexamples with more users). A
    counterexample with any m users refutes the property. The property is valid if P proves
    it for every n >= L and each m < L is proved: by the exact side with m users, or, if no
    address variable is universal in the negation of the property, by any proof with M >= m
    users, P's included (Cor. 7.8). After P's proof, the exact sides with m >= L stop. The
    side `wit`, if any, proves instances of an existential over a method (`_witness_rounds`):
    its proof holds for every n."""
    sides: List[V._Side] = []
    exact: Dict[int, V._Side] = {}
    # the numbers of users m proved, each with the users M of its proof: M = m, or M > m by
    # Cor. 7.8 (for m >= L, covered by the proof of P, M = m)
    proved: Dict[int, int] = {}
    try:
        downward = V.Scanner(V.System.make(program, 1)).idle_needed(prop.formula) == 0
    except V.OutOfFragment:
        downward = False

    def alone() -> bool:
        return sum(1 for s in sides if s.outcome is None) == 1

    def add(m: int):
        exact[m] = side(m, False, None, None, alone=alone)
        sides.append(exact[m])

    def cover(ms, users: Optional[int], o: V.Outcome) -> None:
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
    if wit is not None:
        sides.append(wit)
    for m in range(1, c if c is not None else 2):
        add(m)
    low = None                          # P proved every n >= low

    def close() -> None:
        for s in sides:
            if s.outcome is None:
                s.gen.close()

    while True:
        for s in [s for s in sides if s.outcome is None]:
            if s.outcome is not None or not V._step(s):
                continue
            o = s.outcome
            if o.status == "invalid":
                close()
                if s is not param:
                    o.scope = f"counterexample with {V._n(s.users)}"
                return o
            if o.status != "valid":
                continue
            if s is wit:
                close()
                return o
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
                    v.scope += (f", n < {low} by " + (f"{V._proofs(own)}, and by " if own else "")
                                + V._proofs(more) + (", which holds" if len(more) == 1
                                                   else ", which hold") + " for fewer users")
                return v
        if (low is None and all(s.outcome is not None for s in exact.values())
                and (deadline is None or V.time.time() < deadline)):
            # the next number of users (best effort, for counterexamples with more users)
            add(max(exact, default=(c or 1) - 1) + 1)
        elif all(s.outcome is not None for s in sides):
            break
    k = 0
    while k + 1 in proved:
        k += 1
    others = [m for m in sorted(proved) if m > k and (low is None or m < low)]
    parts = (([f"up to {V._n(k)}"] if k else [])
             + ([f"for {V._users_list(others)}"] if others else [])
             + ([f"for every n >= {V._n(low)}"] if low else []))
    # an error (of Kind 2) of a side still needed is the outcome, as with n users; not one of
    # a side covered by another proof, or of a side from the cutoff on (only best effort)
    bound = low or c
    failed = [s.outcome for m, s in exact.items() if s.outcome.status == "error"
              and m not in proved and (bound is None or m < bound)]
    errors = list(dict.fromkeys(e for f in failed for e in f.errors))
    o = V.Outcome(prop, None if failed else kind2.PropertyResult(prop.name, "unknown"), errors,
                true_for=" and ".join(parts))
    o.cti = next((s.outcome.cti for s in sides if s.outcome.cti), "")
    unproved = [m for m in sorted(exact) if m not in proved]
    open_ = ([f"with {V._users_list(unproved)}"] if unproved else []) + \
        ([f"with the cutoff {c}"] if param is not None and low is None else [])
    o.scope = "; ".join(([f"true {o.true_for}"] if o.true_for else [])
                        + ([f"no verdict {', nor '.join(open_)}"] if open_ else []))
    return o




# ------------------------------------------------------------------ random scripts

class FakeTime:
    """A clock that advances by one at each reading: the deadline allows a fixed number of
    readings, the same in both drivers (they read it in the same conditions)."""

    def __init__(self):
        self.now = 0.0

    def time(self):
        self.now += 1
        return self.now


def plan(rnd: random.Random, c: Optional[int], wit: bool):
    """For each side, (rounds, status, users_from), drawn on first use from a generator
    seeded by the side (the same in both drivers, whatever the order of the sides)."""
    base = rnd.random()
    statuses = ["valid", "invalid", "unknown", "unknown", "error"]

    def get(key):
        r = random.Random(f"{base}:{key}")
        if key == "wit":
            return r.randrange(8), r.choice(["valid", "unknown"]), None
        users, ghost = key
        if ghost:
            st = r.choice(["valid", "valid", "unknown", "invalid"])
            return r.randrange(5), st, (r.randint(1, users) if st == "valid" else None)
        return r.randrange(5), r.choice(statuses), None

    get.wit = wit
    return get


def run(driver, p: dict, c, deadline_steps, prop, monkeypatch):
    program = CAPPED if prop.name == EXISTENTIAL.name else PROGRAM
    clock = FakeTime()
    monkeypatch.setattr(V, "time", clock)
    made = []

    def build(key, users, ghost, goal, **flags):
        rounds, st, users_from = p(key)
        o = outcome(st, "m", users_from, prop=prop)
        if st == "unknown":
            o.cti = f"cti of {key}"
        if st == "error":
            o.errors.append(f"error of {key}")
        return make(users, ghost, goal, rounds, o, **flags)

    def side(users, ghost, goal, cut, **flags):
        made.append((users, ghost))
        return build((users, ghost), users, ghost, goal, **flags)

    wit = build("wit", 1, True, None, kind2=False, search=False, prop=prop) if p.wit else None
    o = driver(program, prop, None, c, side, deadline_steps, wit)
    return (o.status, o.scope, o.true_for, o.method, o.cti, list(o.errors)), made


@pytest.mark.parametrize("seed", range(10))
def test_the_combiner_drives_as_before(seed, monkeypatch):
    rnd = random.Random(f"combiner:{seed}")
    statuses, best_effort = set(), 0
    for _ in range(100):
        c = rnd.choice([None, 1, 2, 3, 4])
        prop = rnd.choice([UNIVERSAL, EXISTENTIAL])
        p = plan(rnd, c, rnd.random() < 0.3)
        deadline = rnd.choice([0, 5, 20, 60])
        old = run(old_drive_any, p, c, deadline, prop, monkeypatch)
        new = run(V._drive_any, p, c, deadline, prop, monkeypatch)
        assert old == new, (c, prop.name, deadline)
        statuses.add(new[0][0])
        best_effort += sum(1 for users, ghost in new[1] if not ghost and users >= (c or 2))
    # the scripts reach every kind of outcome, and sides with more users
    assert statuses == {"valid", "invalid", "unknown", "error"}, statuses
    assert best_effort > 0


@pytest.mark.parametrize("seed", range(3))
def test_the_combined_mode_drives_as_before(seed):
    rnd = random.Random(f"combined:{seed}")
    for _ in range(100):
        outs, seed_ = [], rnd.random()
        for driver in (old_drive_combined, V._drive_combined):
            r = random.Random(seed_)
            with_param = r.random() < 0.7
            param = make(2, True, 5, r.randrange(4), outcome(
                r.choice(["valid", "unknown"]), "invariants", 2)) if with_param else None
            exact = make(5, False, 5, r.randrange(4), outcome(
                r.choice(["valid", "invalid", "unknown"]), "kind2"))
            o = driver(param, exact, r.choice(["", "cutoff 7 > 5"]))
            outs.append((o.status, o.scope, o.method, o.cti))
        assert outs[0] == outs[1]
