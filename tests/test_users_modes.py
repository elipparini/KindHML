"""The users modes (DESIGN.md, Sect. 7.6): the drivers of the sides, with scripted sides
(no Kind 2)."""

import os
import time
from dataclasses import replace

import pytest

from kindhml import kind2
from kindhml import verify as V

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REGISTRY = os.path.join(ROOT, "tests", "contracts", "parameterized", "registry.sol")
PROGRAM, _ = V.load(REGISTRY)
UNIVERSAL = PROGRAM.prop("Registered_bounded")       # no address variable universal in ¬φ
CAPPED, _ = V.load(os.path.join(ROOT, "tests", "contracts", "parameterized",
                                "capped_registry.sol"))
EXISTENTIAL = CAPPED.prop("Someone_unregistered")    # need(¬φ) = 1: no Cor. 7.8
PAST = time.time() - 1                               # a deadline already passed


def outcome(status: str, method: str = "", users_from=None, scope: str = "",
            prop=UNIVERSAL) -> V.Outcome:
    o = V.Outcome(prop, kind2.PropertyResult(prop.name, status), [], method=method,
                  scope=scope)
    o.users_from = users_from
    return o


def scripted(rounds: int, o: V.Outcome):
    """A side that ends with `o` after `rounds` rounds."""
    for _ in range(rounds):
        yield
    return o


def make(users, ghost, goal, rounds, o, **flags) -> V._Side:
    s = V._Side(users, ghost, goal, **flags)
    s.gen = scripted(rounds, o)
    return s


def test_parse_users():
    assert V.parse_users("3") == 3
    assert V.parse_users("any") == V.ANY
    for bad in ("0", "-1", "x"):
        with pytest.raises(ValueError):
            V.parse_users(bad)


def test_users_mode_of():
    assert V.users_mode_of(None) == "combined"
    assert V.users_mode_of(None, parameterized=True) == "parameterized"
    assert V.users_mode_of("exact", parameterized=True) == "exact"


def test_combined_first_verdict_wins():
    param = make(2, True, 5, 1, outcome("valid", "invariants", 2, "for every n >= 2 users"))
    exact = make(5, False, 5, 3, outcome("valid", "kind2"))
    o = V._drive_combined(param, exact, "")
    assert (o.status, o.scope) == ("valid", "for every n >= 2 users")
    param = make(2, True, 5, 3, outcome("unknown"))
    exact = make(5, False, 5, 1, outcome("invalid", "fuzz"))
    o = V._drive_combined(param, exact, "")
    assert (o.status, o.scope) == ("invalid", "counterexample with 5 users")


def test_combined_without_verdict():
    """Without a verdict: the outcome of the exact side; the scope names both sides."""
    param = make(2, True, 5, 1, outcome("unknown"))
    exact = make(5, False, 5, 2, outcome("unknown", "kind2"))
    o = V._drive_combined(param, exact, "")
    assert o.status == "unknown" and o.method == "kind2"
    assert o.scope == "no verdict with 5 users, nor with the cutoff 2"
    exact = make(5, False, 5, 0, outcome("unknown", "kind2"))
    assert V._drive_combined(None, exact, "cutoff 7 > 5").scope == "cutoff 7 > 5"


def test_combined_without_the_cutoff():
    """A cutoff larger than n: a verdict holds for n users only, with the reason."""
    exact = make(5, False, 5, 1, outcome("valid", "kind2"))
    o = V._drive_combined(None, exact, "cutoff 7 > 5")
    assert (o.status, o.scope) == ("valid", "only for 5 users (cutoff 7 > 5)")


def any_mode(script, c, deadline=PAST, prop=UNIVERSAL):
    """`_drive_any` with the sides of `script`: (users, ghost) -> (rounds, outcome); the
    sides made, in order."""
    program = CAPPED if prop.name == EXISTENTIAL.name else PROGRAM
    made = []

    def side(users, ghost, goal, cut, **flags):
        assert goal is None
        rounds, o = script[(users, ghost)]
        made.append((users, ghost))
        return make(users, ghost, goal, rounds, o, **flags)

    return V._drive_any(program, prop, None, c, side, deadline), made


def test_any_valid():
    """A proof for every n >= L, and proofs with each m < L users."""
    script = {(3, True): (0, outcome("valid", "invariants", 3)),
              (1, False): (1, outcome("valid", "invariants")),
              (2, False): (2, outcome("valid", "invariants"))}
    o, made = any_mode(script, 3, prop=EXISTENTIAL)
    assert o.status == "valid", o.describe()
    assert o.scope == "n >= 3 by invariants, n < 3 one by one"
    assert made == [(3, True), (1, False), (2, False)]
    o, _ = any_mode({(1, True): (0, outcome("valid", "invariants", 1))}, 1)
    assert (o.status, o.scope) == ("valid", "n >= 1 by invariants")


def test_any_parameterized_proof_holds_for_fewer_users():
    """Cor. 7.8: with no address variable universal in ¬φ, the proof for every n >= L holds
    with L users, hence for every m < L: valid at once, the exact sides stop."""
    script = {(3, True): (0, outcome("valid", "invariants", 3)),
              (1, False): (9, outcome("unknown")),
              (2, False): (9, outcome("unknown"))}
    o, made = any_mode(script, 3)
    assert (o.status, o.method) == ("valid", "invariants"), o.describe()
    assert o.scope == ("n >= 3 by invariants, n < 3 by the proof with 3 users, which holds"
                       " for fewer users")


def test_any_sides_from_the_proof_bound_stop():
    """P proves every n >= 2 with the cutoff 4: the exact sides for 2 and 3 users are no
    longer needed, only the one for 1 user."""
    script = {(4, True): (0, outcome("valid", "invariants", 2)),
              (1, False): (2, outcome("valid", "invariants")),
              (2, False): (9, outcome("unknown")),
              (3, False): (9, outcome("unknown"))}
    o, _ = any_mode(script, 4, prop=EXISTENTIAL)
    assert (o.status, o.scope) == ("valid", "n >= 2 by invariants, n < 2 one by one")
    script[(1, False)] = (2, outcome("unknown"))
    o, _ = any_mode(script, 4, prop=EXISTENTIAL)
    assert o.status == "unknown"
    assert o.scope == "true for every n >= 2 users; no verdict with 1 user"


def test_any_counterexample_with_more_users():
    """The required sides are proved, the parameterized side is not: the exact sides go on
    with more users (best effort), and a counterexample with 3 users refutes the property."""
    script = {(2, True): (5, outcome("unknown")),
              (1, False): (0, outcome("valid", "invariants")),
              (2, False): (0, outcome("valid", "invariants")),
              (3, False): (0, outcome("invalid", "fuzz"))}
    o, made = any_mode(script, 2, deadline=None)
    assert (o.status, o.scope) == ("invalid", "counterexample with 3 users")
    assert made == [(2, True), (1, False), (2, False), (3, False)]


def test_any_without_verdict():
    script = {(4, True): (0, outcome("valid", "invariants", 4)),
              (1, False): (0, outcome("valid", "invariants")),
              (2, False): (0, outcome("valid", "invariants")),
              (3, False): (1, outcome("unknown"))}
    o, _ = any_mode(script, 4, prop=replace(EXISTENTIAL, groundtruth=True))
    assert o.status == "unknown"
    assert o.true_for == "up to 2 users and for every n >= 4 users"
    assert o.groundtruth_check() == "OK-up to 2 users and for every n >= 4 users"
    assert o.scope == ("true up to 2 users and for every n >= 4 users;"
                       " no verdict with 3 users")
    script = {(4, True): (1, outcome("unknown")),
              (1, False): (0, outcome("unknown")),
              (2, False): (0, outcome("valid", "invariants")),
              (3, False): (1, outcome("unknown"))}
    o, _ = any_mode(script, 4, prop=EXISTENTIAL)
    assert o.status == "unknown"
    assert o.true_for == "for 2 users"
    assert o.scope == "true for 2 users; no verdict with 1, 3 users, nor with the cutoff 4"


def test_any_error_of_a_side():
    """An error of a side still needed (Kind 2), without a verdict, is the outcome, with its
    message; not one of a side whose number of users is proved otherwise."""
    failed = V.Outcome(EXISTENTIAL, None, ["Kind 2 failed"])
    script = {(2, True): (0, outcome("unknown")), (1, False): (0, failed)}
    o, _ = any_mode(script, 2, prop=replace(EXISTENTIAL, groundtruth=True))
    assert (o.status, o.errors) == ("error", ["Kind 2 failed"])
    assert o.scope == "no verdict with 1 user, nor with the cutoff 2"
    script = {(3, True): (0, outcome("valid", "invariants", 2)),
              (1, False): (1, outcome("unknown")), (2, False): (0, failed)}
    o, _ = any_mode(script, 3, prop=replace(EXISTENTIAL, groundtruth=True))
    assert o.status == "unknown", o.describe()
    assert o.groundtruth_check() == "OK-for every n >= 2 users"


def test_any_mixed_proofs():
    """m = 1 by its own proof, m = 2 by the proof with 3 users (Cor. 7.8)."""
    script = {(4, True): (3, outcome("valid", "invariants", 4)),
              (1, False): (0, outcome("valid", "invariants")),
              (2, False): (9, outcome("unknown")),
              (3, False): (1, outcome("valid", "kind2"))}
    o, _ = any_mode(script, 4)
    assert o.status == "valid", o.describe()
    assert o.scope == ("n >= 4 by invariants, n < 4 by the proof with 1 user, and by the"
                       " proof with 3 users, which holds for fewer users")


def test_users_list():
    assert V._users_list([1]) == "1 user"
    assert V._users_list([1, 2, 3, 5]) == "1-3, 5 users"


def test_any_exact_proof_holds_for_fewer_users():
    """Cor. 7.8: with no address variable universal in ¬φ, a proof with m users, by Kind 2
    or by invariants, holds for every m' <= m; not otherwise."""
    for method in ("kind2", "invariants"):
        script = {(3, True): (9, outcome("unknown")),
                  (1, False): (9, outcome("unknown")),
                  (2, False): (0, outcome("valid", method))}
        o, _ = any_mode(script, 3)
        assert (o.status, o.true_for) == ("unknown", "up to 2 users"), o.describe()
        o, _ = any_mode(script, 3, prop=EXISTENTIAL)
        assert (o.status, o.true_for) == ("unknown", "for 2 users"), o.describe()


def test_any_lone_side_gets_the_time_left():
    """Kind 2 gets all the time left only on a side alone: the exact side with 1 user, after
    the parameterized side has ended."""
    seen = []

    def recording(s, rounds, o):
        for _ in range(rounds):
            seen.append((s.users, s.ghost, s.alone()))
            yield
        return o

    def side(users, ghost, goal, cut, **flags):
        s = V._Side(users, ghost, goal, **flags)
        s.gen = (recording(s, 1, outcome("unknown")) if ghost
                 else recording(s, 3, outcome("valid", "invariants")))
        return s

    V._drive_any(PROGRAM, UNIVERSAL, None, 2, side, PAST)
    assert seen == [(2, True, False), (1, False, False), (1, False, True), (1, False, True)]


def test_kind2_target():
    prop = PROGRAM.prop("At_most_two")
    args = (V.DEFAULT_MODE, V.DEFAULT_EXPAND)
    assert V.kind2_target({}, PROGRAM, prop, 5, "combined", *args) == (5, False)
    assert V.kind2_target({}, PROGRAM, prop, 5, "exact", *args) == (5, False)
    assert V.kind2_target({}, PROGRAM, prop, 5, "parameterized", *args) == (2, True)
    assert V.kind2_target({}, PROGRAM, prop, V.ANY, "combined", *args) == (1, False)
