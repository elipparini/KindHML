"""End-to-end regression tests: each property of contracts/regression and tests/contracts must
match its ground truth within a small timeout, for every number of users (the default of the
tool), or for the number of users of the option --users (e.g. `--users 2`). Runs Kind 2 (one
job at a time); select with -m kind2.

Properties listed in OPEN are known not to match yet; each entry says why. Those listed in
OPEN_ANY are known not to match for every number of users only, and those of LONGER_ANY get
more time for every number of users.
"""

import glob
import os

import pytest

from kindhml import verify as V

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# With the default solver strategy, z3 gets the second half of it; some properties need z3 for
# about 10 s (calls Relay_never_reverts, with three contracts).
TIMEOUT = 30
DIRS = [os.path.join(ROOT, "contracts", "regression"), os.path.join(ROOT, "tests", "contracts")]

OPEN = {
    ("division", "P1_true"): "nonlinear witness; unknown within the timeout",
    ("two-donatees", "P2_true"): "needs an auxiliary invariant; unknown within the timeout",
    ("two-donatees", "P4_true"): "needs an auxiliary invariant; unknown within the timeout",
    ("two-donatees", "P2b_true"): "valid by IC3 with z3 in about 30 s: at the edge of the timeout",
    ("two-donatees", "P3c_true"): "needs an auxiliary invariant; unknown within the timeout",
    ("signature_error", "P5_true"): "valid by IC3 with z3, in 16 s to more than 30 s depending "
                                    "on the run: at the edge of the timeout",
    ("calls", "Report_sees_balance_after_transfer"): "invalid; found in 25-30 s (by the search "
                                                     "of the counterexample to induction): at "
                                                     "the edge of the timeout",
    ("calls", "Buy_mints"): "valid by invariants in about 24 s, or unknown, depending on the "
                            "run (Houdini ends at about 29 s in the rounds of the property): at "
                            "the edge of the timeout, in exact mode too (2026-10-19)",
    ("calls", "Report_sees_balance_at_call_point"): "as Buy_mints",
}


# for every number of users only
OPEN_ANY = {
    ("additivity", "P1_true"): "outside the fragment (an address existential under a universal):"
                               " no cutoff, true up to some number of users only",
    ("features", "Trivial"): "outside the fragment (the map next has address values): no cutoff,"
                             " true up to some number of users only",
}

# for every number of users only: the time of the properties decided after TIMEOUT, since
# the invariant phases of the checks with the cutoff and with 1, 2, ... users share it (with
# 120 s, on 2026-10-22: two-donatees P1_false in 45 s, P3b_false 57 s, calls
# Pay_zero_reverts 70 s, real_balances Small_payment 88 s, swap_pool Inv 57 s,
# Swap_reversibility 59 s)
LONGER_ANY = {("two-donatees", "P1_false"), ("two-donatees", "P3b_false"),
              ("calls", "Pay_zero_reverts"), ("real_balances", "Small_payment"),
              ("swap_pool", "Inv"), ("swap_pool", "Swap_reversibility")}
TIMEOUT_LONGER = 180


@pytest.fixture
def users(request):
    """The number of users of the option --users (conftest.py): every number by default."""
    return V.parse_users(request.config.getoption("--users"))


def cases():
    for path in [p for d in DIRS for p in sorted(glob.glob(os.path.join(d, "*.sol")))]:
        program, _ = V.load(path)
        for prop in program.properties:
            key = (V.stem(path), prop.name)
            marks = [pytest.mark.xfail(reason=OPEN[key], strict=False)] if key in OPEN else []
            yield pytest.param(path, prop.name, marks=marks, id=f"{key[0]}-{key[1]}")


@pytest.mark.kind2
@pytest.mark.parametrize("path,prop", list(cases()))
def test_regression(path, prop, users, request):
    program, _ = V.load(path)
    key = (V.stem(path), prop)
    if users == V.ANY and key in OPEN_ANY:
        request.node.add_marker(pytest.mark.xfail(reason=OPEN_ANY[key], strict=False))
    timeout = TIMEOUT_LONGER if users == V.ANY and key in LONGER_ANY else TIMEOUT
    outcome = V.verify(program, program.prop(prop), users, timeout)
    assert outcome.groundtruth_check() == "OK", outcome.describe()
