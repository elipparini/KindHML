"""End-to-end regression tests: each rule of contracts/regression and tests/contracts must
match its ground truth within a small timeout. Runs Kind 2 (one job at a time); select with
-m kind2.

Rules listed in OPEN are known not to match yet; each entry says why.
"""

import glob
import os

import pytest

from kindhml import verify as V

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# With the default solver strategy, z3 gets the second half of it; some rules need z3 for
# about 10 s (calls Relay_never_reverts, with three contracts).
TIMEOUT = 30
DIRS = [os.path.join(ROOT, "contracts", "regression"), os.path.join(ROOT, "tests", "contracts")]

OPEN = {
    ("division", "P1_true"): "nonlinear witness; unknown within the timeout",
    ("two-donatees", "P2_true"): "needs an auxiliary invariant; unknown within the timeout",
    ("two-donatees", "P4_true"): "needs an auxiliary invariant; unknown within the timeout",
    ("two-donatees", "P2b_true"): "valid by IC3 with z3 in about 30 s: at the edge of the timeout",
    ("two-donatees", "P3c_true"): "needs an auxiliary invariant; unknown within the timeout",
    ("two-donatees", "P5_true"): "valid by IC3 in about 27 s with strategy kind2; the checks on "
                                 "free states of the portfolio leave too little time",
    ("signature_error", "P5_true"): "valid by IC3 with z3, in 16 s to more than 30 s depending "
                                    "on the run: at the edge of the timeout",
    ("calls", "Report_sees_balance_after_transfer"): "invalid; found in 25-30 s (by the search "
                                                     "of the counterexample to induction): at "
                                                     "the edge of the timeout",
}


def cases():
    for path in [p for d in DIRS for p in sorted(glob.glob(os.path.join(d, "*.sol")))]:
        program, _ = V.load(path)
        for rule in program.rules:
            key = (V.stem(path), rule.name)
            marks = [pytest.mark.xfail(reason=OPEN[key], strict=False)] if key in OPEN else []
            yield pytest.param(path, rule.name, marks=marks, id=f"{key[0]}-{key[1]}")


@pytest.mark.kind2
@pytest.mark.parametrize("path,rule", list(cases()))
def test_regression(path, rule):
    program, _ = V.load(path)
    outcome = V.verify(program, program.rule(rule), 2, TIMEOUT)
    assert outcome.groundtruth_check() == "OK", outcome.describe()
