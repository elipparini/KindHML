"""End-to-end regression tests: each rule of contracts/regression must match its ground
truth within a small timeout. Runs Kind 2 (one job at a time); select with -m kind2.

Rules listed in OPEN are known not to match yet; each entry says why.
"""

import glob
import os

import pytest

from kindhml import verify as V

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TIMEOUT = 10

OPEN = {
    ("division", "P1_true"): "nonlinear witness; unknown within the timeout",
    ("two-donatees", "P2_true"): "needs an auxiliary invariant; unknown within the timeout",
    ("two-donatees", "P4_true"): "needs an auxiliary invariant; unknown within the timeout",
    ("two-donatees", "P2b_true"): "needs an auxiliary invariant; unknown within the timeout",
    ("two-donatees", "P3c_true"): "needs an auxiliary invariant; unknown within the timeout",
}


def cases():
    for path in sorted(glob.glob(os.path.join(ROOT, "contracts", "regression", "*.sol"))):
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
