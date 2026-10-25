"""Boundary values of the fuzzer (`fuzz.boundaries`): a numeric parameter sometimes takes the
value of an expression it is compared with in the requires of its procedure, e.g. the whole
debt of lending-real, which random amounts almost never hit; and the weakened formula of the
bounded evaluation (`fuzz.weakened`) of properties with existentials over methods."""

import os

from kindhml import fuzz, pretty
from kindhml import verify as V
from kindhml.fuzz import Fuzzer
from kindhml.model import System

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPAY = os.path.join(ROOT, "tests", "contracts", "fuzz", "repay.sol")
LENDING_REAL = os.path.join(ROOT, "contracts", "lending-real", "lending_real.sol")
LOCK = os.path.join(ROOT, "tests", "contracts", "witness", "lock.sol")


def test_the_whole_debt_is_a_boundary_value_of_repay():
    program, _ = V.load(LENDING_REAL)
    bounds = fuzz.boundaries(program.contract("Lending").proc("repay"))
    texts = [pretty.expr(e) for e in bounds["v"]]
    assert any("sdebt" in t and "idx" in t for t in texts), texts
    assert all(t not in ("0", "0.0") for t in texts)        # constants are no boundaries


def test_boundary_values_reach_a_full_repayment(monkeypatch):
    """Never_repaid fails only after pay(debt * rate): with boundary values the fuzzer finds a
    candidate at once; without them, no seed of five found one in 10 s (2026-10-25)."""
    program, _ = V.load(REPAY)
    prop = program.prop("Never_repaid")
    found = Fuzzer(System.make(program, 1), "s1").candidates(prop, 10, limit=1)
    assert found
    monkeypatch.setattr(fuzz, "BOUNDARY", 0.0)
    assert not Fuzzer(System.make(program, 1), "s1").candidates(prop, 2, limit=1)


def test_the_weakened_formula_drops_the_existentials_over_methods():
    """Defence_exists = forall a . is_EOA(a) -> exists f, args . ... : weakened, the conclusion
    becomes false, which implies it."""
    program, _ = V.load(LOCK)
    formula = program.prop("Defence_exists").formula
    assert fuzz.has_method_existential(formula)
    assert pretty.expr(fuzz.weakened(formula)) == "(forall a:address. (is_EOA(a) -> false))"
    plain = V.load(REPAY)[0].prop("Never_repaid").formula
    assert fuzz.weakened(plain) is plain and not fuzz.has_method_existential(plain)


def test_a_slow_evaluation_switches_to_the_weakened_formula(monkeypatch):
    import signal
    program, _ = V.load(LOCK)
    prop = program.prop("Defence_exists")
    f = Fuzzer(System.make(program, 1), "s1")
    st = next(st for _, st in f.traces() if all(st.constructed.values()))
    old = signal.signal(signal.SIGALRM, fuzz._alarm)
    try:
        assert not f._violates(prop, st, 30)            # the property holds (lock(true))
        assert f._weak[prop.name] is None
        monkeypatch.setattr(fuzz, "SLOW_EVALUATION", 1e-6)
        assert f._violates(prop, st, 30)                # weakened: false for an EOA
        assert f._weak[prop.name] is not None
    finally:
        signal.signal(signal.SIGALRM, old)
