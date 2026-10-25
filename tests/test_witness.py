"""Candidate witnesses of existentials over a method and its arguments (`witness.py`)."""

import os

import pytest

from kindhml import pretty
from kindhml import verify as V
from kindhml import witness

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LENDING = os.path.join(ROOT, "contracts", "lending-simple-real", "lending_simple_real.sol")
LOCK = os.path.join(ROOT, "tests", "contracts", "witness", "lock.sol")
UINT = os.path.join(ROOT, "tests", "contracts", "witness", "uint.sol")
LENDING_REAL = os.path.join(ROOT, "contracts", "lending-real", "lending_real.sol")


def test_an_instance_is_the_explicit_strategy():
    """Liquidation_defence_exists with f = repay and v = debt[a] is Liquidation_defence."""
    program, _ = V.load(LENDING)
    found = dict(witness.instances(program, program.prop("Liquidation_defence_exists")))
    assert pretty.expr(found["repay(debt[a])"].formula) == \
        pretty.expr(program.prop("Liquidation_defence").formula)


def test_procedures_with_fewer_combinations_first():
    program, _ = V.load(LENDING)
    texts = [t for t, _ in witness.instances(program, program.prop("Liquidation_defence_exists"))]
    assert len(texts) == witness.MAX_INSTANCES and len(set(texts)) == len(texts)
    # the guard terms first (repay's require debt[msg.sender] >= v), then the generic ones
    assert texts.index("repay(debt[a])") < 16


def test_guard_terms_give_the_whole_debt():
    """On lending-real the defence repays the whole debt sdebt[a] * idx: a product, which only
    the guard of repay (sdebt[msg.sender] * idx >= v) gives."""
    program, _ = V.load(LENDING_REAL)
    texts = [t for t, _ in witness.instances(program, program.prop("Liquidation_defence"))]
    whole = [t for t in texts if t.startswith("repay(") and "sdebt[a]" in t and "idx" in t]
    assert whole and texts.index(whole[0]) < 16


def test_guard_terms_fit_the_type():
    program, _ = V.load(UINT)
    c = program.contracts[0]
    assert witness.guard_terms(program, c.proc("f"), c.proc("f").params[0], None, ["a"]) == []


def test_no_instance_without_an_existential_over_a_method():
    program, _ = V.load(LENDING)
    assert witness.instances(program, program.prop("Liquidation_defence")) == []
    assert witness.instances(program, program.prop("Health_non_interference")) == []


SOURCE = """
pragma balance real;
contract C {
    real r;
    constructor() { r = 0.0 }
    function set(real v) { r = v }
    function inc() { r = r + 1.0 }
}
property Here { forall a : address . << a : C.inc() >> exists f : method .
    exists args : calldataargs . << a : C.f(args) >> r == 1.0 }
property Later { forall a : address . exists f : method . exists args : calldataargs .
    << a : C.inc() >> << a : C.f(args) >> r == 1.0 }
"""


def test_arguments_only_at_the_state_of_the_existential():
    """The terms replace the arguments only in modalities at the state of the existential: in
    Later, r in set(r) would denote r after inc, not a value fixed at the existential."""
    from kindhml.builder import parse
    from kindhml.typecheck import check
    program = check(parse(SOURCE))[0]
    here = [t for t, _ in witness.instances(program, program.prop("Here"))]
    assert "set(r)" in here and "inc()" in here
    assert witness.instances(program, program.prop("Later")) == []


@pytest.mark.kind2
def test_an_instance_proves_the_property_for_every_number_of_users():
    """Defence_exists has no cutoff; its instance lock(true) has one, and is proved for every n
    (milestone D). On lending-simple-real Liquidation_defence_exists, the instance
    repay(debt[a]) is proved in 30 s, after 63 refuted instances (`experiments/witness/`)."""
    program, _ = V.load(LOCK)
    o = V.verify(program, program.prop("Defence_exists"), V.ANY, 60, users_mode="combined")
    assert o.status == "valid", o.describe()
    assert o.scope.startswith("n >= ") and "for the instance lock(true)" in o.scope


def test_no_int_term_for_a_uint_parameter():
    """f(m[a]) with m of type int is no instance of Revertible: a negative m[a] makes the call of
    f(uint) revert, while the arguments of the property range over the naturals."""
    program, _ = V.load(UINT)
    texts = [t for t, _ in witness.instances(program, program.prop("Revertible"))]
    assert "f(m[a])" not in texts and "f(k)" not in texts
    assert "setm(m[a])" in texts and "setm(k)" in texts


@pytest.mark.kind2
def test_a_false_property_is_not_proved_by_an_ill_typed_instance():
    program, _ = V.load(UINT)
    o = V.verify(program, program.prop("Revertible"), V.ANY, 60, users_mode="combined")
    assert o.status != "valid", o.describe()
