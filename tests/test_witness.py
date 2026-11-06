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
CASES = os.path.join(ROOT, "tests", "contracts", "witness", "cases.sol")
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


# ------------------------------------------------------------------ disjunctive instances

def _bound(e) -> list:
    """The names bound in e, with repetitions."""
    from kindhml import syntax as S
    out = [e.var] if isinstance(e, S.Quant) else []
    for name in getattr(e, "__dataclass_fields__", ()):
        v = getattr(e, name)
        for x in (v if isinstance(v, tuple) else (v,)):
            if isinstance(x, S.Expr):
                out += _bound(x)
    return out


def test_extended_terms_have_constants_and_products():
    program, _ = V.load(CASES)
    prop = program.prop("Defence_cases")
    plain = [t for t, _ in witness.choices(program, prop, witness.MAX_POOL)]
    extended = [t for t, _ in witness.choices(program, prop, witness.MAX_POOL, extended=True)]
    assert "price(1)" not in plain and "price((d[a] * r))" not in plain
    assert "price(1)" in extended and "price(0)" in extended and "price((d[a] * r))" in extended
    assert set(plain) <= set(extended)


def test_a_disjunctive_instance_binds_its_variables_apart():
    """Each case binds the liquidator b of the body: the second is renamed."""
    program, _ = V.load(CASES)
    prop = program.prop("Defence_cases")
    pool = dict(witness.choices(program, prop, witness.MAX_POOL, extended=True))
    text, inst = witness.instance(prop, [("price(1)", pool["price(1)"]),
                                         ("price((d[a] * r))", pool["price((d[a] * r))"])], "D")
    assert text == "price(1) | price((d[a] * r))"
    names = _bound(inst.formula)
    assert len(names) == len(set(names)) and "b__1" in names


def _state(txs):
    from kindhml.model import System
    from kindhml.reference import Interpreter, Tx, initial_state
    program, _ = V.load(CASES)
    system = System.make(program, 2)
    interp, st = Interpreter(system), initial_state(system, {})
    for sender, proc, args in txs:
        st = interp.step(st, Tx(sender, "C", ("C", proc), args))
        assert not st.revert, (proc, args)
    return st, system


def test_the_cases_cover_the_states():
    """At s1 (c[u2] == 0, price 3) only price(1) defends u2; at s2 (c[u2] == 1) a price of at
    least 4 does. The cases: price(1) and a call that holds at s2."""
    program, _ = V.load(CASES)
    cases = witness.Cases(program, program.prop("Defence_cases"))
    s1, system = _state([("u1", "constructor", {"s": 5}), ("u2", "owe", {"v": 2}),
                         ("u1", "grow", {}), ("u1", "price", {"v": 3})])
    first = cases.add(s1, system)
    assert [t for t, _ in first] == ["price(1)"]
    s2, _ = _state([("u1", "constructor", {"s": 5}), ("u1", "give", {"to": "u2", "v": 1}),
                    ("u2", "put", {"v": 1}), ("u2", "owe", {"v": 2}), ("u1", "grow", {}),
                    ("u1", "price", {"v": 3})])
    second = cases.add(s2, system)
    texts = [t for t, _ in second]
    assert len(texts) == 2 and "price(1)" in texts
    assert cases.add(s2, system) is None          # the same cases: not given again


@pytest.mark.kind2
def test_a_disjunctive_instance_proves_the_property():
    """Defence_cases has no cutoff and no single instance that proves it (each of price(1),
    price(d[a] * r) fails in one of the cases); a disjunction of instances is proved."""
    program, _ = V.load(CASES)
    o = V.verify(program, program.prop("Defence_cases"), V.ANY, 600, users_mode="combined")
    assert o.status == "valid", o.describe()
    assert "for the instance" in o.scope and " | " in o.scope, o.scope


def test_the_pool_has_the_defence_of_lending_int_v2():
    """The pool is ordered by the kind of the terms (fields, then constants, then products),
    each over all the procedures: with the procedures in turn, setPrice, the last procedure
    with one parameter, was cut out of the first 512 calls (2026-11-06)."""
    program, _ = V.load(os.path.join(ROOT, "contracts", "lending-int", "lending_int_v2.sol"))
    texts = [t for t, _ in witness.choices(program, program.prop("Liquidation_defence"),
                                           witness.MAX_POOL, extended=True)]
    assert "setPrice(1)" in texts and "setPrice((sdebt[a] * idx))" in texts
    assert texts.index("setPrice(1)") < min(i for i, t in enumerate(texts) if "*" in t)
