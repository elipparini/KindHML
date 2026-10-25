"""Instances of a chain of existentials over methods (`chains.py`, `verify._chain_rounds`), on
the crafted pools of tests/contracts/chain/: pool.sol (true: lower the price, liquidate, restore
it) and pool_oracle.sol (false: only the oracle sets the price)."""

import os
import time

import pytest

from kindhml import chains
from kindhml import verify as V

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
POOL = os.path.join(ROOT, "tests", "contracts", "chain", "pool.sol")
ORACLE = os.path.join(ROOT, "tests", "contracts", "chain", "pool_oracle.sol")
LOCK = os.path.join(ROOT, "tests", "contracts", "witness", "lock.sol")


def test_shape_of_a_chain():
    program, _ = V.load(POOL)
    sh = chains.shape(program.prop("Attack_any"))
    assert sh is not None and len(sh.chain) == 3
    assert [v for v, _ in sh.univ] == ["a", "b"]


def test_a_single_existential_is_no_chain():
    program, _ = V.load(LOCK)
    assert chains.shape(program.prop("Defence_exists")) is None


def test_instance_fixes_methods_and_addresses_not_numbers():
    program, _ = V.load(POOL)
    prop = program.prop("Attack_any")
    search = chains.Search(program, prop, chains.shape(prop))
    procs = {p.name: p for p in program.contract("Pool").procs}
    seq = (procs["setPrice"], procs["liquidate"], procs["setPrice"])
    env = {"a": "u1", "b": "u2"}
    args = [{"q": 1}, {"b": "u2", "v": 1}, {"q": 1}]
    text, inst = search.instance(seq, env, args)
    assert text == "setPrice(setPrice_0_q); liquidate(b, liquidate_1_v); setPrice(setPrice_2_q)"
    assert chains.shape(inst) is None           # no existential over methods is left


def test_new_existentials_avoid_the_names_taken():
    """A new existential named as a variable of the property would capture it (soundness
    review, 2026-10-25): it gets a fresh name instead."""
    program, _ = V.load(POOL)
    prop = program.prop("Attack_any")
    search = chains.Search(program, prop, chains.shape(prop))
    search.taken.add("setPrice_0_q")
    procs = {p.name: p for p in program.contract("Pool").procs}
    seq = (procs["setPrice"], procs["setPrice"], procs["setPrice"])
    text, _ = search.instance(seq, {}, None)
    assert text == "setPrice(setPrice_0_q_); setPrice(setPrice_1_q); setPrice(setPrice_2_q)"


@pytest.mark.kind2
def test_a_premise_that_never_holds_is_proved_by_the_weakened_property():
    """The side of the chain alone (other sides may prove this property first)."""
    program, _ = V.load(POOL)
    prop = program.prop("Attack_any_vacuous")
    context = {}
    V.prove_invariants(program, V.ANY, 120, context)
    start = time.time()
    gen = V._chain_rounds(program, prop, chains.shape(prop), context, V.DEFAULT_MODE,
                          V.DEFAULT_EXPAND, True, True, start, start + 120)
    try:
        while True:
            next(gen)
    except StopIteration as stop:
        o = stop.value
    assert o.status == "valid", o.describe()
    assert "its premise never holds" in o.scope


@pytest.mark.kind2
def test_a_true_chain_property_is_proved_by_an_instance():
    program, _ = V.load(POOL)
    o = V.verify(program, program.prop("Attack_any"), V.ANY, 300)
    assert o.status == "valid", o.describe()
    assert "for the instance" in o.scope


@pytest.mark.kind2
def test_a_false_chain_property_is_not_proved():
    program, _ = V.load(ORACLE)
    o = V.verify(program, program.prop("Attack_any"), V.ANY, 120)
    assert o.status != "valid", o.describe()
