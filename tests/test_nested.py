"""Nested modalities in mode inline (`encode_formula.FormulaEncoder.modal`): a large next state
that a nested modality whose method is a variable takes as input gets fresh variables
(INLINE_BOUND), and the encoders stop at the time limit of the check (DEADLINE)."""

import os
import time

import pytest

from kindhml import encode_formula as E
from kindhml import lustre as L
from kindhml import lustre_subst
from kindhml import verify as V
from kindhml.invariants import Checks

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ANY = os.path.join(ROOT, "tests", "contracts", "nested", "any.sol")
WITNESS = os.path.join(ROOT, "tests", "contracts", "swap_witness.sol")
POOL = os.path.join(ROOT, "tests", "contracts", "swap_pool.sol")
AMM = os.path.join(ROOT, "contracts", "amm-real", "amm_real_v4.sol")


def test_tree_size_counts_shared_nodes_as_often_as_printed():
    x = L.op("+", L.Var("a"), L.Var("b"))          # 3 nodes
    y = L.op("*", x, x)                              # shared twice: 1 + 3 + 3
    assert E.tree_size(x) == 3 and E.tree_size(y) == 7
    assert E.tree_size(L.record("R", [("f", y), ("g", x)])) == 1 + 7 + 3


def test_modalities_with_method_variables_are_detected():
    program, _ = V.load(ANY, lemmas=False)
    assert all(E._has_method_variable(program.prop(n).formula) for n in ("Any1", "Any2", "Any3"))
    pool, _ = V.load(POOL)
    assert not E._has_method_variable(pool.prop("Inv").formula)
    amm, _ = V.load(AMM)
    assert not E._has_method_variable(amm.prop("Sandwich").formula)


def test_three_nested_modalities_are_encoded_quickly():
    """Any3 (three modalities whose methods are variables) did not encode in 600 s: the next
    states had 4,200, 375,000 and 31 million nodes as trees (2 users)."""
    program, _ = V.load(ANY, lemmas=False)
    c = Checks(program, 2, "inline", ("address", "method"))
    start = time.time()
    e = c._property(program.prop("Any3"), L.Var("s"), True)
    assert time.time() - start < 60
    assert E.tree_size(e) < 2_000_000
    assert "exists" in L.render(e)[:10 ** 6]


def test_the_encoding_stops_at_the_deadline(monkeypatch):
    program, _ = V.load(ANY, lemmas=False)
    monkeypatch.setattr(E, "INLINE_BOUND", 10 ** 12)     # the old encoding, which never ended
    monkeypatch.setattr(E, "LAST_BOUND", 10 ** 12)
    monkeypatch.setattr(lustre_subst, "DEADLINE", time.time() + 2)
    c = Checks(program, 2, "inline", ("address", "method"))
    start = time.time()
    with pytest.raises(E.EncodingTimeout):
        c._property(program.prop("Any3"), L.Var("s"), True)
    assert time.time() - start < 30


@pytest.mark.kind2
@pytest.mark.parametrize("path,name,expected", [
    (WITNESS, "Swap_reversibility", "valid"), (WITNESS, "Arbitrage_exists_at_the_price", "invalid"),
    (POOL, "Swap_reversibility", "valid"), (POOL, "Swap_takes_everything", "invalid")])
def test_bound_states_keep_the_verdicts(monkeypatch, path, name, expected):
    """With every next state bound to existential variables (bound 0), the verdicts are those
    of the substituted terms (Trans is a function)."""
    monkeypatch.setattr(E, "INLINE_BOUND", 0)
    monkeypatch.setattr(E, "LAST_BOUND", 0)
    program, _ = V.load(path)
    outcome = V.verify(program, program.prop(name), 2, 60, users_mode="exact")
    assert outcome.status == expected, outcome.describe()


@pytest.mark.kind2
def test_a_check_stops_during_an_encoding(monkeypatch):
    """verify returns at its time limit even if an encoding would not end."""
    monkeypatch.setattr(E, "INLINE_BOUND", 10 ** 12)
    monkeypatch.setattr(E, "LAST_BOUND", 10 ** 12)
    program, _ = V.load(ANY, lemmas=False)
    start = time.time()
    outcome = V.verify(program, program.prop("Any3"), 2, 20, users_mode="exact")
    assert time.time() - start < 60
    assert outcome.status == "unknown"
