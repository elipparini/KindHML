"""The completion of fuzzer states by the solver (`extend.py`): one more transaction, found by
z3, from a reachable state of the fuzzer."""

import os
import time

import pytest

from kindhml import extend
from kindhml import verify as V
from kindhml.fuzz import Fuzzer
from kindhml.invariants import Checks
from kindhml.reference import FormulaEvaluator

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
COMPLETION = os.path.join(ROOT, "tests", "contracts", "fuzz", "completion.sol")


def _completion(name: str, users: int = 1):
    program, _ = V.load(COMPLETION)
    checks = Checks(program, users, V.DEFAULT_MODE, V.DEFAULT_EXPAND)
    return extend.Completion.make(checks, program.prop(name)), program


def _candidates(comp, seconds: float):
    fuzzer = Fuzzer(comp.system, "t1")
    return list(comp.candidates(fuzzer, time.time() + seconds)), fuzzer


def test_applicable():
    program, _ = V.load(COMPLETION)
    assert extend.applicable(program.prop("Never_target").formula)
    assert extend.applicable(program.prop("Scale_grows").formula)    # old inside a modality
    assert not extend.applicable(program.prop("Top_reverted").formula)
    comp, _ = _completion("Top_reverted")
    assert comp is None


def test_the_completion_finds_the_needle():
    """set(1000003) from a state of the fuzzer, then the property is false at the new state."""
    comp, program = _completion("Never_target")
    assert comp is not None
    found, fuzzer = _candidates(comp, 20)
    assert found
    txs, st, tx = found[0]
    assert tx.method == ("C", "set") and tx.args == {"v": 1000003}
    nxt = fuzzer.interp.step(st, tx)
    assert not nxt.revert
    ev = FormulaEvaluator(comp.system, range(-1, 4))
    assert not ev.holds(program.prop("Never_target").formula, [nxt])


def test_no_completion_of_a_true_property():
    comp, _ = _completion("Scale_grows")
    assert comp is not None
    found, _ = _candidates(comp, 5)
    assert found == []
    assert comp.keys                   # some states were completed


def test_states_with_a_known_key_are_not_completed_again():
    comp, _ = _completion("Scale_grows")
    fuzzer = Fuzzer(comp.system, "t1")
    first = comp._new_states(fuzzer, "s", 1)
    again = comp._new_states(fuzzer, "s", 1)
    assert first                        # each state returned is counted under its key
    assert sum(comp.keys.values()) == len(first) + len(again)
    assert all(n <= comp.per_key for n in comp.keys.values())


def test_the_keys_saturate_and_admit_more_states():
    """The keys are finitely many: when a batch finds no state, `per_key` is doubled."""
    comp, _ = _completion("Scale_grows")
    fuzzer = Fuzzer(comp.system, "t1")
    for _ in range(20):
        if comp.per_key > 1:
            break
        comp._new_states(fuzzer, "s", 0.5)
    assert comp.per_key > 1


def test_closest_states_to_a_target():
    """With a target (as from a counterexample to induction), the walk keeps the closest
    state of each trace; the relative distance is 0 at the target."""
    comp, _ = _completion("Never_target")
    fuzzer = Fuzzer(comp.system, "t1")
    target = comp._target({("C", "x"): 0, ("C", "k"): 4, (None, "u9"): 3})
    assert (None, "u9") not in target           # not an address of this system
    states = comp._closest_states(fuzzer, "g", target, 1)
    assert states
    st = states[0][1]
    assert extend.distance(st, {("C", "k"): st.fields[("C", "k")]}) == 0


def test_the_sources_alternate_by_state():
    """With a target, the states closest to it and the states by key alternate one by one,
    so both are completed even within one short call (a batch of closest states is larger
    than a window of the rounds)."""
    comp, _ = _completion("Scale_grows")
    fuzzer = Fuzzer(comp.system, "t1")
    guide = {("C", "x"): 0, ("C", "k"): 4}
    assert list(comp.candidates(fuzzer, time.time() + 3, guide)) == []
    assert comp.completed["near"] >= 1 and comp.completed["keys"] >= 1
    assert sum(comp.keys.values()) >= 1     # by batch: 0 of 92 states (2026-11-06)


def test_the_closest_states_go_first():
    """With a target, the first state completed is one of the closest states."""
    comp, _ = _completion("Scale_grows")
    fuzzer = Fuzzer(comp.system, "t1")
    calls = []
    near, keys = comp._closest_states, comp._new_states
    comp._closest_states = lambda *a: calls.append("near") or near(*a)
    comp._new_states = lambda *a: calls.append("keys") or keys(*a)
    list(comp.candidates(fuzzer, time.time() + 3, {("C", "x"): 0, ("C", "k"): 4}))
    assert calls[:2] == ["near", "keys"]


@pytest.mark.kind2
def test_a_needle_is_refuted():
    program, _ = V.load(COMPLETION)
    o = V.verify(program, program.prop("Never_target"), 1, 60)
    assert o.status == "invalid", o.describe()
