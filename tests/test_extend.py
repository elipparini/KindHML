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
    assert first                        # each state returned has a key not seen before
    assert len(comp.keys) == len(first) + len(again)


@pytest.mark.kind2
def test_a_needle_is_refuted():
    program, _ = V.load(COMPLETION)
    o = V.verify(program, program.prop("Never_target"), 1, 60)
    assert o.status == "invalid", o.describe()
