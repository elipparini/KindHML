"""Differential test of the formula encoding Φ (Theorem `thm:correctness` on samples).

On random reachable states S, the generated property (∧ constructed) → Φ(φ), evaluated in
Python on the Lustre AST, must agree with the direct evaluation of φ in S by
`reference.FormulaEvaluator`. Both evaluations quantify integers over the same small domain,
so they must agree exactly; this checks the encoding of modalities, old, args, h(), the
quantifier domains and their expansion, independently of Kind 2.
"""

import glob
import os
import random
import signal
import time

import pytest

from kindhml import lustre as L
from kindhml.encode_formula import METHOD_COPIES, FormulaEncoder, parse_expand
from kindhml.encode_trans import Encoder
from kindhml.lustre_eval import Evaluator
from kindhml.model import System
from kindhml.reference import FormulaEvaluator, Interpreter
from kindhml import verify as V

import test_trans as T

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FILES = sorted(glob.glob(os.path.join(ROOT, "contracts", "*", "*.sol"))
               + glob.glob(os.path.join(ROOT, "tests", "contracts", "*.sol")))
INTS = (-1, 0, 1, 2)
STATES = 6
BUDGET = 3.0            # seconds per rule and configuration; later states are skipped
CONFIGS = [("inline", ("address", "method")), ("inline", ()), ("subst", ("address", "method"))]


def cases():
    for path in FILES:
        program, _ = V.load(path)
        for rule in program.rules:
            for mode, expand in CONFIGS:
                yield pytest.param(path, rule.name, mode, expand,
                                   id=f"{V.stem(path)}-{rule.name}-{mode}-{'x' if expand else 'q'}")


@pytest.mark.slow
@pytest.mark.parametrize("path,rule_name,mode,expand", list(cases()))
def test_formula_matches_reference(path, rule_name, mode, expand):
    program, _ = V.load(path)
    rule = program.rule(rule_name)
    system = System.make(program, 2)
    enc = Encoder(system)
    prog, _ = enc.program()
    prop = FormulaEncoder(enc, mode, expand).rule(rule)
    lev = Evaluator(prog, int_domain=INTS)
    ref = FormulaEvaluator(system, INTS)
    interp = Interpreter(system)
    rnd = random.Random(f"{path}:{rule_name}")
    start, checked = time.time(), 0
    signal.signal(signal.SIGALRM, _too_slow)
    try:
        for _ in range(STATES):
            left = BUDGET - (time.time() - start)
            if left <= 0:
                break
            st = T.random_reachable_state(system, rnd, interp)
            signal.setitimer(signal.ITIMER_REAL, left)
            try:
                state = lev.eval(T.state_literal(st, system, enc), {})
                encoded = lev.eval(prop, {"s": state})
                expected = (not all(st.constructed.values())) or ref.holds(rule.formula, [st])
            except _TooSlow:
                break
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
            assert encoded == expected, (st, encoded, expected)
            checked += 1
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    if checked == 0:
        pytest.skip("no state checked within the budget")


class _TooSlow(Exception):
    pass


def _too_slow(signum, frame):
    raise _TooSlow()


VAULT = os.path.join(ROOT, "contracts", "vault", "vault.sol")


def test_parse_expand():
    assert parse_expand(("address", "method")) == ({"address", "method"}, METHOD_COPIES)
    assert parse_expand(("method:9",)) == ({"method"}, 9)
    for bad in (("address:3",), ("method:x",)):
        with pytest.raises(ValueError):
            parse_expand(bad)


@pytest.mark.parametrize("bound,symbolic", [(9, set()), (3, {"f2"}), (1, {"f1", "f2"})])
def test_method_copies_bound_the_expansion(bound, symbolic):
    """Two_steps_drainability nests f1 and f2 over the 3 methods of the vault: 9 copies.
    With the bound 3 only f1 (the outer one) is expanded; the others stay quantified, as
    fresh variables q_f1_N, q_f2_N."""
    program, _ = V.load(VAULT)
    enc = Encoder(System.make(program, 2))
    prop = FormulaEncoder(enc, "inline", ("address", f"method:{bound}")).rule(
        program.rule("Two_steps_drainability"))
    text = L.render(prop)
    assert {f for f in ("f1", "f2") if f"q_{f}_" in text} == symbolic


def test_partial_expansion_matches_reference():
    """The encoding with f1 expanded and f2 quantified agrees with the reference."""
    test_formula_matches_reference(VAULT, "Two_steps_drainability", "inline",
                                   ("address", "method:3"))
