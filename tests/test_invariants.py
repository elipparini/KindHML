"""Invariant-assisted checks (`invariants.py`, `verify.verify` with strategy portfolio)."""

import os
from fractions import Fraction

import pytest

from kindhml import kind2
from kindhml import lustre as L
from kindhml import verify as V
from kindhml.invariants import Checks, constant, state_fields, state_values

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
POOL = os.path.join(ROOT, "tests", "contracts", "swap_pool.sol")

try:
    kind2.find_kind2()
    HAVE_KIND2 = True
except FileNotFoundError:
    HAVE_KIND2 = False


def checks():
    program, _ = V.load(POOL)
    return program, Checks(program, 2, "inline", ("address", "method"))


def test_candidates_include_the_balance_lemma():
    _, c = checks()
    assert list(c.candidates) == ["_lemma_balances_nonnegative", "Inv", "Small_reserves"]


def test_only_relevant_invariants_are_assumed():
    """The balance lemma (over balance) does not concern Swap_reversibility."""
    program, c = checks()
    prop = c.fenc.rule(program.rule("Swap_reversibility"), L.Var("s"))
    assert "Pool_r1" in state_fields(prop) and "balance" not in state_fields(prop)
    assert c.relevant(prop, list(c.candidates)) == ["Inv", "Small_reserves"]


def test_programs_have_no_transition_system():
    program, c = checks()
    for lus in (c.step_check(["Inv"]), c.rule_check(program.rule("Swap_reversibility"), ["Inv"])):
        main = lus[lus.index("node main"):]
        assert "pre" not in main and "->" not in main.replace("=>", "")


def test_state_values_of_a_counterexample():
    cex = [{"name": "main", "streams": [
        {"name": "s.Pool_r0", "instantValues": [[0, {"num": 3, "den": 2}]]},
        {"name": "s.Pool_t0.k_u1", "instantValues": [[0, {"num": 0, "den": 1}]]},
        {"name": "s.constructed_Pool", "instantValues": [[0, True]]},
        {"name": "t.sender", "instantValues": [[0, "A_u1"]]}]}]
    values = state_values(cex)
    assert values == {"s.Pool_r0": L.Real(Fraction(3, 2)), "s.Pool_t0.k_u1": L.Real(Fraction(0)),
                      "s.constructed_Pool": L.TRUE}
    assert constant("A_u1") == L.Var("A_u1") and constant(4) == L.Int(4)


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_portfolio_on_the_swap_pool():
    """Inv is proved (inductive, or by Kind 2 if Houdini needs more than its first budget),
    Small_reserves is dropped, Swap_reversibility is proved on a free state under Inv,
    Swap_takes_everything is refuted."""
    program, _ = V.load(POOL)
    context = {}
    out = {r.name: V.verify(program, r, 2, 60, context=context) for r in program.rules}
    assert out["Inv"].status == "valid"
    assert (out["Swap_reversibility"].status, out["Swap_reversibility"].method) == \
        ("valid", "invariants")
    assert out["Swap_takes_everything"].status == "invalid"
    assert out["Small_reserves"].status == "invalid"
    invs = next(iter(context.values()))
    assert invs.proved == ["_lemma_balances_nonnegative", "Inv"]
    assert invs.dropped == {"Small_reserves": "inductive step"}
