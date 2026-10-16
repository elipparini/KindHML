"""Invariant-assisted checks (`invariants.py`, `verify.verify` with strategy portfolio)."""

import os
from fractions import Fraction

import pytest

from kindhml import kind2
from kindhml import lustre as L
from kindhml import verify as V
from kindhml import invgen, pretty
from kindhml import syntax as S
from kindhml.builder import parse
from kindhml.errors import KindHMLError
from kindhml.fuzz import Fuzzer, has_witness
from kindhml.model import System
from kindhml.reference import FormulaEvaluator, initial_state
from kindhml.typecheck import check
from kindhml.invariants import Checks, cases, constant, hoist, state_fields, state_values

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
    prop = c.fenc.prop(program.prop("Swap_reversibility"), L.Var("s"))
    assert "Pool_r1" in state_fields(prop) and "balance" not in state_fields(prop)
    assert c.relevant(prop, list(c.candidates)) == ["Inv", "Small_reserves"]


def test_premises_direct_then_transitive():
    """In the AMM, the swaps share fields with Nonnegative only; Shares is connected to them
    through `supply`, which occurs in Nonnegative."""
    program, _ = V.load(os.path.join(ROOT, "contracts", "amm-real", "amm_real.sol"))
    c = Checks(program, 2, "inline", ("address", "method"))
    invariants = c.axioms + ["Nonnegative", "Shares"]
    assert c.premises(program.prop("Swap_reversibility"), invariants) == \
        [["Nonnegative"], ["Nonnegative", "Shares"]]


def test_programs_have_no_transition_system():
    program, c = checks()
    step, about = c.step_check(["Inv"])
    for lus in (step, c.property_check(program.prop("Swap_reversibility"), ["Inv"])[0]):
        main = lus[lus.index("node main"):]
        assert "pre" not in main and "->" not in main.replace("=>", "")
    # one step property per procedure, constructor included
    assert sorted(about) == [f"step_Inv__Pool_{p}" for p in
                             ("constructor", "init", "swap0", "swap1", "transfer0")]


def test_cases_through_implications():
    a, b, c_ = L.Var("a"), L.Var("b"), L.Var("c")
    assert cases(L.op("=>", a, L.op("and", b, c_))) == [L.op("=>", a, b), L.op("=>", a, c_)]
    assert cases(L.op("and", L.op("=>", a, b), c_)) == [L.op("=>", a, b), c_]


def test_property_split_into_cases():
    """Swap_reversibility quantifies over the addresses but null: one case per user (with
    the sender Pool, the transaction reverts, and its case simplifies to true)."""
    program, c = checks()
    _, names = c.property_check(program.prop("Swap_reversibility"), ["Inv"], split=True)
    assert names == ["Swap_reversibility__0", "Swap_reversibility__1"]
    _, names = c.property_check(program.prop("Swap_reversibility"), ["Inv"])
    assert names == ["Swap_reversibility"]


def test_sum_of_a_mapping():
    """sum(m): typed as the values of m, encoded as the sum of the fields of the record,
    evaluated by the reference interpreter."""
    program, _ = V.load(os.path.join(ROOT, "tests", "contracts", "reals.sol"))
    prop = program.prop("Shares_total")
    assert isinstance(prop.formula.left, S.SumMap) and prop.formula.real
    c = Checks(program, 2, "inline", ("address", "method"))
    text = L.render(c.fenc.prop(prop, L.Var("s")))
    assert "(((s.Pool_share.k_null + s.Pool_share.k_Pool) + s.Pool_share.k_u1)" in text
    st = initial_state(c.enc.system, {})
    st.fields[("Pool", "share")]["u1"] = Fraction(3, 2)
    st.fields[("Pool", "total")] = Fraction(3, 2)
    assert FormulaEvaluator(c.enc.system, range(2)).holds(prop.formula, [st])
    with pytest.raises(KindHMLError, match="mapping to numbers"):
        check(parse("contract C { int x; } property R { sum(x) == 0 }"))


def test_invariant_templates():
    """The generated candidates include the invariants written by hand for the AMM."""
    program, _ = V.load(os.path.join(ROOT, "contracts", "amm-real", "amm_real.sol"))
    texts = invgen.templates(program)
    for t in ("AMM.r0 >= 0", "(AMM.r0 > 0) == (AMM.r1 > 0)", "sum(AMM.minted) == AMM.supply",
              "forall _u : address . !is_EOA(_u) -> AMM.minted[_u] == 0",
              "AMM.minted[null] == 0"):
        assert t in texts, t
    assert len(invgen.candidates(program)) == len(texts)      # all well typed


def test_invariant_definitions():
    """An assignment f = e / d under the conditions G gives G && d != 0 -> f * d == e."""
    program, _ = V.load(os.path.join(ROOT, "contracts", "lending", "lending.sol"))
    texts = invgen.templates(program)
    assert ("((Lending.sc0 > (0)) && Lending.sc0 != 0) -> Lending.xr0 * Lending.sc0 == "
            "(Lending.res0 + (Lending.ssdebt * Lending.idx))") in texts
    assert "((Lending.sc0 == (0))) -> Lending.xr0 == (1)" in texts


def test_generated_candidates_filtered_by_reachable_states():
    """r0 <= 1 is false in reachable states of the pool (deposits of any size)."""
    program, _ = V.load(os.path.join(ROOT, "contracts", "amm-real", "amm_real.sol"))
    alive, n, keys = invgen.generate(program, Fuzzer(System.make(program, 2), seed="test"), 1.0)
    texts = {pretty.expr(r.formula) for r in alive}
    assert "(sum(minted) == supply)" in texts and "(r0 <= 1.0)" not in texts
    assert 0 < len(alive) < n


def test_minimize_keeps_the_strongest():
    f, g = "C.f", "C.g"
    keys = [("ge", f, Fraction(0)), ("gt", f), ("ge", f, Fraction(1)), ("le", g, Fraction(2)),
            ("le", g, Fraction(1)), ("pimp", f, g), ("peq", f, g), ("sum_eq", "C.m", f),
            ("sum_le", "C.m", f), ("null_eq", "C.m"), ("null_ge", "C.m")]
    assert invgen.minimize(keys) == [("ge", f, Fraction(1)), ("le", g, Fraction(1)),
                                     ("peq", f, g), ("sum_eq", "C.m", f), ("null_eq", "C.m")]


def test_hoist_universal_quantifiers():
    x, y, a = L.Var("x"), L.Var("y"), L.Var("a")
    inputs = []
    e = L.op("=>", a, L.Quant("forall", (("x", "real"),),
                              L.op("or", L.Quant("exists", (("y", "real"),), y), x)))
    assert hoist(e, inputs) == L.op("=>", a, L.op("or", L.Quant("exists", (("y", "real"),), y), x))
    assert inputs == [("x", "real")]
    # not under a negation, nor in the premise of an implication
    inputs = []
    e = L.op("=>", L.Quant("forall", (("x", "real"),), x), L.neg(L.Quant("forall", (("y", "real"),), y)))
    assert hoist(e, inputs) == e and inputs == []


def test_fuzzer_reaches_constructed_states():
    program, c = checks()
    f = Fuzzer(c.enc.system, seed="test")
    states = [st for _ in range(30) for _, st in f.traces()]
    assert any(all(st.constructed.values()) for st in states)
    assert all(not st.revert for st in states)


def test_fuzzer_candidates_and_witnesses():
    program, c = checks()
    f = Fuzzer(c.enc.system, seed="test")
    found = f.candidates(program.prop("Swap_takes_everything"), 5)
    assert found and all(all(st.constructed.values()) for _, st in found)
    assert not has_witness(program.prop("Swap_reversibility").formula)
    amm, _ = V.load(os.path.join(ROOT, "contracts", "amm-real", "amm_real.sol"))
    assert has_witness(amm.prop("Swap_additivity").formula)        # exists v12, v3
    assert has_witness(amm.prop("Arbitrage_exists").formula)       # exists x
    assert not has_witness(amm.prop("Slippage").formula)


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


def test_refuted_after_an_expanded_address_argument(tmp_path):
    """An address argument is expanded (A1), so it is not an input of the counterexample:
    the call is run with every address (a default 0 was not an address)."""
    path = tmp_path / "c.sol"
    path.write_text("contract C { mapping (address => int) m;"
                    " function set(address b) { m[b] = 1 } }\n"
                    "invariant Zero { forall u : address . m[u] == 0 }\n")
    program, _ = V.load(str(path))
    c = Checks(program, 2, "inline", ("address", "method"))
    contract = program.contracts[0]
    proc = contract.proc("set")
    cex = [{"name": "main", "streams": [
        {"name": "s.constructed_C", "instantValues": [[0, True]]}]}]
    assert c.refuted_after(cex, ["Zero"], contract, proc) == {"Zero"}


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_first_houdini_pass_runs():
    """A pass of FIRST_BUDGET seconds, the first round of `verify`, decides steps (they take
    about 0.5 s on the swap pool); it used to start none."""
    program, _ = V.load(POOL)
    invs = V._entry({}, program, 2, V.DEFAULT_MODE, V.DEFAULT_EXPAND, False, True)
    invs.attempt(V.FIRST_BUDGET)
    assert invs._done or invs.dropped


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_portfolio_on_the_swap_pool():
    """Inv is proved (inductive, or by Kind 2 if Houdini needs more than its first budget),
    Small_reserves is dropped, Swap_reversibility is proved on a free state under Inv,
    Swap_takes_everything is refuted. Without an invariant phase before the properties, Houdini
    runs in the rounds of the properties; its passes start programs from the first round."""
    program, _ = V.load(POOL)
    context = {}
    out = {r.name: V.verify(program, r, 2, 60, context=context) for r in program.properties}
    assert out["Inv"].status == "valid", out["Inv"].describe()
    assert (out["Swap_reversibility"].status, out["Swap_reversibility"].method) == \
        ("valid", "invariants")
    assert out["Swap_takes_everything"].status == "invalid"
    assert out["Small_reserves"].status == "invalid"
    invs = next(iter(context.values()))
    declared = [n for n in invs.proved if n not in invs.generated]
    assert declared == ["_lemma_balances_nonnegative", "Inv"]
    assert invs.dropped["Small_reserves"].startswith("inductive step")
