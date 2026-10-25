"""Checks on free values by z3 directly (`direct.py`): translation, guards of divisions,
rewriting into pure real arithmetic, models; with z3 (marker kind2: a solver job), the checks of
tests/contracts/swap_witness.sol."""

import os
from fractions import Fraction

import pytest
import z3

from kindhml import direct
from kindhml import lustre as L
from kindhml import verify as V
from kindhml.concrete import state_literal
from kindhml.direct import Declarations, NotApplicable, check_fragment, check_guards
from kindhml.invariants import Checks
from kindhml.reference import initial_state

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WITNESS = os.path.join(ROOT, "tests", "contracts", "swap_witness.sol")

DECLS = Declarations(
    {"St": [("x", "real"), ("y", "real"), ("ok", "bool"), ("n", "int"), ("who", "address")]},
    {"address": ["A_null", "A_u1"]}, {})
s, v = L.Var("s"), L.Var("v")
x, y = L.Proj(s, "x"), L.Proj(s, "y")
ZERO, ONE = L.Real(Fraction(0)), L.Real(Fraction(1))


def div(a, b):
    return L.op("/", a, b)


def guarded(a, b):
    """a / b as the encoding of contract code writes it: ite(b != 0, a / b, 0)."""
    return L.Ite(L.neg(L.op("=", b, ZERO)), div(a, b), ZERO)


def prepare(formula, inputs=(("s", "St"),)):
    return direct.prepare(formula, list(inputs), DECLS)


def test_records_and_enum_constants_are_translated():
    q = prepare(L.op("=>", L.op("=", L.Var("A_u1"), L.Var("A_u1")),
                     L.op(">=", L.op("*", x, x), ZERO)))
    assert set(q.free) == {"s.x"}


def test_a_field_of_enumerated_type_splits_the_check():
    """The field ranges over exactly the constants of its type: one query per constant."""
    q = prepare(L.op("=", L.Proj(s, "who"), L.Var("A_u1")))
    assert isinstance(q, direct.SplitQuery)
    assert [fixed for fixed, _ in q.cases] == [{"s.who": "A_null"}, {"s.who": "A_u1"}]
    assert [case.trivial for _, case in q.cases] == [False, True]


def test_too_many_cases_are_outside_the_fragment(monkeypatch):
    monkeypatch.setattr(direct, "MAX_CASES", 1)
    with pytest.raises(NotApplicable):
        prepare(L.op("=", L.Proj(s, "who"), L.Var("A_u1")))


def test_a_variable_address_is_outside_the_fragment():
    """An address that is not a field of an input record (here a quantified one) is not split."""
    a = L.Var("a")
    with pytest.raises(NotApplicable):
        prepare(L.Quant("exists", (("a", "address"),), L.op("=", a, L.Var("A_u1"))))


def test_integers_are_outside_the_fragment():
    with pytest.raises(NotApplicable):
        prepare(L.op(">=", L.Proj(s, "n"), L.Int(0)))


def test_guarded_divisions_are_accepted():
    body = L.op(">", guarded(x, L.op("+", y, v)), ZERO)
    prepare(L.Quant("exists", (("v", "real"),), body))
    # guards by an implication, by a conjunct, by a disjunct b = 0
    prepare(L.op("=>", L.op(">", y, ZERO), L.op(">", div(x, y), ONE)))
    prepare(L.op("and", L.neg(L.op("=", y, ZERO)), L.op(">", div(x, y), ONE)))
    prepare(L.op("or", L.op("=", y, ZERO), L.op(">", div(x, y), ONE)))


def test_an_unguarded_division_is_outside_the_fragment():
    """With d free when b = 0, `exists v . x / (y + v) > 0` would become valid."""
    body = L.op(">", div(x, L.op("+", y, v)), ZERO)
    with pytest.raises(NotApplicable):
        prepare(L.Quant("exists", (("v", "real"),), body))
    # the guard must be on the divisor itself
    with pytest.raises(NotApplicable):
        prepare(L.op("=>", L.op(">", x, ZERO), L.op(">", div(x, y), ONE)))


def test_a_guard_does_not_cross_into_an_inner_quantifier():
    """In `exists v . v != 0 && (exists w . w = 0 && 1 / w = 5)`, the guard on v must not guard
    the division by w (both are the de Bruijn index 0 in z3's bodies): accepted, the formula
    would be found valid with w = 0 and d = 5, while 1 / 0 is unspecified."""
    w = L.Var("w")
    inner = L.Quant("exists", (("w", "real"),),
                    L.op("and", L.op("=", w, ZERO), L.op("=", div(ONE, w), L.Real(Fraction(5)))))
    with pytest.raises(NotApplicable):
        prepare(L.Quant("exists", (("v", "real"),),
                        L.op("and", L.neg(L.op("=", v, ZERO)), inner)))


def test_a_division_by_the_numeral_zero_is_outside_the_fragment():
    with pytest.raises(NotApplicable):
        prepare(L.op(">", div(x, ZERO), ONE))
    prepare(L.op(">", div(x, L.Real(Fraction(2))), ONE))


def test_the_rewriting_gives_pure_real_arithmetic():
    body = L.op(">", L.op("+", guarded(x, L.op("+", y, v)),
                          L.Ite(L.op(">", v, ONE), v, L.op("-", v))), ZERO)
    q = prepare(L.Quant("exists", (("v", "real"),), body))
    check_fragment(q.assertion)
    assert "ite" not in q.smtlib()


def _holds(q, point) -> bool:
    """The truth of the quantified formula q (one quantifier at the top) at a point (values of
    its free constants), by a quantifier-free query: its body, with the bound variables as
    constants, is satisfiable (exists) or its negation is not (forall)."""
    xs = [z3.Const(f"{q.var_name(i)}!{i}", q.var_sort(i)) for i in range(q.num_vars())]
    body = z3.substitute(z3.substitute_vars(q.body(), *reversed(xs)), *point)
    s_ = z3.Solver()
    s_.set("timeout", 5000)
    s_.add(body if q.is_exists() else z3.Not(body))
    r = s_.check()
    assert r != z3.unknown
    return (r == z3.sat) == q.is_exists()


def test_the_rewriting_is_an_equivalence_for_guarded_divisions():
    """Each rewritten formula has the truth value of the original at each point of a grid of
    values of the free constants (z3, in process, on small formulas)."""
    r = direct._Rewriter()
    a, b, p = z3.Reals("a b p")
    t = z3.Real("t")
    formulas = [
        z3.Exists([t], z3.If(z3.Not(b + t == 0), a / (b + t), p) > 1),
        z3.ForAll([t], z3.If(t > 0, t, -t) + z3.If(z3.Not(b == 0), a / b, 0) >= p),
        z3.Exists([t], z3.And(t > 0, z3.If(z3.Not(t * b == 0),
                                          (a / (t * b)) * z3.If(a > 0, a, 1), 0) > p)),
    ]
    grid = [z3.RealVal(v) for v in ("-1", "0", "1/2", "2")]
    for f in formulas:
        check_guards(f)
        rewritten, new, defs = r.formula(f)
        assert not new and z3.is_quantifier(rewritten)
        check_fragment(rewritten)
        for va in grid:
            for vb in grid:
                for vp in grid:
                    point = [(a, va), (b, vb), (p, vp)]
                    assert _holds(f, point) == _holds(rewritten, point), (f, point)


def test_values_of_a_model():
    text = ("((|s.AMM_r0| 1.0) (q_p_3 (/ 511.0 512.0)) (|s.ok| true) (m (- (/ 1.0 4.0)))"
            " (w (root-obj (+ (^ x 2) (- 2)) 1)))")
    assert direct.parse_values(text) == {"s.AMM_r0": 1, "q_p_3": Fraction(511, 512),
                                         "s.ok": True, "m": Fraction(-1, 4)}
    assert direct.literal(Fraction(1, 2)) == L.Real(Fraction(1, 2))
    assert direct.literal(True) == L.TRUE


def test_inputs_of_a_counterexample_to_induction():
    assert V._inputs({"q_p_3": Fraction(511, 512), "q_x_10": Fraction(2), "s.r0": 1}) \
        == "; with p = 511/512, x = 2"
    assert V._inputs(None) == ""


# ------------------------------------------------------------------ with z3

def witness_checks(users=2):
    program, _ = V.load(WITNESS)
    return program, Checks(program, users, "inline", ("address", "method"))


@pytest.mark.kind2
def test_existentials_on_free_states():
    program, c = witness_checks()
    for name, expected in (("Swap_reversibility", "valid"), ("Arbitrage_exists", "valid"),
                           ("Arbitrage_exists_at_the_price", "invalid")):
        status, refuted, solver, answer = V._direct_check(
            c, program.prop(name), ["Inv"], [], 20, {}, ("k",))
        assert status == expected, name
        assert solver == V.DIRECT_SOLVER
        if expected == "invalid":
            # the values of the universal p and of the state, for the search of s*
            model = answer.values
            assert not answer.missing
            [p] = [val for k, val in model.items() if k.startswith("q_p")]
            assert model["s.Pool_r1"] == p * model["s.Pool_r0"]


@pytest.mark.kind2
def test_a_split_check_is_decided_case_by_case():
    who = L.Proj(s, "who")
    valid = prepare(L.op("or", L.op("=", who, L.Var("A_null")), L.op("=", who, L.Var("A_u1"))))
    assert valid.run(20).status == "valid"
    # refuted in the case who = A_null: the model has the constant of the case, for s*
    answer = prepare(L.op("=>", L.op("=", who, L.Var("A_null")), L.op(">", x, ZERO))).run(20)
    assert answer.status == "invalid" and answer.values["s.who"] == "A_null"
    assert direct.literal(answer.values["s.who"]) == L.Var("A_null")


@pytest.mark.kind2
def test_existential_at_a_concrete_state():
    program, c = witness_checks()
    st = initial_state(c.enc.system, {a: Fraction(0) for a in c.enc.system.addresses})
    st.constructed["Pool"] = True
    st.fields[("Pool", "r0")], st.fields[("Pool", "r1")] = Fraction(2), Fraction(2)
    st.fields[("Pool", "t0")]["u1"] = Fraction(1)
    literal = state_literal(st, c.enc.system, c.enc)
    prop = program.prop("Arbitrage_exists_at_the_price")
    assert V._direct_concrete(c, prop, literal, 20) == ("invalid", V.DIRECT_SOLVER)
    assert V._direct_concrete(c, program.prop("Arbitrage_exists"), literal, 20)[0] == "valid"


@pytest.mark.kind2
@pytest.mark.parametrize("name,expected", [("Swap_reversibility", "valid"),
                                           ("Arbitrage_exists", "valid"),
                                           ("Arbitrage_exists_at_the_price", "invalid")])
def test_existentials_for_every_number_of_users(name, expected):
    program, _ = V.load(WITNESS)
    outcome = V.verify(program, program.prop(name), V.ANY, 60)
    assert outcome.status == expected, outcome.describe()
    if expected == "valid":
        assert outcome.solver == V.DIRECT_SOLVER
