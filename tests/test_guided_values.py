"""The guided search of the fuzzer with the values of the universal variables of a
counterexample to induction (`fuzz.Fuzzer.guided`, `values`): the bounded evaluation tries them
first, so a counterexample that needs an amount outside its fixed domain is found (milestone C;
amm_real_v4 Sandwich needs a small x)."""

from fractions import Fraction

from kindhml.builder import parse
from kindhml.fuzz import Fuzzer
from kindhml.model import System
from kindhml.typecheck import check

SOURCE = """
pragma balance real;
contract C {
    real r;
    constructor(real r0) { require(r0 >= 1.0); r = r0 }
    function set(real v) { require(v >= 1.0); r = v }
}
property Small { forall x : real . x > 0.0 -> x * 1000.0 > r }
"""


def program():
    return check(parse(SOURCE))[0]


def test_values_of_the_counterexample_to_induction_are_tried_first():
    p = program()
    prop = p.prop("Small")
    target = {("C", "r"): Fraction(1)}
    plain = Fuzzer(System.make(p, 1), seed="t").guided(prop, target, 3)
    assert plain == []                   # x ranges over -1, -1/2, 0, 1/2, ..., 3: x * 1000 > r
    with_values = Fuzzer(System.make(p, 1), seed="t").guided(
        prop, target, 3, values={"x": [Fraction(1, 1000)]})
    assert with_values
    txs, st = with_values[0]
    assert st.fields[("C", "r")] >= 1


def test_values_are_restored_after_the_search():
    p = program()
    f = Fuzzer(System.make(p, 1), seed="t")
    f.guided(p.prop("Small"), {("C", "r"): Fraction(1)}, 1, values={"x": [Fraction(1, 1000)]})
    assert f.ev.extra == {}


def test_values_take_the_type_of_the_quantifier():
    from kindhml import syntax as S
    from kindhml.reference import _of_type
    assert _of_type(1, S.REAL) == Fraction(1) and isinstance(_of_type(1, S.REAL), Fraction)
    two = _of_type(Fraction(4, 2), S.INT)
    assert two == 2 and isinstance(two, int)
    assert _of_type(Fraction(1, 2), S.INT) is None
    assert _of_type(-1, S.UINT) is None
    assert _of_type(True, S.INT) is None and _of_type("A_a", S.REAL) is None


def test_the_universal_values_of_a_model_or_counterexample():
    from kindhml import verify as V
    model = {"q_x_3": Fraction(1, 1000), "q_x_7": 2, "q_ok_4": True, "q_a_5": "a", "s.r": 1}
    assert V._input_values(model) == {"x": [Fraction(1, 1000), 2]}
    cex = [{"streams": [
        {"name": "q_x_3", "instantValues": [[0, {"num": 1, "den": 1000}]]},
        {"name": "q_a_5", "instantValues": [[0, "A_a"]]},
        {"name": "s.r", "instantValues": [[0, 1]]}]}]
    assert V._stream_inputs(cex) == {"q_x_3": Fraction(1, 1000), "q_a_5": "a"}
    assert V._input_values(V._stream_inputs(cex)) == {"x": [Fraction(1, 1000)]}
    assert V._stream_inputs(None) == {}
