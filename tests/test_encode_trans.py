"""Structural tests of the statement encoding S^i(s)."""

import pytest

from kindhml import desugar
from kindhml.errors import KindHMLError
from kindhml import lustre as L
from kindhml import syntax as S
from kindhml.builder import parse
from kindhml.encode_trans import Encoder
from kindhml.model import System
from kindhml.typecheck import check

CONTRACT = """
contract C {
    int x; int y;
    function f(bool e) { if (e) { x = 1; y = 2 } else { y = 3 } }
    function g(int d) { x = 10 / d }
}
"""


def encoder():
    program, _ = check(parse(CONTRACT))
    return Encoder(System.make(program, 1)), program.contracts[0]


def test_length_of_conditional_is_max_of_branches():
    enc, c = encoder()
    assert enc.length(c.proc("f").body) == 2


def test_paper_example_padding():
    """S^i(if e then (x = 1; y = 2) else y = 3) = ITE(e^i, x^{i+1} = 1 ∧ y^{i+2} = 2, y^{i+1} = 3),
    the else branch padded with one skip: both branches define levels i+1 and i+2."""
    enc, c = encoder()
    levels = enc.levels(desugar.body(enc.system, c, c.proc("f").body), 0, L.Var("t"))
    assert sorted(levels) == [1, 2]
    for k in (1, 2):
        assert isinstance(levels[k], L.Ite)
    # level 1: then-branch sets x, else-branch sets y
    then1 = dict(levels[1].then.fields)
    else1 = dict(levels[1].orelse.fields)
    assert then1["C_x"] == L.Int(1) and else1["C_y"] == L.Int(3)
    # level 2 of the else-branch is the padding skip: nothing changes, no revert
    else2 = dict(levels[2].orelse.fields)
    assert else2["C_y"] == L.Proj(L.Var("l1"), "C_y") and else2["revert"] == L.FALSE


def test_division_is_guarded():
    """A statement with a division is ITE(def^i(s), S^i(s), S^i(require false))."""
    enc, c = encoder()
    stmt = S.SetField("C", "x", None, c.proc("g").body.value)
    level = enc.levels(stmt, 0, L.Var("t"))[1]
    assert isinstance(level, L.Ite)
    assert level.cond == L.op("<>", L.Proj(L.Var("t"), "C_g_d"), L.Int(0))
    assert dict(level.orelse.fields)["revert"] == L.TRUE


def test_cyclic_calls_rejected_A4():
    program, _ = check(parse("""
        contract A { function f() { B.g() } }
        contract B { function g() { A.f() } }"""))
    with pytest.raises(KindHMLError, match="cyclic contract calls"):
        Encoder(System.make(program, 1)).program()


def test_call_arguments_evaluated_at_call_point():
    """In the unfolded body, parameters denote terms over the level of the call."""
    program, _ = check(parse("""
        contract A { function f() { B.g(balance) $ 1 } }
        contract B { int x; function g(int b) payable { x = b } }"""))
    enc = Encoder(System.make(program, 1))
    a = program.contract("A")
    body = desugar.body(enc.system, a, a.proc("f").body)
    assert isinstance(body, S.Unfold) and body.caller == "A" and body.callee == "B"
    levels = enc.levels(body, 0, L.Var("t"))
    # initPay (level 1), constructed guard (2), x = b (3): b is balance[A] at level 0
    assert dict(levels[3].fields)["B_x"] == L.Proj(L.Proj(L.Var("s"), "balance"), "k_A")


def test_procedure_length_includes_guards():
    """Levels: tx guard, initPay, constructed guard, then the body."""
    enc, c = encoder()
    fn = enc.trans_proc(c, c.proc("f"))
    assert len(fn.locals) == 3 + 2
