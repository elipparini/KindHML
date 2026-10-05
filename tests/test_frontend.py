"""Parser and type checker tests."""

import glob
import os

import pytest

from kindhml import pretty
from kindhml import syntax as S
from kindhml.builder import parse
from kindhml.errors import KindHMLError
from kindhml.typecheck import check

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ALL_FILES = sorted(glob.glob(os.path.join(ROOT, "contracts", "*", "*.sol")))

BANK = """
contract Bank {
    mapping (address => int) funds;
    function deposit() payable { funds[msg.sender] += msg.value }
    function withdraw(uint amount) {
        require(amount <= funds[msg.sender]);
        funds[msg.sender] -= amount;
        msg.sender.transfer(amount)
    }
}
"""


def checked(rules: str, contract: str = BANK) -> S.Program:
    program, _ = check(parse(contract + rules))
    return program


def formula(rule_body: str, contract: str = BANK) -> str:
    program = checked("rule R { " + rule_body + " }", contract)
    return pretty.expr(program.rules[0].formula)


def rejects(rule_body: str, message: str, contract: str = BANK):
    with pytest.raises(KindHMLError, match=message):
        checked("rule R { " + rule_body + " }", contract)


@pytest.mark.parametrize("path", ALL_FILES, ids=os.path.basename)
def test_benchmarks_typecheck(path):
    program, _ = check(parse(open(path).read()))
    assert program.rules


def test_benchmarks_have_groundtruth():
    for path in ALL_FILES:
        program = parse(open(path).read())
        missing = [r.name for r in program.rules if r.groundtruth is None]
        assert not missing, (path, missing)


# ---------------------------------------------------------------- parsing

def test_implicit_constructor():
    c = checked("").contracts[0]
    assert c.procs[0].name == S.CONSTRUCTOR and c.procs[0].params == ()


def test_compound_assignment_desugared():
    deposit = checked("").contracts[0].proc("deposit")
    assert isinstance(deposit.body, S.Assign)
    assert isinstance(deposit.body.value, S.BinOp) and deposit.body.value.op == "+"


def test_quantifier_and_modality_bodies_extend_right():
    assert formula("forall a : address . a != null -> << a : Bank . deposit() $ 1 >> "
                   "funds[a] > 0 && !lastReverted") == (
        "(forall a:address. ((a != null) -> (<< a : Bank.deposit() $ 1 >> "
        "((funds[a] > 0) && !lastReverted))))")


def test_block_increase_in_modality():
    assert formula("forall a : address . forall n : uint . "
                   "<< a : Bank . deposit() $ 1 @ n + 1 >> true") == (
        "(forall a:address. (forall n:uint. (<< a : Bank.deposit() $ 1 @ (n + 1) >> true)))")


def test_implication_is_right_associative():
    assert formula("true -> false -> true") == "(true -> (false -> true))"


def test_groundtruth_comment_attaches_to_next_rule():
    program = parse(BANK + """
        // @groundtruth: True
        rule A { true }
        rule B { true }
        /* @groundtruth: False */ rule C { true }
        rule D_false { true }
        // @groundtruth: True
        rule E_false { true }""")
    assert [r.groundtruth for r in program.rules] == [True, None, False, False, True]


def test_syntax_error_has_position():
    with pytest.raises(KindHMLError, match="line 2"):
        parse("contract C {\n  int x = }")


# ---------------------------------------------------------------- resolution

def test_balance_forms():
    assert formula("balance > 0 && balance[this] == Bank.balance") == (
        "((balance[Bank] > 0) && (balance[Bank] == balance[Bank]))")


def test_old_moves_one_level_up():
    program = checked("rule R { forall a : address . << a : Bank . deposit() $ 1 >> "
                      "funds[a] == old(funds[a]) + 1 }")
    modal = program.rules[0].formula.body
    assert isinstance(modal, S.Modal) and isinstance(modal.proc, S.ProcConst)


def test_method_variable_and_args():
    program = checked("rule R { forall f : method . forall x : calldataargs . "
                      "f != withdraw -> << null : Bank . f(x) $ 0 >> true }")
    modal = program.rules[0].formula.body.body.right
    assert modal.proc == S.QVar("f", S.METHOD) and modal.args == (S.QVar("x", S.ARGS),)


def test_method_variable_without_args():
    checked("rule R { exists f : method . << null : Bank . f() $ 0 >> true }")


# ---------------------------------------------------------------- errors

def test_old_at_depth_zero():
    rejects("funds[null] == old(funds[null])", "scope of a modality")


def test_old_too_deep():
    rejects("<< null : Bank . deposit() $ 1 >> old(old(balance)) > 0", "scope of a modality")


def test_sender_in_rule_A6():
    rejects("msg.sender == null", "A6")


def test_args_in_two_modalities_A7():
    rejects("forall f : method . forall x : calldataargs . "
            "<< null : Bank . f(x) $ 0 >> << null : Bank . f(x) $ 0 >> true", "A7")


def test_wrong_number_of_arguments():
    rejects("<< null : Bank . withdraw() $ 0 >> true", "requires 1 argument")


def test_unknown_contract():
    rejects("<< null : Bnak . deposit() $ 0 >> true", "unknown contract")


def test_unknown_procedure():
    rejects("<< null : Bank . foo() $ 0 >> true", "neither a procedure")


def test_type_mismatch():
    rejects("funds[null] == true", "cannot compare")


def test_map_index_must_be_address():
    rejects("funds[1] > 0", "type address")


def test_quantified_name_clash():
    rejects("forall funds : int . true", "clashes")


def test_lastreverted_in_contract():
    with pytest.raises(KindHMLError, match="only occur in rules"):
        checked("", "contract C { bool b; function f() { b = lastReverted } }")


def test_assign_to_parameter():
    with pytest.raises(KindHMLError, match="only fields can be assigned"):
        checked("", "contract C { function f(int x) { x = 1 } }")


def test_assign_whole_mapping():
    with pytest.raises(KindHMLError, match="whole mapping"):
        checked("", "contract C { mapping(address => int) m; function f() { m = 1 } }")


# ---------------------------------------------------------------- reals

POOL = """
contract P {
    real r;
    int n;
    mapping (address => real) m;
    function f(real x, int k) payable { r = x + k; m[msg.sender] = 1; n = k }
}
"""


def test_int_converted_to_real():
    assert formula("r + n > 1 && r == 2", POOL) == "(((r + real(n)) > 1.0) && (r == 2.0))"
    assert formula("n + 1 > 1", POOL) == "((n + 1) > 1)"


def test_real_literals():
    assert formula("r > -0.25 && m[null] < 1.5", POOL) == "((r > -0.25) && (m[null] < 1.5))"


def test_real_quantifier():
    assert formula("forall x : real . x * x >= 0", POOL) == "(forall x:real. ((x * x) >= 0.0))"


def test_real_division_flag():
    program = checked("rule R { r / 2 == n / 2 }", POOL)
    eq = program.rules[0].formula
    assert eq.real and eq.left.real and not eq.right.arg.real    # real(n div 2)


def test_mod_on_reals():
    rejects("r % 2 == 0", "not defined on reals", POOL)


def test_real_into_int():
    with pytest.raises(KindHMLError, match="type int, found real"):
        checked("", "contract C { int n; function f(real x) { n = x } }")


def test_integer_division_converted_to_real_warns():
    _, warnings = check(parse("contract C { real r; function f(int a) { r = a / 2 } }"))
    assert any("integer division converted to real" in w for w in warnings)


def test_real_value_needs_real_balances():
    rejects("<< null : P.f(1, 1) $ 0.5 >> true", "type int, found real", POOL)
    program = checked("rule R { << null : P.f(1, 1) $ 0.5 >> balance > 0.25 }",
                      "pragma balance real;" + POOL)
    assert program.balance_type == S.REAL


def test_amounts_are_real_with_real_balances():
    with pytest.raises(KindHMLError, match="type int, found real"):
        checked("", "pragma balance real; contract C { int x; function f() payable"
                    " { x = msg.value } }")


def test_bad_pragma():
    for text in ("pragma balance bool;", "pragma value real;"):
        with pytest.raises(KindHMLError, match="only pragmas"):
            checked("", text + " contract C { }")
