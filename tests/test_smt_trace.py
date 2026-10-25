"""Saving SMT-LIB instances (`smt_trace.py`): logics, splitting of incremental scripts with
pushes, pops, assumptions and activation literals, the files written; with z3 (marker kind2:
a solver job), the answers of the standalone scripts."""

import csv
import os

import pytest
import z3

from kindhml import smt_trace as T


def logic(script: str) -> str:
    commands, _ = T.parse(script)
    return T.logic_name(T.incremental(commands)[1])


DECLS = "(declare-fun x () Int)(declare-fun y () Int)"


@pytest.mark.parametrize("body, expected", [
    ("(assert (= (* 2 x) y))", "QF_LIA"),
    ("(assert (= (* x y) 1))", "QF_NIA"),
    ("(assert (= (* (- 3) x (+ 1 2)) y))", "QF_LIA"),
    ("(assert (= (div x 2) (mod y 3)))", "QF_LIA"),
    ("(assert (= (div 2 x) y))", "QF_NIA"),
    ("(assert (= (mod y x) 0))", "QF_NIA"),
    ("(assert (= (abs x) y))", "QF_LIA"),
    ("(assert (let ((c 3) (d x)) (= (* c x) (* 2 d))))", "QF_LIA"),
    ("(assert (let ((d x)) (= (* d x) 0)))", "QF_NIA"),
    ("(assert (let ((c 3)) (let ((c x)) (= (* c y) 0))))", "QF_NIA"),
    ("(assert (let ((c x)) (and (let ((c 3)) (= (* c y) 0)) (> c 0))))", "QF_LIA"),
    ("(define-fun k () Int (+ 2 3))(assert (= (* k x) y))", "QF_LIA"),
    ("(define-fun k () Int (+ 2 y))(assert (= (* k x) y))", "QF_NIA"),
    ("(define-fun f ((a Int)) Int (* a a))(assert (= (f x) y))", "QF_NIA"),
    ("(assert (forall ((z Int)) (>= (* z x) 0)))", "NIA"),
    ("(assert (exists ((z Int)) (= (+ z x) 0)))", "LIA"),
    ("(declare-fun r () Real)(assert (= (to_real x) (* r r)))", "QF_NIRA"),
    ("(declare-fun f (Int) Int)(assert (= (f x) (* 2 y)))", "QF_UFLIA"),
])
def test_logic(body, expected):
    assert logic(DECLS + body + "(check-sat)") == expected


def test_logic_without_arithmetic():
    assert logic("(declare-fun p () Bool)(assert p)(check-sat)") == "QF_UF"
    assert T.logic_name({"Q"}) == "UF"


def test_sublogics():
    assert T.sublogics({"Q", "N", "I"}) == {"NIA", "QF_NIA", "LIA", "QF_LIA", "UF", "QF_UF"}


def test_truncated_and_answers():
    script = (DECLS + "(assert (> x 0))\n;; Success\n(check-sat)\n;; Sat\n"
              "(check-sat-assuming (p))\n;; Unsat\n(assert (and (> x")
    commands, truncated = T.parse(script)
    assert truncated
    assert [c.head for c in commands] == ["declare-fun", "declare-fun", "assert", "check-sat",
                                          "check-sat-assuming"]
    assert [c.status for c in commands[3:]] == ["sat", "unsat"]
    assert commands[4].assumptions == (("p", True),)


# activation literals as Kind 2 uses them: a0 activates the property, a1 and a2 two queries
SCRIPT = """
(set-option :print-success true)
(set-logic NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun unused () Int)
(declare-fun a0 () Bool)
(declare-fun a1 () Bool)
(declare-fun a2 () Bool)
(define-fun prop ((v Int)) Bool (> (* v v) 3))
(assert (and (>= x 0) (<= x 10)))
(assert (=> a0 (prop x)))
(push 1)
(declare-fun z () Int)
(assert (=> a1 (= (* x y) 7)))
(check-sat-assuming (a0 a1))
;; Sat
(get-value (x y))
(pop 1)
(assert (=> a2 (< x 2)))
(check-sat-assuming (a0 a2))
;; Unsat
(assert (not a2))
(check-sat)
;; Sat
(exit)
"""


def standalones(script: str):
    commands, _ = T.parse(script)
    return [(k, c, T.standalone(commands, live, c)) for k, c, live in T.replay(commands)]


def test_split_scopes_and_assumptions():
    (k1, c1, (s1, f1)), (k2, c2, (s2, f2)), (k3, c3, (s3, f3)) = standalones(SCRIPT)
    assert (k1, c1.status, k2, c2.status, k3, c3.status) == (1, "sat", 2, "unsat", 3, "sat")
    text1, text2, text3 = "\n".join(s1), "\n".join(s2), "\n".join(s3)
    # the declaration of z is in scope for the first query only, and unused
    assert "(declare-fun z () Int)" not in text1 + text2
    assert "unused" not in text1 + text2 + text3
    # the first query: a1 assumed, a2 not declared yet
    assert "(assert a0)" in text1 and "(assert a1)" in text1 and "a2" not in text1
    # the second query: the assertion of a1 was popped
    assert "a1" not in text2 and "(=> a2 (< x 2))" in text2
    # the third query: no assumption, so a0 and a2 are set to false and their assertions go
    assert "a0" not in text3 and "a2" not in text3 and "prop" not in text3
    assert T.logic_name(f3) == "QF_LIA"
    assert T.logic_name(f1) == T.logic_name(f2) == "QF_NIA"


def test_guard_used_elsewhere_is_kept():
    script = ("(declare-fun x () Int)(declare-fun a () Bool)"
              "(assert (=> a (> (* x x) 2)))(assert (or a (= x 1)))(check-sat)")
    [(_, _, (lines, feats))] = standalones(script)
    assert "(assert (=> a (> (* x x) 2)))" in lines and T.logic_name(feats) == "QF_NIA"


def test_guard_used_through_a_definition_is_kept():
    script = ("(declare-fun x () Int)(declare-fun a () Bool)(define-fun g () Bool (not a))"
              "(assert (=> a (> (* x x) 2)))(assert g)(check-sat)")
    [(_, _, (lines, _))] = standalones(script)
    assert "(assert (=> a (> (* x x) 2)))" in lines and "(define-fun g () Bool (not a))" in lines


def test_cleaned_incremental():
    commands, _ = T.parse(SCRIPT)
    lines, feats, checks = T.incremental(commands)
    text = "\n".join(lines)
    assert checks == 3 and T.logic_name(feats) == "QF_NIA"
    assert "set-option" not in text and "get-value" not in text and "set-logic" not in text
    assert text.count("(set-info :status sat)") == 2 and "(set-info :status unsat)" in text


def test_tracer_files_filter_and_duplicates(tmp_path):
    tracer = T.Tracer(str(tmp_path), ["QF_NIA"])
    tracer.start_task("contracts/amm-int/amm_int_v2.sol", "Swap")
    assert tracer.task == "amm-int-v2__Swap"
    # the trace (QF_NIA) and its first two checks; the third is QF_LIA
    assert tracer.record(SCRIPT, 1, "rounds", "bmc-1", "z3", "sources/x.lus") == 3
    assert tracer.record(SCRIPT, 2, "search", "ind-1", "z3", "sources/y.lus") == 3
    rows = list(csv.DictReader(open(tmp_path / "MANIFEST.csv")))
    assert [(r["kind"], r["logic"], r["query"], r["status"]) for r in rows[:3]] == [
        ("incremental", "QF_NIA", "", ""), ("standalone", "QF_NIA", "1", "sat"),
        ("standalone", "QF_NIA", "2", "unsat")]
    assert rows[1]["file"] == ("standalone/amm-int-v2__Swap__call001-rounds__bmc-1__z3"
                               "__q0001__QF_NIA.smt2")
    assert [r["duplicate_of"] for r in rows[3:]] == [r["file"] for r in rows[:3]]
    assert [r["file"] for r in rows[3:]] == ["", "", ""]
    assert sorted(os.listdir(tmp_path / "standalone")) == sorted(
        os.path.basename(r["file"]) for r in rows[1:3])
    text = open(tmp_path / rows[2]["file"]).read()
    assert "(set-logic QF_NIA)" in text and "(set-info :status unsat)" in text


def test_tracer_incremental(tmp_path):
    tracer = T.Tracer(str(tmp_path), ["QF_NIA", "NIA"])
    tracer.start_task("contracts/bank/bank.sol", "invariants")
    tracer.record(SCRIPT, 3, "free-run", "ic3ia-p3-2", "cvc5", "")
    [inc] = os.listdir(tmp_path / "incremental")
    assert inc == "bank-v1__invariants__call003-free-run__ic3ia-p3-2__cvc5__QF_NIA.smt2"


@pytest.mark.kind2
def test_standalone_answers_with_z3(tmp_path):
    """Each standalone script has the answer of its check in the trace."""
    tracer = T.Tracer(str(tmp_path))
    tracer.record(SCRIPT, 1, "rounds", "bmc-1", "z3", "")
    rows = [r for r in csv.DictReader(open(tmp_path / "MANIFEST.csv"))
            if r["kind"] == "standalone"]
    assert len(rows) == 3
    for r in rows:
        s = z3.Solver()
        s.from_file(str(tmp_path / r["file"]))
        assert str(s.check()) == r["status"]
