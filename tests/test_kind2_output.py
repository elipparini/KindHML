"""Reading Kind 2's JSON and plain-text outputs (no Kind 2 needed)."""

import os
import subprocess

from kindhml import kind2
from kindhml.kind2 import format_counterexample, parse_output, parse_text, parse_version

RAW = """[
{
  "objectType" : "log",
  "level" : "info",
  "value" : "kind2 v2.3.0"
}
,
{
  "objectType" : "property",
  "name" : "init.(0 <= r.x and
 r.x <= 0)",
  "isCandidate" : "true",
  "answer" : {"source" : "ind2", "value" : "valid"}
}
,
{
  "objectType" : "property",
  "name" : "P",
  "isCandidate" : "false",
  "runtime" : {"unit" : "sec", "timeout" : false, "value" : 1.5},
  "answer" : {"source" : "ind", "value" : "valid"}
}
,
{
  "objectType" : "property",
  "name" : "Q",
  "isCandidate" : "false",
  "runtime" : {"unit" : "sec", "timeout" : false, "value" : 2.0},
  "answer" : {"source" : "bmc", "value" : "falsifiable"}
}
]
"""


def test_complete_output():
    out = parse_output(RAW)
    assert [(p.name, p.status) for p in out.properties] == [("P", "valid"), ("Q", "invalid")]
    assert out.errors == []


COUNTER = """[
{
  "objectType" : "property",
  "name" : "P",
  "isCandidate" : "false",
  "runtime" : {"unit" : "sec", "timeout" : false, "value" : 0.051},
  "k" : 2,
  "answer" : {"source" : "bmc", "value" : "falsifiable"},
  "counterExample" :
  [{"blockType" : "node", "name" : "main", "streams" :
    [{"name" : "x", "type" : "int", "class" : "output",
      "instantValues" : [[0, 0], [1, 1], [2, 2]]}]}]
}
]
"""


def test_transactions_of_a_counterexample():
    """k is the number of steps after the initial state, i.e. of transactions: x = 0 -> pre x +
    1 with the property x < 2 is refuted with k = 2 (output of Kind 2 v3.0.0, abridged; the
    text output of v2.3.0 and v3.0.0 says "for k=2" too)."""
    p = parse_output(COUNTER).properties[0]
    assert (p.status, p.k) == ("invalid", 2)
    assert p.describe() == "invalid after 2 transactions, 0.051s"
    q = next(p for p in parse_text(TEXT).properties if p.name == "Q")
    assert q.describe() == "invalid after 3 transactions, 2.842s"
    assert kind2.PropertyResult("P", "invalid", 1).describe() == "invalid after 1 transaction"
    assert kind2.PropertyResult("P", "invalid").describe() == "invalid"


def test_truncated_output_keeps_complete_objects():
    for cut in range(len(RAW)):
        names = [p.name for p in parse_output(RAW[:cut]).properties]
        assert names in ([], ["P"], ["P", "Q"])
    assert [p.name for p in parse_output(RAW[:RAW.index('"Q"')]).properties] == ["P"]


def test_stray_text_between_objects():
    raw = RAW.replace("\n,\n{\n  \"objectType\" : \"property\",\n  \"name\" : \"Q\"",
                      "\nFatal error: exception\n,\n{\n  \"objectType\" : \"property\",\n"
                      "  \"name\" : \"Q\"", 1)
    assert "Fatal error" in raw
    assert [p.name for p in parse_output(raw).properties] == ["P", "Q"]


def test_empty_output_reports_stderr():
    assert parse_output("", "Segmentation fault\n").errors == [
        "no output from Kind 2: Segmentation fault"]
    assert parse_text("", "Segmentation fault\n").errors == [
        "no output from Kind 2: Segmentation fault"]


TEXT = """ kind2 v2.3.0-467-gc2817d4
================================================================================
Analyzing main
<Warning> Cannot mine invariants in quantified terms

<Success> Generated candidate property init[l101c8].((0 <= r.x) and (r.x <= 0)) is valid by 2-induction after 0.159s.

<Success> Property L is valid by 2-induction after 0.159s.

<Error> Runtime error in inductive step: Invalid_argument("Ltree.fold : quantified term")

<Success> Property P is valid by property directed reachability (IA) after 0.829s.

<Failure> Property Q is invalid by bounded model checking for k=3 after 2.842s.

--------------------------------------------------------------------------------
Summary of properties:
--------------------------------------------------------------------------------
P: valid (k=1)
Q: invalid after 3 steps
R: true up to 2 steps
S: unknown
L: valid (k=2)
================================================================================
<Timeout> Wallclock timeout.
"""


def test_text_output():
    out = parse_text(TEXT)
    got = {p.name: (p.status, p.k, p.engine, p.time, p.true_up_to) for p in out.properties}
    assert got == {"L": ("valid", 2, "ind2", 0.159, None),
                   "P": ("valid", 1, "ic3ia", 0.829, None),
                   "Q": ("invalid", 3, "bmc", 2.842, None),
                   "R": ("unknown", None, None, None, 2),
                   "S": ("unknown", None, None, None, None)}
    assert out.errors == ['Runtime error in inductive step: '
                          'Invalid_argument("Ltree.fold : quantified term")', "Wallclock timeout."]


TEXT_V3 = """ kind2 v3.0.0

================================================================================
Analyzing main
<Success> Property _lemma_balances_nonnegative is valid by property directed reachability (IA) after 5.041s.

<Note> Incomplete analysis result: Not all properties could be proven invariant

--------------------------------------------------------------------------------
Summary of Properties:
--------------------------------------------------------------------------------
Arbitrage_exists: true up to 0 steps
  (s.constructed_AMM =>
  ((forall (q_p_1: real) true and
     forall
       (q_p_3: real)
       ((q_p_3 > 0.0) => exists (q_x_4: real) (q_x_4 > 0.0))))
_lemma_balances_nonnegative: valid (k=1)
  (s.AMM_r0 >= 0.0)
================================================================================

<Timeout> Wallclock timeout.
"""


def test_text_output_of_v3():
    """Kind 2 v3.0.0 writes "Summary of Properties:" and, unless --show_props false, the
    expression of each property under its line (an output of v3.0.0, the expressions cut)."""
    for text in (TEXT_V3, "\n".join(line for line in TEXT_V3.splitlines()
                                    if not line.startswith("  "))):
        out = parse_text(text)
        got = {p.name: (p.status, p.k, p.engine, p.true_up_to) for p in out.properties}
        assert got == {"_lemma_balances_nonnegative": ("valid", 1, "ic3ia", None),
                       "Arbitrage_exists": ("unknown", None, None, 0)}
        assert out.timed_out


def test_version(monkeypatch):
    assert parse_version(" kind2 v3.0.0\n") == (3, 0, 0)
    assert parse_version(" kind2 v2.3.0-ge8216dd\n") == (2, 3, 0)
    assert parse_version("") == (0, 0, 0)
    monkeypatch.setattr(kind2, "version", lambda path: (3, 0, 0))
    assert kind2.text_args("kind2")[-2:] == ["--show_props", "false"]
    assert kind2.default_args("kind2") == ["--bmc_check_unroll", "true"]
    monkeypatch.setattr(kind2, "version", lambda path: (2, 3, 0))
    assert "--show_props" not in kind2.text_args("kind2")
    assert kind2.default_args("kind2") == []


def test_cvc5_with_mbqi_alone(monkeypatch, tmp_path):
    """The solver "cvc5-mbqi" is cvc5 through the wrapper, which adds --no-cegqi
    --no-sygus-inst, unless KINDHML_CVC5_OPTIONS=kind2 or no cvc5 is found; "cvc5" keeps
    Kind 2's options."""
    cvc5 = tmp_path / "cvc5"
    cvc5.write_text("#!/bin/sh\necho \"$@\"\n")
    cvc5.chmod(0o755)
    monkeypatch.setenv("CVC5", str(cvc5))
    monkeypatch.delenv("KINDHML_CVC5_OPTIONS", raising=False)
    assert kind2.solver_args("cvc5") == ["--smt_solver", "cvc5"]
    assert kind2.solver_env("cvc5") is None
    args = kind2.solver_args("cvc5-mbqi")
    assert args == ["--smt_solver", "cvc5", "--cvc5_bin", kind2.CVC5_WRAPPER]
    assert os.access(kind2.CVC5_WRAPPER, os.X_OK)
    env = kind2.solver_env("cvc5-mbqi")
    assert env["KINDHML_CVC5_REAL"] == str(cvc5)
    out = subprocess.run([kind2.CVC5_WRAPPER, "--lang=smt2", "--incremental"], env=env,
                         capture_output=True, text=True).stdout.split()
    assert out == ["--lang=smt2", "--incremental", "--no-cegqi", "--no-sygus-inst"]
    out = subprocess.run([kind2.CVC5_WRAPPER, "--version"], env=env,
                         capture_output=True, text=True).stdout.split()
    assert out == ["--version"]
    assert kind2.solver_env("z3") is None
    monkeypatch.setenv("KINDHML_CVC5_OPTIONS", "kind2")
    assert kind2.solver_args("cvc5-mbqi") == ["--smt_solver", "cvc5"]
    assert kind2.solver_env("cvc5-mbqi") is None


def test_method_names_the_engine():
    """A verdict of Kind 2 has the method kind2-<ENGINE> (verify.kind2_method)."""
    from kindhml.verify import kind2_method
    out = {p.name: kind2_method(p) for p in parse_text(TEXT).properties}
    assert out == {"L": "kind2-IND2", "P": "kind2-IC3IA", "Q": "kind2-BMC", "R": "kind2",
                   "S": "kind2"}
    assert kind2_method(None) == "kind2"


def test_timeout_before_the_analysis():
    """When the time limit expires before the analysis (e.g. while parsing a large
    program), Kind 2 reports its timeout exception as an error, with no summary
    (outputs of Kind 2 v2.3.0)."""
    text = (" kind2 v2.3.0-467-gc2817d4\n\n<Error> Error opening input file '/tmp/task.lus':\n"
            "        Lib.TimeoutWall\n")
    out = parse_text(text)
    assert out.properties == [] and out.timed_out
    raw = ('[\n{\n  "objectType" : "log",\n  "level" : "fatal",\n  "source" : "parse",\n'
           '  "value" : "Error opening input file \'/tmp/task.lus\':\\nLib.TimeoutWall"\n}\n]\n')
    out = parse_output(raw)
    assert out.properties == [] and out.timed_out
    assert parse_text(TEXT).timed_out                  # the timeout after the summary
    assert not parse_text(TEXT.replace("<Timeout> Wallclock timeout.\n", "")).timed_out
    assert not parse_output(RAW).timed_out


def test_text_output_of_a_killed_run():
    """Answers are printed when found, before the summary."""
    out = parse_text(TEXT[:TEXT.index("----")])
    assert {p.name: p.status for p in out.properties} == {"L": "valid", "P": "valid",
                                                          "Q": "invalid"}


def test_counterexample_with_reals():
    """Kind 2 writes a real as {"num": n, "den": d} (output of Kind 2 v2.3.0)."""
    cex = [{"name": "main", "streams": [
        {"name": "t.value", "type": "real",
         "instantValues": [[0, {"num": 0, "den": 1}], [1, {"num": 3, "den": 2}],
                           [2, {"num": 1, "den": 1}]]},
        {"name": "s.revert", "type": "bool",
         "instantValues": [[0, False], [1, True], [2, False]]}]}]
    rows = format_counterexample(cex).splitlines()
    assert rows[1].split() == ["t.value", "|", "0", "|", "3/2", "|"]
    assert rows[2].split() == ["s.revert", "|", "False", "|", "True", "|", "False"]


def test_the_last_transaction_is_blank():
    """A counterexample with k transactions has k + 1 steps; the transaction of the last step
    is not taken, and its cells are blank (the inputs ib and the state are shown)."""
    cex = [{"name": "main", "streams": [
        {"name": "t.sender", "type": "address", "instantValues": [[0, "A_u1"], [1, "A_u2"]]},
        {"name": "ib.k_u1", "type": "int", "instantValues": [[0, 5], [1, 0]]},
        {"name": "s.revert", "type": "bool", "instantValues": [[0, False], [1, False]]}]}]
    rows = format_counterexample(cex).splitlines()
    assert rows[0].split() == ["|", "step", "0", "|", "step", "1"]
    assert rows[1].split() == ["t.sender", "|", "A_u1", "|"]
    assert rows[2].split() == ["ib.k_u1", "|", "5", "|", "0"]
    assert rows[3].split() == ["s.revert", "|", "False", "|", "False"]
