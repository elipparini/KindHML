"""Reading Kind 2's JSON and plain-text outputs (no Kind 2 needed)."""

from kindhml.kind2 import format_counterexample, parse_output, parse_text

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
         "instantValues": [[0, {"num": 0, "den": 1}], [1, {"num": 3, "den": 2}]]},
        {"name": "s.revert", "type": "bool", "instantValues": [[0, False], [1, True]]}]}]
    rows = format_counterexample(cex).splitlines()
    assert rows[1].split() == ["t.value", "|", "0", "|", "3/2"]
    assert rows[2].split() == ["s.revert", "|", "False", "|", "True"]
