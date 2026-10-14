"""Cutoffs and the parameterized mode (`cutoff.py`; DESIGN.md, Sect. 7)."""

import os

import pytest

from kindhml import invgen, kind2
from kindhml import lustre as L
from kindhml import syntax as S
from kindhml import verify as V
from kindhml.builder import parse, parse_expr
from kindhml.concrete import state_literal
from kindhml.cutoff import OutOfFragment, Scanner
from kindhml.encode_trans import Encoder
from kindhml.invariants import Checks
from kindhml.lustre_eval import Evaluator
from kindhml.model import System
from kindhml.reference import Interpreter
from kindhml.typecheck import check, check_rule

import test_trans as T

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REGISTRY = os.path.join(ROOT, "tests", "contracts", "parameterized", "registry.sol")

try:
    kind2.find_kind2()
    HAVE_KIND2 = True
except FileNotFoundError:
    HAVE_KIND2 = False

SOURCE = """
contract C {
    mapping (address => int) m;
    address owner;
    int x;
    constructor (address o) { owner = o }
    function f(address a, int k) { m[a] = k }
    function g() { x = x + 1 }
}
"""


def formula(text: str) -> S.Expr:
    program, _ = check(parse(SOURCE))
    return check_rule(program, S.Rule("R", parse_expr(text))).formula


@pytest.mark.parametrize("text, skolems, dual", [
    ("forall a : address . m[a] >= 0", 1, False),
    ("exists a : address . m[a] > 0", 0, True),
    ("forall k : int . exists a : address . m[a] == k", 0, True),
    ("(forall a : address . m[a] >= 0) && (forall b : address . m[b] <= 5)", 1, False),
    ("(forall a : address . m[a] >= 0) || (forall b : address . m[b] <= 5)", 2, False),
    ("forall a : address . forall b : address . m[a] == m[b]", 2, False),
    ("(exists a : address . m[a] > 0) -> (forall b : address . m[b] > 0)", 2, False),
    ("exists h : method . forall a : address . m[a] >= 0", 2, False),    # 2 methods
    ("forall a : address . << a : C . f(a, 1) >> m[a] == 1", 1, False),
    # only the address parameter of f counts: method variables do not denote constructors
    ("forall a : address . forall h : method . forall args : calldataargs ."
     " << a : C . h(args) >> m[a] >= 0", 2, False),
    ("exists h : method . exists args : calldataargs . << null : C . h(args) >> x > 0", 0, True),
])
def test_skolem_constants(text, skolems, dual):
    program, _ = check(parse(SOURCE))
    scan = Scanner(System.make(program, 1))
    assert scan.skolems(formula(text), positive=True) == skolems
    assert scan.dual(formula(text)) == dual


def test_address_existential_under_a_universal():
    """¬χ = ∀k ∃a ...: a Skolem function from the integers to the addresses."""
    program, _ = check(parse(SOURCE))
    with pytest.raises(OutOfFragment):
        Scanner(System.make(program, 1)).skolems(
            formula("exists k : int . forall a : address . m[a] <= k"), positive=True)


def test_cutoffs_of_the_benchmarks():
    bank, _ = V.load(os.path.join(ROOT, "contracts", "bank", "bank.sol"))
    _, _, cut = V.effective_users({}, bank, 100, V.DEFAULT_MODE, V.DEFAULT_EXPAND, True, True)
    assert cut.steps == 2 and cut.of_rule("Liquidity") == 2
    assert cut.checks["rule No_frontrun_deposit"] == 2 and cut.checks["rule Liquidity"] == 1
    # P1_true: forall c1 c2 . exists c3 v12 v3 . forall addr ...
    additivity, _ = V.load(os.path.join(ROOT, "contracts", "regression", "additivity.sol"))
    args = (V.DEFAULT_MODE, V.DEFAULT_EXPAND, True, True)
    users, ghost, cut = V.effective_users({}, additivity, 100, *args)
    assert (users, ghost, sorted(cut.outside)) == (1, True, ["P1_true", "P2_false"])
    assert "under a universal" in cut.outside["P1_true"]
    assert V.effective_users({}, additivity, 100, *args, additivity.rule("P1_true"))[:2] == \
        (100, False)
    assert V.effective_users({}, additivity, 100, *args, additivity.rule("P3_true"))[:2] == \
        (1, True)


def test_steps_of_houdini_have_their_own_cutoffs():
    """In parameterized mode, each step is checked with the cutoff of that step for the
    current candidates (vault: its procedures have different address parameters)."""
    program, _ = V.load(os.path.join(ROOT, "contracts", "vault", "vault.sol"))
    invs = V._Invariants.make(program, 5, V.DEFAULT_MODE, V.DEFAULT_EXPAND, invgen=False,
                              ghost_sums=True)
    names = invs.candidates
    users = {}
    for _, c, p, checks in invs._steps(names):
        users[p.name] = checks.enc.system.n_users
        assert users[p.name] == max(1, invs.checks.step_count(names, c, p))
    assert len(set(users.values())) > 1, users


def test_effective_users():
    """The cutoff if it is at most the number of users asked for, with sums as state
    variables; otherwise the number asked for, as without parameterized mode."""
    program, _ = V.load(REGISTRY)
    args = (V.DEFAULT_MODE, V.DEFAULT_EXPAND, True, True)
    assert V.effective_users({}, program, 100, *args)[:2] == (2, True)
    assert V.effective_users({}, program, 2, *args)[:2] == (2, True)
    assert V.effective_users({}, program, 1, *args)[:2] == (1, False)


def test_default_mode_expands_sums():
    program, _ = V.load(REGISTRY)
    rule = check_rule(program, S.Rule("S", parse_expr("sum(registered) == count")))
    assert "sum_Registry_registered" not in V.lustre_for(program, rule, 2)
    assert "sum_Registry_registered" in V.lustre_for(program, rule, 2, ghost_sums=True)


def with_sums(path: str) -> S.Program:
    """The program of `path` with rules summing every map to numbers, and the balances."""
    program, _ = check(parse(open(path).read()))
    rules = [check_rule(program, S.Rule("_sum_balance", parse_expr("sum(balance) >= 0")))]
    rules += invgen.candidates(program)            # sum(m) == f, ... for the fields f
    return S.Program(program.contracts, program.rules + tuple(rules), program.balance_type)


@pytest.mark.parametrize("path", T.FILES, ids=os.path.basename)
def test_ghost_sums_match_reference(path):
    """With sums as state variables, `trans` evaluated in Python agrees with the reference
    interpreter, sums included (`state_literal` writes the sums of the entries)."""
    system = System.make(with_sums(path), 2, ghost_sums=True)
    enc = Encoder(system)
    assert enc.ghosts
    prog, _ = enc.program()
    ev = Evaluator(prog)
    interp = Interpreter(system)
    for i, st, tx, expected in T.samples(system, interp, T.random.Random(path), 100):
        actual = ev.eval(L.call("trans", state_literal(st, system, enc),
                                T.tx_literal(tx, system, enc)), {})
        assert actual == ev.eval(state_literal(expected, system, enc), {}), (i, st, tx)


def test_sum_axioms_need_nonnegative_entries():
    """The bounds by sum(m) are assumed only with premises making the entries of m
    nonnegative (`forall u. m[u] >= 0` and `m[null] >= 0`)."""
    program, _ = V.load(REGISTRY)
    invariants = [check_rule(program, S.Rule(name, parse_expr(text), invariant=True))
                  for name, text in [("Every", "forall u : address . registered[u] >= 0"),
                                     ("Null", "registered[null] >= 0"),
                                     ("Total", "sum(registered) == count")]]
    extended = S.Program(program.contracts, program.rules + tuple(invariants),
                         program.balance_type)
    checks = Checks(extended, 2, V.DEFAULT_MODE, V.DEFAULT_EXPAND, ghost_sums=True)
    s = L.Var("s")
    assert checks.sum_axioms(["Every", "Total"], s) == L.TRUE
    assert checks.sum_axioms(["Null", "Total"], s) == L.TRUE
    assert "sum_Registry_registered" in L.render(checks.sum_axioms(["Every", "Null"], s))


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_parameterized_registry():
    """With 3 users asked for, the checks use 2: the rules true for every number of users
    are proved for every n >= 2; At_most_two, false with 3 users, is not proved. Without
    parameterized mode, it is proved with 2 users and refuted with 3."""
    program, _ = V.load(REGISTRY)
    context: dict = {}
    V.prove_invariants(program, 3, 30, context, parameterized=True)
    out = {r.name: V.verify(program, r, 3, 20, context=context, parameterized=True)
           for r in V.tasks(program)}
    for name in ("Flags", "Count_nonnegative", "Registered_bounded"):
        assert out[name].status == "valid", out[name].describe()
        assert out[name].scope.startswith("for every n >= 2 users"), out[name].scope
    assert out["At_most_two"].status == "unknown"
    rule = program.rule("At_most_two")
    for n, status in ((2, "valid"), (3, "invalid")):
        context = {}
        V.prove_invariants(program, n, 30, context)
        assert V.verify(program, rule, n, 20, context=context).status == status
