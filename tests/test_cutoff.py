"""Cutoffs and the parameterized mode (`cutoff.py`; DESIGN.md, Sect. 7)."""

import os
from dataclasses import replace

import pytest

from kindhml import invgen, kind2
from kindhml import lustre as L
from kindhml import syntax as S
from kindhml import verify as V
from kindhml.builder import parse, parse_expr
from kindhml.concrete import state_from_values, state_literal, state_paths
from kindhml.cutoff import OutOfFragment, Scanner, idle_users
from kindhml.encode_trans import Encoder
from kindhml.errors import KindHMLError
from kindhml.invariants import Checks
from kindhml.lustre_eval import Evaluator
from kindhml.model import System
from kindhml.reference import Interpreter, Tx, initial_state
from kindhml.typecheck import check, check_property

import test_trans as T

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REGISTRY = os.path.join(ROOT, "tests", "contracts", "parameterized", "registry.sol")
CAPPED = os.path.join(ROOT, "tests", "contracts", "parameterized", "capped_registry.sol")
SHARES = os.path.join(ROOT, "tests", "contracts", "parameterized", "shares.sol")
POOL = os.path.join(ROOT, "contracts", "regression", "pool.sol")

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
    return check_property(program, S.Property("R", parse_expr(text))).formula


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


@pytest.mark.parametrize("text, needed", [
    ("forall a : address . m[a] >= 0", 0),                      # Lemma 7.5
    ("exists a : address . m[a] > 0", 1),
    # ¬: forall a . exists b: the existential after the last universal needs no idle user
    ("exists a : address . forall b : address . m[a] >= m[b]", 1),
    # ¬: exists a . forall b: the witness of a may be an idle user
    ("forall a : address . exists b : address . m[b] > m[a]", 2),
    ("exists h : method . exists args : calldataargs . << null : C . h(args) >> x > 0", 1),
])
def test_idle_users_needed(text, needed):
    program, _ = check(parse(SOURCE))
    assert Scanner(System.make(program, 1)).idle_needed(formula(text)) == needed


def test_idle_users():
    """Idle: every map entry has its default value, and no address field holds the user;
    grouped by balance."""
    program, _ = check(parse(SOURCE))
    system = System.make(program, 4)
    state = {"s.C_owner": "u1", "s.C_x": 3}
    for a in system.addresses:
        state[f"s.C_m.k_{a}"] = 5 if a == "u2" else 0
        state[f"s.balance.k_{a}"] = 7 if a == "u4" else 0
    assert idle_users(state, system) == {0: ["u3"], 7: ["u4"]}
    del state["s.C_m.k_u3"]                     # a missing value: not idle
    assert idle_users(state, system) == {7: ["u4"]}


def test_participants_of_a_counterexample():
    """The users named by the transactions taken (all steps but the last): the sender, the
    called address and the address arguments of the procedure called, not those of the
    other procedures."""
    program, _ = check(parse(SOURCE))
    stream = lambda name, *vs: {"name": name, "instantValues": [[i, v] for i, v in enumerate(vs)]}
    cex = [{"streams": [stream("t.sender", "A_u1", "A_u2", "A_u3"),
                        stream("t.cx", "A_C", "A_C", "A_u4"),
                        stream("t.fx", "P_C_constructor", "P_C_f", "P_C_f"),
                        stream("t.C_constructor_o", "A_u5", "A_u6", "A_u6"),
                        stream("t.C_f_a", "A_u7", "A_u8", "A_u9"),
                        stream("s.C_x", 0, 0, 0)]}]
    assert V._participants(cex, System.make(program, 9)) == {"u1", "u2", "C", "u5", "u8"}


def test_address_existential_under_a_universal():
    """¬χ = ∀k ∃a ...: a Skolem function from the integers to the addresses."""
    program, _ = check(parse(SOURCE))
    with pytest.raises(OutOfFragment):
        Scanner(System.make(program, 1)).skolems(
            formula("exists k : int . forall a : address . m[a] <= k"), positive=True)


def test_cutoffs_of_the_benchmarks():
    bank, _ = V.load(os.path.join(ROOT, "contracts", "bank", "bank.sol"))
    _, _, cut = V.effective_users({}, bank, 100, V.DEFAULT_MODE, V.DEFAULT_EXPAND, True, True)
    assert cut.steps == 2 and cut.of_property("Liquidity") == 2
    assert cut.checks["property No_frontrun_deposit"] == 2 and cut.checks["property Liquidity"] == 1
    # P1_true: forall c1 c2 . exists c3 v12 v3 . forall addr ...
    additivity, _ = V.load(os.path.join(ROOT, "contracts", "regression", "additivity.sol"))
    args = (V.DEFAULT_MODE, V.DEFAULT_EXPAND, True, True)
    users, ghost, cut = V.effective_users({}, additivity, 100, *args)
    assert (users, ghost, sorted(cut.outside)) == (1, True, ["P1_true", "P2_false"])
    assert "under a universal" in cut.outside["P1_true"]
    assert V.effective_users({}, additivity, 100, *args, additivity.prop("P1_true"))[:2] == \
        (100, False)
    assert V.effective_users({}, additivity, 100, *args, additivity.prop("P3_true"))[:2] == \
        (1, True)


LEMMAS = """
contract C {
    mapping (address => int) m;
    int t;
    constructor () { t = 0 }
    function put() { require(m[msg.sender] == 0); m[msg.sender] = 1; t = t + 1 }
}
property Small { t >= 0 }
invariant Four {
    (forall a : address . forall b : address . forall d : address .
        m[a] + m[b] + m[d] >= 0 || m[a] + m[b] + m[d] < 0)
    && (exists x1 : address . exists x2 : address . exists x3 : address .
        exists x4 : address . x1 != x2 && x1 != x3 && x1 != x4 && x2 != x3 && x2 != x4
        && x3 != x4)
}
invariant Max { exists b : address . forall a : address . m[a] <= m[b] }
"""


def test_cutoffs_of_lemmas():
    """Every property has its cutoff, also a lemma (no task, but it can be checked by
    name). Without the invariants of the file as candidates, the cutoff of the steps is 1,
    that of Four 3 (Four is false with 2 users: 4 distinct addresses are needed), and Max is
    outside the fragment. Before, both had the cutoff of the steps: Four was "valid" with 2
    users, and the check of Max raised OutOfFragment."""
    program, _ = check(parse(LEMMAS))
    program = replace(program, properties=tuple(replace(r, lemma=r.invariant)
                                                for r in program.properties))
    cut = V.cutoff_of({}, program, V.DEFAULT_MODE, V.DEFAULT_EXPAND, False, False)
    assert (cut.steps, cut.of_property("Small"), cut.of_property("Four"),
            cut.of_property("Max")) == (1, 1, 3, None)
    assert V.effective_users({}, program, 2, V.DEFAULT_MODE, V.DEFAULT_EXPAND, False, False,
                             program.prop("Four"))[:2] == (2, False)
    assert V.Cutoff(1).of_property("Small") is None         # a count not computed


def test_names_of_the_tool_are_reserved():
    """A property named like a built-in lemma or a generated invariant would replace it as a
    premise: such names are rejected."""
    for name in ("_lemma_balances_nonnegative", "_gen_0"):
        with pytest.raises(KindHMLError, match="reserved"):
            check(parse("contract C { int t; constructor () { t = 0 } }\n"
                        f"invariant {name} {{ t == 5 }}"))


def test_invariants_without_candidates_keep_their_sums():
    """Without the invariants of the file as candidates (--no_user_invariants), an invariant
    is still checked, as a property: in parameterized mode, its sums need their state
    variables (before, "sum(...) of a map without its state variable")."""
    program, _ = V.load(SHARES)
    invs = V._Invariants.make(program, 3, V.DEFAULT_MODE, V.DEFAULT_EXPAND, invgen=False,
                              user_invariants=False, ghost_sums=True)
    assert invs.candidates == []
    prop = program.prop("Total")
    for premises in invs.checks.premises(prop, invs.assumed()):
        invs.checks.property_check(prop, premises, False)


def test_state_paths_keep_the_whole_state():
    """The final state of a fuzzer's counterexample, by path, gives the same state back:
    with the construction flags (before, `normalized` rebuilt a state where no contract was
    constructed, at which the property held)."""
    program, _ = check(parse(SOURCE))
    system = System.make(program, 2)
    st = Interpreter(system).step(initial_state(system, {"u1": 5, "u2": 7}),
                                  Tx("u1", "C", ("C", "constructor"), args={"o": "u2"}))
    back = state_from_values(state_paths(st, system), system, Encoder(system))
    assert st.constructed == {"C": True}
    assert (back.constructed, back.balance, back.fields, back.revert) == \
        (st.constructed, st.balance, st.fields, st.revert)


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
    prop = check_property(program, S.Property("S", parse_expr("sum(registered) == count")))
    assert "sum_Registry_registered" not in V.lustre_for(program, prop, 2)
    assert "sum_Registry_registered" in V.lustre_for(program, prop, 2, ghost_sums=True)


def with_sums(path: str) -> S.Program:
    """The program of `path` with properties summing every map to numbers, and the balances."""
    program, _ = check(parse(open(path).read()))
    properties = [check_property(program,
                                 S.Property("_sum_balance", parse_expr("sum(balance) >= 0")))]
    properties += invgen.candidates(program)            # sum(m) == f, ... for the fields f
    return S.Program(program.contracts, program.properties + tuple(properties),
                     program.balance_type)


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
    invariants = [check_property(program, S.Property(name, parse_expr(text), invariant=True))
                  for name, text in [("Every", "forall u : address . registered[u] >= 0"),
                                     ("Null", "registered[null] >= 0"),
                                     ("Total", "sum(registered) == count")]]
    extended = S.Program(program.contracts, program.properties + tuple(invariants),
                         program.balance_type)
    checks = Checks(extended, 2, V.DEFAULT_MODE, V.DEFAULT_EXPAND, ghost_sums=True)
    s = L.Var("s")
    assert checks.sum_axioms(["Every", "Total"], s) == L.TRUE
    assert checks.sum_axioms(["Null", "Total"], s) == L.TRUE
    axiom = L.render(checks.sum_axioms(["Every", "Null"], s))
    # one bound: the sum of the entries at all the addresses is at most the sum variable
    assert axiom.count("<= s.sum_Registry_registered") == 1
    assert all(f"s.Registry_registered.k_{a}" in axiom for a in checks.enc.system.addresses)


def test_witness_premises():
    """The witness premise of a sum (if the entries at null and at the contracts do not add
    up to it, a user has a nonzero entry) is for the sums of the property and of its
    premises; it adds one user to the cutoff of the check."""
    program, _ = V.load(POOL)
    checks = Checks(program, 2, V.DEFAULT_MODE, V.DEFAULT_EXPAND, ghost_sums=True)
    prop = program.prop("Someone_deposited")
    deposit = ("Pool", "deposit")
    assert checks.witness_maps([], prop) == []          # the property has no sum
    assert checks.witness_maps(["Nonnegative"], prop) == []
    assert checks.witness_maps(["Sum"], prop) == [deposit]
    assert checks.property_count(["Sum"], prop, [deposit]) == \
        checks.property_count(["Sum"], prop) + 1
    axiom = L.render(checks.witness_axioms([deposit], L.Var("s")))
    assert axiom == ("((not (s.sum_Pool_deposit = (s.Pool_deposit.k_null + s.Pool_deposit.k_Pool)))"
                     " => ((not (s.Pool_deposit.k_u1 = 0)) or (not (s.Pool_deposit.k_u2 = 0))))")
    assert axiom in checks.property_check(prop, ["Sum"], witnesses=[deposit])[0]
    assert axiom not in checks.property_check(prop, ["Sum"])[0]


def registry_with(*invariants) -> S.Program:
    """The registry with the given invariants (name, text) added."""
    program, _ = V.load(REGISTRY)
    extra = [check_property(program, S.Property(name, parse_expr(text), invariant=True))
             for name, text in invariants]
    return S.Program(program.contracts, program.properties + tuple(extra),
                     program.balance_type)


def test_nonnegative_maps_in_conjunctions():
    """The entries of a map are nonnegative also by conjuncts of the premises, as in the
    declared invariants of the use cases."""
    program = registry_with(
        ("Both", "(forall u : address . registered[u] >= 0 && registered[u] <= 1)"
                 " && count >= 0"),
        ("Null", "count >= 0 && registered[null] == 0"),
        ("Total", "sum(registered) == count"))
    checks = Checks(program, 2, V.DEFAULT_MODE, V.DEFAULT_EXPAND, ghost_sums=True)
    assert "sum_Registry_registered" in L.render(checks.sum_axioms(["Both", "Null"], L.Var("s")))
    assert checks.sum_axioms(["Both"], L.Var("s")) == L.TRUE


def test_replay_keeps_the_sums_of_a_free_state():
    """Parameterized mode: in a free state, sum(registered) also counts users outside the
    system; replaying `register` from it keeps `sum(registered) == count`."""
    program = registry_with(("Total", "sum(registered) == count"))
    checks = Checks(program, 2, V.DEFAULT_MODE, V.DEFAULT_EXPAND, ghost_sums=True)
    values = {"s.constructed_Registry": True, "s.Registry_count": 5,
              "s.sum_Registry_registered": 5}
    values.update({f"s.Registry_registered.k_{a}": 0 for a in checks.enc.system.addresses})
    cex = [{"streams": [{"name": n, "instantValues": [[0, v]]} for n, v in values.items()]}]
    registry = program.contracts[0]
    assert checks.refuted_after(cex, ["Total"], registry, registry.proc("register")) == set()


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_parameterized_registry():
    """With 3 users asked for, the checks use 2: the properties true for every number of users
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
    assert out["At_most_two"].status != "valid"
    prop = program.prop("At_most_two")
    for n, status in ((2, "valid"), (3, "invalid")):
        context = {}
        V.prove_invariants(program, n, 30, context, users_mode="exact")
        assert V.verify(program, prop, n, 20, context=context,
                        users_mode="exact").status == status


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_combined_registry():
    """Combined mode (the default), 3 users: the properties true for every number of users
    are proved with the cutoff 2, for every n >= 2; At_most_two is refuted with 3 users, and
    proved with 2 users asked for, by the exact side."""
    program, _ = V.load(REGISTRY)
    context: dict = {}
    V.prove_invariants(program, 3, 30, context)
    out = {r.name: V.verify(program, r, 3, 30, context=context) for r in V.tasks(program)}
    for name in ("Flags", "Count_nonnegative", "Registered_bounded"):
        assert out[name].status == "valid", out[name].describe()
        assert out[name].scope.startswith("for every n >= 2 users"), out[name].scope
    assert out["At_most_two"].status == "invalid", out["At_most_two"].describe()
    assert out["At_most_two"].scope == "counterexample with 3 users"
    context = {}
    V.prove_invariants(program, 2, 30, context)
    o = V.verify(program, program.prop("At_most_two"), 2, 30, context=context)
    assert (o.status, o.scope) == ("valid", "only for 2 users"), o.describe()


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_any_number_of_users():
    """Every number of users: Registered_bounded is proved for every n >= 2 by invariants and
    with 1 user; At_most_two, true with at most 2 users, is refuted with 3 (the exact sides go
    on with more users); capped registry, Someone_unregistered is refuted with 2 users (its
    counterexample does not extend, but it is one for n = 2)."""
    program, _ = V.load(REGISTRY)
    context: dict = {}
    V.prove_invariants(program, V.ANY, 30, context)
    o = V.verify(program, program.prop("Registered_bounded"), V.ANY, 60, context=context)
    assert o.status == "valid" and "by invariants" in o.scope, o.describe()
    o = V.verify(program, program.prop("At_most_two"), V.ANY, 120, context=context)
    assert (o.status, o.scope) == ("invalid", "counterexample with 3 users"), o.describe()
    program, _ = V.load(CAPPED)
    context = {}
    V.prove_invariants(program, V.ANY, 30, context)
    o = V.verify(program, program.prop("Someone_unregistered"), V.ANY, 60, context=context)
    assert o.status == "invalid", o.describe()


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_any_number_of_users_without_cutoff():
    """A property outside the fragment, for every number of users: proved with 1, 2, ...
    users, one after the other, until the time limit."""
    program, _ = V.load(os.path.join(ROOT, "contracts", "regression", "additivity.sol"))
    o = V.verify(program, program.prop("P1_true"), V.ANY, 20)
    assert o.status == "unknown" and o.true_for.startswith("up to"), o.describe()


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_sum_of_all_entries_bounds_the_shares():
    """Houdini in parameterized mode proves the invariants of the shares, whose step for
    redeem needs the bound of the sum of all the entries by sum(minted)."""
    program, _ = V.load(SHARES)
    context: dict = {}
    [invs] = V.prove_invariants(program, 5, 60, context, parameterized=True, invgen=False)
    assert sorted(n for n in invs.proved or [] if not n.startswith("_")) == [
        "Nonnegative", "Pairs", "Total"], invs.dropped


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_witness_premises_prove_for_every_number_of_users():
    """Pool, Someone_deposited (total == 0 || exists a . deposit[a] > 0): without the witness
    premise of sum(deposit), the check with the cutoff has a counterexample to induction where
    the depositor is a user outside the system; with it, the property is proved for every
    n >= 2, and with 1 user by the exact side."""
    program, _ = V.load(POOL)
    prop = program.prop("Someone_deposited")
    o = V.verify(program, prop, V.ANY, 60)
    assert (o.status, o.scope) == ("valid", "n >= 2 by invariants, n < 2 one by one"), \
        o.describe()
    o = V.verify(program, prop, 3, 60, parameterized=True)
    assert o.status == "valid" and o.scope.startswith("for every n >= 2 users"), o.describe()


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_address_templates_prove_for_every_number_of_users():
    """price-bet, Winnability: the generated invariants player_has_joined -> player != null
    and player_has_joined -> player != Bet exclude its former counterexample to induction (the
    player null after the join), so the check with the cutoff proves it (before, it was true
    up to 6 users after 600 s)."""
    program, _ = V.load(os.path.join(ROOT, "contracts", "price-bet", "price-bet.sol"))
    o = V.verify(program, program.prop("Winnability"), V.ANY, 120)
    assert (o.status, o.scope) == ("valid", "n >= 5 by invariants, n < 5 one by one"), \
        o.describe()


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_kind2_with_more_users():
    """With 3 users asked for, Kind 2 proves At_most_two with 2 users (the cutoff), not a
    proof for 3 users; it goes on with 3 users and refutes it. The property has no address
    quantifier, so the proof holds for every n <= 2 (Cor. 7.8) and the counterexample for
    every n >= 3 (Lemma 7.5)."""
    program, _ = V.load(REGISTRY)
    context: dict = {}
    V.prove_invariants(program, 3, 30, context, parameterized=True)
    out = V.verify(program, program.prop("At_most_two"), 3, 120, context=context,
                   parameterized=True)
    assert out.status == "invalid", out.describe()
    assert out.scope == ("counterexample with 3 users, for every n >= 3; true up to 2 users"), \
        out.scope


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_kind2_timeout_before_the_analysis_is_unknown():
    """With 2 users, Kind 2 needs more than 1 s to reach the analysis of the vault (on the
    development machine): it stops at its time limit before reporting on the property, which
    is no verdict, not an error."""
    program, _ = V.load(os.path.join(ROOT, "contracts", "vault", "vault.sol"))
    prop = program.prop("Two_steps_drainability_non_inflation")
    out = V.kind2_search(prop, V.lustre_for(program, prop, 2), 1)
    assert out.status == "unknown", out.describe()


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
def test_counterexamples_extend_with_idle_users():
    """With 3 users asked for, the checks use at most 2. The counterexample of
    Someone_registered leaves idle users and holds for every larger number of users
    (Lemma 7.6); that of Someone_unregistered has none and is not extended (the property holds
    with 3 users). With 2 users asked for, Someone_unregistered is refuted."""
    program, _ = V.load(CAPPED)
    context: dict = {}
    V.prove_invariants(program, 3, 30, context, parameterized=True)
    out = {r.name: V.verify(program, r, 3, 20, context=context, parameterized=True)
           for r in V.tasks(program)}
    assert out["Someone_registered"].status == "invalid", out["Someone_registered"].describe()
    assert "for every n >=" in out["Someone_registered"].scope
    assert out["Someone_unregistered"].status != "invalid", \
        out["Someone_unregistered"].describe()
    context = {}
    V.prove_invariants(program, 2, 30, context, parameterized=True)
    prop = program.prop("Someone_unregistered")
    o = V.verify(program, prop, 2, 20, context=context, parameterized=True)
    assert (o.status, o.scope) == ("invalid", "counterexample with 2 users"), o.describe()
