"""Reduction by symmetry of the checks on free states (`encode_formula.FormulaEncoder`,
`symmetric`; DESIGN.md, Sect. 7.7): a universal address quantifier in positive position needs
one value per pattern of equalities with the users bound around it."""

import re

import pytest

from kindhml import lustre as L
from kindhml import verify as V
from kindhml.builder import parse
from kindhml.invariants import Checks
from kindhml.typecheck import check

SOURCE = """
pragma balance real;
contract C {
    mapping (address => real) m;
    function set(real v) { m[msg.sender] = v }
}
property Pairs { forall a : address . forall b : address . m[a] - m[b] <= m[a] - m[b] }
property Either { (forall a : address . m[a] > 0.0) || (forall b : address . m[b] <= 0.0) }
property Some { exists a : address . forall b : address . m[b] <= m[a] }
property Premise { (forall a : address . m[a] >= 0.0) -> m[null] >= 0.0 }
property After { forall a : address . << a : C.set(1.0) >> forall b : address . m[b] <= 1.0 }
"""


def program():
    return check(parse(SOURCE))[0]


def users_in(e: L.LExpr) -> set:
    """The users named in e, as address constants or as the fields of map entries."""
    return {f"A_{u}" for u in re.findall(r"(?:A_|k_)(u\d+)", L.render(e))}


def goal(name, users=4, symmetric=True):
    p = program()
    return Checks(p, users, "inline", ("address", "method"))._property(p.prop(name),
                                                                    L.Var("s"), symmetric)


def test_one_case_per_pattern():
    """(a, b) over the contract C and 4 users: a in {C, u1}; b in {C, u1} if a = C, in
    {C, u1, u2} if a = u1: 5 cases instead of 25."""
    p = program()
    c = Checks(p, 4, "inline", ("address", "method"))
    names, _ = c.property_goals(p.prop("Pairs"), [], split=True)
    assert len(names) == 5
    assert users_in(goal("Pairs")) == {"A_u1", "A_u2"}
    assert users_in(goal("Pairs", symmetric=False)) == {"A_u1", "A_u2", "A_u3", "A_u4"}


def test_no_reduction_in_a_disjunction_an_existential_or_a_premise():
    """In `(forall a . A) || (forall b . B)` the two quantifiers need their patterns together
    (b = u2 with a = u1 is not covered by a per-quantifier choice); an existential or a
    premise is not a universal in positive position."""
    for name in ("Either", "Some", "Premise"):
        assert users_in(goal(name)) == {"A_u1", "A_u2", "A_u3", "A_u4"}, name


def test_reduction_through_a_modality():
    """⟨t⟩∀b.ψ ⟺ ∀b.⟨t⟩ψ: b ranges over C, the sender u1 and one more user."""
    assert users_in(goal("After")) == {"A_u1", "A_u2"}


ARGUMENT = """
pragma balance real;
contract C {
    mapping (address => real) m;
    bool f;
    address owner;
    function own() { owner = msg.sender }
    function set(real v) { m[msg.sender] = v }
    function g(bool x) { f = x }
}
property P {
    << owner : C.g(forall b : address . (is_EOA(b) -> m[b] >= 0.0)) >>
    forall a : address . (is_EOA(a) -> (lastReverted || f || m[a] < 0.0))
}
"""


def test_no_reduction_in_the_arguments_of_a_modality():
    """A quantified argument of a modality is a term, not a formula in positive position:
    reduced, P (false with m[u1] = 0, m[u2] = -1) would be valid (found by an audit)."""
    p = check(parse(ARGUMENT))[0]
    c = Checks(p, 2, "inline", ("address", "method"))
    e = c._property(p.prop("P"), L.Var("s"), True)
    assert {"A_u1", "A_u2"} <= users_in(e)


@pytest.mark.kind2
def test_a_quantified_argument_is_refuted_on_free_states():
    p = check(parse(ARGUMENT))[0]
    c = Checks(p, 2, "inline", ("address", "method"))
    lus, names = c.property_check(p.prop("P"), [])
    assert V._free_run(lus, names, 30)[0] == "invalid"


def test_no_reduction_at_a_concrete_state():
    p = program()
    c = Checks(p, 4, "inline", ("address", "method"))
    st = L.Var("s")
    assert users_in(c.concrete_goal(p.prop("Pairs"), st)) == {"A_u1", "A_u2", "A_u3", "A_u4"}


@pytest.mark.kind2
def test_a_disjunction_is_still_refuted_on_free_states():
    """Either is false on a free state (m[u1] = 1, m[u2] = 0); with a reduction that chose b
    like a, its check would be valid."""
    p = program()
    c = Checks(p, 2, "inline", ("address", "method"))
    lus, names = c.property_check(p.prop("Either"), [])
    assert V._free_run(lus, names, 30)[0] == "invalid"
    lus, names = c.property_check(p.prop("Pairs"), [], split=True)
    assert V._free_run(lus, names, 30)[0] == "valid"
