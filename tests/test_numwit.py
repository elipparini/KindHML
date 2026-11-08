"""Numeric witnesses of existentials (`numwit.py`): instances found from samples, and proofs
for every number of users through them."""

import os

import pytest

from kindhml import numwit
from kindhml import pretty
from kindhml import syntax as S
from kindhml import verify as V
from kindhml.fuzz import Fuzzer
from kindhml.model import System

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ADDITIVITY = os.path.join(ROOT, "contracts", "regression", "additivity.sol")
DIVISION = os.path.join(ROOT, "contracts", "regression", "division.sol")


def _exists(e) -> bool:
    if isinstance(e, S.Quant) and e.kind == "exists":
        return True
    return any(_exists(x) for n in getattr(e, "__dataclass_fields__", ())
               for x in (getattr(e, n) if isinstance(getattr(e, n), tuple)
                         else (getattr(e, n),)) if isinstance(x, S.Expr))


@pytest.mark.parametrize("path, want", [(ADDITIVITY, "c3 := (c1 + c2)"),
                                        (DIVISION, "c3 := (c1 * c2)")])
def test_the_witnesses_of_a_block_of_existentials(path, want):
    """forall c1 c2 . exists c3 v12 v3 . forall a . ...: c3 from the candidate terms, v12 and
    v3 (storage variables) from the values of v after the calls."""
    program, _ = V.load(path)
    found = numwit.instances(program, program.prop("P1_true"),
                             Fuzzer(System.make(program, 2), "t1"))
    assert found, "no instance"
    text, inst = found[0]
    assert text.startswith(want), text
    assert not _exists(inst.formula)


def test_no_witness_for_a_false_property():
    """additivity P2_false: c3 is universal, v12 == v3 fails for some c3: its instance (the
    storage terms) is found, and is false (its check refutes it, nothing is proved)."""
    program, _ = V.load(ADDITIVITY)
    found = numwit.instances(program, program.prop("P2_false"),
                             Fuzzer(System.make(program, 2), "t1"))
    assert found == [] or all("v12_storage" in t for t, _ in found)


@pytest.mark.kind2
@pytest.mark.parametrize("path", [ADDITIVITY, DIVISION])
def test_a_numeric_instance_proves_the_property_for_every_n(path):
    """No cutoff (an address universal under the existentials), true for every n: proved
    through the instance, which is universal."""
    program, _ = V.load(path)
    o = V.verify(program, program.prop("P1_true"), V.ANY, 300, users_mode="combined")
    assert o.status == "valid", o.describe()
    assert "for the instance" in o.scope, o.scope


NUMWIT = os.path.join(ROOT, "tests", "contracts", "witness", "numwit.sol")


def _guarded(inst: S.Property, term: str) -> bool:
    """Whether the body under the universal prefix of an instance is `term >= 0 && ...`."""
    e = inst.formula
    while isinstance(e, S.Quant) and e.kind == "forall":
        e = e.body
    return (isinstance(e, S.BinOp) and e.op == "&&" and isinstance(e.left, S.BinOp)
            and e.left.op == ">=" and pretty.expr(e.left.left) == term)


def test_an_existential_over_a_uint_has_the_conjunct_of_its_domain():
    """A uint y ranges over the naturals: its instance y := t has the conjunct t >= 0,
    without which Uint_false (false) would be proved through d := c."""
    program, _ = V.load(NUMWIT)
    found = numwit.instances(program, program.prop("Uint_true"),
                             Fuzzer(System.make(program, 2), "t1"))
    assert found, "no instance"
    text, inst = found[0]
    assert text == "d := (c * c)", text
    assert _guarded(inst, "(c * c)"), pretty.expr(inst.formula)
    for text, inst in numwit.instances(program, program.prop("Uint_false"),
                                       Fuzzer(System.make(program, 2), "t1")):
        assert _guarded(inst, text.split(" := ")[1]), text


def test_an_existential_under_old():
    """old(y) under one modality is y at the state of the existential: y := v gives
    old(v) == old(v), not old(old(v)), which is above the state of the property."""
    program, _ = V.load(NUMWIT)
    found = numwit.instances(program, program.prop("Old_true"),
                             Fuzzer(System.make(program, 2), "t1"))
    assert found and found[0][0] == "y := v", found
    assert "old(old(" not in pretty.expr(found[0][1].formula)


def test_the_depth_of_a_substitution():
    y = S.QVar("y", S.INT)
    v = S.Field("Counter", "v")
    at = lambda body: S.Modal(sender=S.QVar("a", S.ADDRESS), contract="Counter",
                              proc=S.ProcConst("Counter", "add"), args=(S.IntLit(1),),
                              value=S.IntLit(0), blocks=S.IntLit(0), body=body)
    e = at(S.BinOp("==", S.Old(y), y))
    out = numwit._substitute(e, {"y": v})
    assert out.body.left == S.Old(v) and out.body.right == S.Old(v)
    with pytest.raises(ValueError):
        numwit._substitute(S.Old(y), {"y": v})


@pytest.mark.kind2
@pytest.mark.parametrize("name, status", [("Uint_false", "invalid"), ("Uint_true", "valid"),
                                          ("Old_true", "valid")])
def test_numeric_instances_with_uint_and_old(name, status):
    program, _ = V.load(NUMWIT)
    o = V.verify(program, program.prop(name), V.ANY, 300, users_mode="combined")
    assert o.status == status, o.describe()
    if status == "valid":
        assert "for the instance" in o.scope, o.scope
