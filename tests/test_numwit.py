"""Numeric witnesses of existentials (`numwit.py`): instances found from samples, and proofs
for every number of users through them."""

import os

import pytest

from kindhml import numwit
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
