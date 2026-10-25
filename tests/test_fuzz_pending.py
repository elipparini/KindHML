"""Undecided candidates of the fuzzer are checked again in later rounds (`verify._rounds`,
PENDING_MAX): on lending-simple-real Liquidation_attack_any, a candidate took 45-160 s to find
and its exact check about 45 s, more than the fuzzing budget of a round."""

import os

from kindhml import verify as V

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPAY = os.path.join(ROOT, "tests", "contracts", "fuzz", "repay.sol")


def test_an_undecided_candidate_is_refuted_in_a_later_round(monkeypatch):
    """Every first exact check of a state is made undecided, and the other tasks decide
    nothing: only the check again of a kept candidate can refute the property."""
    real = V._free_run
    seen, retried = set(), []

    def free_run(lus, names, budget):
        if "at a concrete state" not in lus:
            return "unknown", None, ""
        if lus not in seen:
            seen.add(lus)
            return "unknown", None, ""
        retried.append(lus)
        return real(lus, names, budget)

    monkeypatch.setattr(V, "_free_run", free_run)
    monkeypatch.setattr(V, "kind2_search", lambda prop, *a, **k: V.Outcome(
        prop, V.kind2.PropertyResult(prop.name, "unknown"), []))
    program, _ = V.load(REPAY)
    o = V.verify(program, program.prop("Never_repaid"), 1, 120)
    assert (o.status, o.method) == ("invalid", "fuzz")
    assert retried
