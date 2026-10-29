"""Reproducible random choices (2026-10-29): the i-th trace of a stream of the fuzzer, and the
samples of its bounded evaluations, do not depend on the draws made before (other streams,
other properties); the entry points fix the order of the sets of strings (PYTHONHASHSEED)."""

import os
import subprocess
import sys

from kindhml.builder import parse
from kindhml.fuzz import Fuzzer, _key
from kindhml.model import System
from kindhml.typecheck import check

SRC = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "src")

SOURCE = """
pragma balance real;
contract C {
    real r;
    constructor(real r0) { require(r0 >= 1.0); r = r0 }
    function set(real v) { require(v >= 1.0); r = v }
}
property Below { r < 3.0 }
property Above { r > 2.0 }
"""


def program():
    return check(parse(SOURCE))[0]


def trace(f: Fuzzer, stream: str) -> str:
    """The transactions and the last state of the next trace of `stream`, as text."""
    txs, st = list(f.traces(stream))[-1]
    return repr(txs) + _key(st)


def test_a_trace_does_not_depend_on_the_draws_before():
    system = System.make(program(), 2)
    alone, mixed = Fuzzer(system, "t"), Fuzzer(system, "t")
    expected = [trace(alone, "s") for _ in range(20)]
    got = []
    for i in range(20):
        for _ in range(i % 3):
            trace(mixed, "other")
        mixed.rnd.random()
        got.append(trace(mixed, "s"))
    assert got == expected
    assert len(set(expected)) > 1
    assert [trace(Fuzzer(system, "u"), "s") for _ in range(5)] != expected[:5]


def test_the_candidates_of_a_property_do_not_depend_on_those_before():
    p = program()
    system = System.make(p, 1)
    alone = Fuzzer(system, "t").candidates(p.prop("Below"), 30, limit=3)
    f = Fuzzer(system, "t")
    assert f.candidates(p.prop("Above"), 30, limit=2)
    after = f.candidates(p.prop("Below"), 30, limit=3)
    assert len(alone) == 3
    assert [repr(txs) for txs, _ in after] == [repr(txs) for txs, _ in alone]


def test_the_entry_points_fix_the_hash_seed():
    code = (f"import sys; sys.path.insert(0, {SRC!r}); from kindhml import fix_hash_seed; "
            "fix_hash_seed(); print(hash('kindhml'))")
    outs = {subprocess.run([sys.executable, "-c", code], capture_output=True, text=True,
                           check=True, env=dict(os.environ, PYTHONHASHSEED=seed)).stdout
            for seed in ("1", "2", "random")}
    assert len(outs) == 1 and outs.pop().strip()
