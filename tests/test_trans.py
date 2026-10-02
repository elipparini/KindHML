"""Differential test of the transition encoding against the reference interpreter.

For random concrete flagged states S and transactions T, `trans(S, T) = S'` must hold,
where S' is computed by `reference.Interpreter`. This checks Lemma `lem:transition` on
samples: on many samples by evaluating the generated Lustre in Python, and on a few samples
with Kind 2.
"""

import glob
import os
import random

import pytest

from kindhml import kind2
from kindhml import lustre as L
from kindhml import syntax as S
from kindhml.builder import parse
from kindhml.encode_trans import (BALANCE, BLOCK, BLOCKS, REVERT, Encoder, addr_const, constructed_var,
                                  field_var, key_field, map_type, param_var, proc_const)
from kindhml.lustre_eval import Evaluator
from kindhml.model import NULL, System
from kindhml.reference import Interpreter, State, Tx, initial_state
from kindhml.typecheck import check

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FILES = sorted(glob.glob(os.path.join(ROOT, "contracts", "*", "*.sol"))
               + glob.glob(os.path.join(ROOT, "tests", "contracts", "*.sol")))
SAMPLES = int(os.environ.get("KINDHML_SAMPLES", "300"))
KIND2_SAMPLES = 3

try:
    kind2.find_kind2()
    HAVE_KIND2 = True
except FileNotFoundError:
    HAVE_KIND2 = False


def value_literal(v, t: S.AnyType, system: System) -> L.LExpr:
    if isinstance(t, S.MapType):
        return L.record(map_type(t.value), [(key_field(a), value_literal(v[a], t.value, system))
                                            for a in system.addresses])
    if t == S.BOOL:
        return L.Bool(v)
    if t == S.ADDRESS:
        return L.Var(addr_const(v))
    return L.Int(v)


def state_literal(st: State, system: System, enc: Encoder) -> L.LExpr:
    values = {BALANCE: value_literal(st.balance, S.MapType(S.INT), system),
              REVERT: L.Bool(st.revert), BLOCK: L.Int(st.block_num)}
    for c in system.contracts:
        values[constructed_var(c.name)] = L.Bool(st.constructed[c.name])
        for f in c.fields:
            values[field_var(c.name, f.name)] = value_literal(st.fields[(c.name, f.name)],
                                                              f.type, system)
    return L.record("St", [(n, values[n]) for n, _ in enc.state_fields()])


def tx_literal(tx: Tx, system: System, enc: Encoder) -> L.LExpr:
    values = {"sender": L.Var(addr_const(tx.sender)), "cx": L.Var(addr_const(tx.contract)),
              "fx": L.Var(proc_const(*tx.method)), "value": L.Int(tx.value),
              BLOCKS: L.Int(tx.blocks)}
    for v in system.param_vars:
        arg = tx.args.get(v.name) if (v.contract, v.proc) == tx.method else None
        values[param_var(v.contract, v.proc, v.name)] = value_literal(
            arg if arg is not None else random_value(v.type, system, random.Random(0)),
            v.type, system)
    return L.record("Tx", [(n, values[n]) for n, _ in enc.tx_fields()])


def random_value(t: S.AnyType, system: System, rnd: random.Random):
    if isinstance(t, S.MapType):
        return {a: random_value(t.value, system, rnd) for a in system.addresses}
    if t == S.BOOL:
        return rnd.random() < 0.5
    if t == S.ADDRESS:
        return rnd.choice(system.addresses)
    return rnd.randint(-2, 4)


def random_state(system: System, rnd: random.Random) -> State:
    st = initial_state(system, {a: rnd.randint(0, 5) for a in system.addresses})
    for c in system.contracts:
        st.constructed[c.name] = rnd.random() < 0.9
        for f in c.fields:
            st.fields[(c.name, f.name)] = random_value(f.type, system, rnd)
    st.block_num = rnd.randint(0, 3)
    st.revert = rnd.random() < 0.3
    return st


def random_tx(system: System, rnd: random.Random) -> Tx:
    """A random transaction, biased towards valid ones."""
    c, p = rnd.choice(system.methods)
    contract = c.name if rnd.random() < 0.95 else rnd.choice(system.addresses)
    args = {x.name: random_value(x.type, system, rnd) for x in p.params}
    sender = rnd.choice(system.users) if rnd.random() < 0.85 else rnd.choice(system.addresses)
    value = rnd.randint(-1, 3) if p.payable or rnd.random() < 0.1 else 0
    return Tx(sender, contract, (c.name, p.name), args, value, rnd.randint(-1, 3))


def random_reachable_state(system: System, rnd: random.Random, interp: Interpreter) -> State:
    """The state reached by a random sequence of transactions from an initial state."""
    st = initial_state(system, {a: rnd.randint(0, 5) for a in system.addresses},
                       rnd.randint(0, 3))
    for c in system.contracts:
        ctor = c.procs[0]
        st = interp.step(st, Tx(rnd.choice(system.users), c.name, (c.name, ctor.name),
                                {x.name: random_value(x.type, system, rnd) for x in ctor.params},
                                rnd.randint(0, 2) if ctor.payable else 0, 0))
    for _ in range(rnd.randint(0, 4)):
        st = interp.step(st, random_tx(system, rnd))
    return st


def equal_fields(a: L.LExpr, b: L.LExpr, fields) -> L.LExpr:
    return L.conj([L.op("=", L.Proj(a, n), L.Proj(b, n)) for n, _ in fields])


def samples(system: System, interp: Interpreter, rnd: random.Random, n: int):
    for i in range(n):
        st = random_state(system, rnd) if i % 2 else random_reachable_state(system, rnd, interp)
        tx = random_tx(system, rnd)
        yield i, st, tx, interp.step(st, tx)


def setup(path):
    program, _ = check(parse(open(path).read()))
    system = System.make(program, 2)
    enc = Encoder(system)
    return system, enc, Interpreter(system), random.Random(path)


def test_transactions_increase_the_block_number():
    """A transaction increases the block number by its `blocks` before the body runs; a
    negative increase reverts, and a reverted transaction leaves the block number unchanged."""
    program, _ = check(parse("contract C { int t; function f() { t = block.number } }"))
    system = System.make(program, 1)
    enc, interp = Encoder(system), Interpreter(system)
    ev = Evaluator(enc.program()[0])
    st = initial_state(system, {}, 5)
    st.constructed["C"] = True
    for blocks, reverts, block in [(2, False, 7), (0, False, 5), (-1, True, 5)]:
        tx = Tx("u1", "C", ("C", "f"), {}, 0, blocks)
        expected = interp.step(st, tx)
        assert (expected.revert, expected.block_num) == (reverts, block)
        assert reverts or expected.fields[("C", "t")] == block
        actual = ev.eval(L.call("trans", state_literal(st, system, enc),
                                tx_literal(tx, system, enc)), {})
        assert actual == ev.eval(state_literal(expected, system, enc), {}), blocks


def test_senders_of_transactions_and_of_calls():
    """A transaction is sent by a user; in a contract call, the sender is the calling contract
    (Shop.relay calls Router.forward, which calls Token.give, which reads bal[msg.sender])."""
    system, enc, interp, _ = setup(os.path.join(ROOT, "tests", "contracts", "calls.sol"))
    ev = Evaluator(enc.program()[0])
    st = initial_state(system, {a: 1 for a in system.addresses})
    st.constructed = {c: True for c in st.constructed}
    for router_tokens, sender, reverts in [(1, "u1", False), (0, "u1", True),
                                           (1, "Router", True), (1, NULL, True)]:
        s = st.copy()
        s.fields[("Token", "bal")]["Router"] = router_tokens
        tx = Tx(sender, "Shop", ("Shop", "relay"), {"n": 1})
        expected = interp.step(s, tx)
        assert expected.revert == reverts, (router_tokens, sender)
        actual = ev.eval(L.call("trans", state_literal(s, system, enc),
                                tx_literal(tx, system, enc)), {})
        assert actual == ev.eval(state_literal(expected, system, enc), {}), (router_tokens, sender)


@pytest.mark.parametrize("path", FILES, ids=os.path.basename)
def test_trans_matches_reference(path):
    """The generated Lustre `trans`, evaluated in Python, agrees with the interpreter."""
    system, enc, interp, rnd = setup(path)
    prog, _ = enc.program()
    ev = Evaluator(prog)
    succeeded = 0
    for i, st, tx, expected in samples(system, interp, rnd, SAMPLES):
        actual = ev.eval(L.call("trans", state_literal(st, system, enc),
                                tx_literal(tx, system, enc)), {})
        assert actual == ev.eval(state_literal(expected, system, enc), {}), (i, st, tx, expected)
        succeeded += not expected.revert
    assert succeeded > 0


@pytest.mark.kind2
@pytest.mark.skipif(not HAVE_KIND2, reason="Kind 2 not available")
@pytest.mark.parametrize("path", FILES, ids=os.path.basename)
def test_trans_kind2(path):
    """Kind 2 agrees on a few samples (it reads the Lustre program as the evaluator does)."""
    system, enc, interp, rnd = setup(path)
    prog, _ = enc.program()
    # Closed properties are checked in a stateless node, so that Kind 2 does not
    # analyse the transition system.
    main = L.Function("checks", [("dummy", "bool")], [], node=True)
    prog.decls.append(main)
    cases = {}
    for i, st, tx, expected in samples(system, interp, rnd, KIND2_SAMPLES):
        # bind trans(S, T) to a local, so that Kind 2 inlines trans once per case
        actual = L.Var(f"r{i}")
        main.locals.append((actual.name, "St"))
        main.equations.append((actual.name, L.call("trans", state_literal(st, system, enc),
                                                    tx_literal(tx, system, enc))))
        exp = state_literal(expected, system, enc)
        # compare field by field; map fields compare as records
        prop = L.conj([L.op("=", L.Proj(actual, n), L.Proj(exp, n))
                       if not t.startswith("Map_") else
                       equal_fields(L.Proj(actual, n), L.Proj(exp, n),
                                    [(key_field(a), "") for a in system.addresses])
                       for n, t in enc.state_fields()])
        name = f"case{i}"
        main.properties.append((name, prop))
        cases[name] = (st, tx, expected)
    out = kind2.run(prog.render(), timeout=60,
                    extra_args=["--lus_main", "checks", "--enable", "BMC", "--enable", "IND"])
    assert not out.errors, out.errors
    statuses = {p.name: p.status for p in out.properties}
    wrong = {n: (statuses[n], cases[n]) for n, s in statuses.items() if s != "valid"}
    assert len(statuses) == len(cases) and not wrong, wrong
