"""Concrete states and transactions of the reference interpreter as Lustre literals."""

from __future__ import annotations

from fractions import Fraction
from typing import Dict

from . import lustre as L
from . import syntax as S
from .encode_trans import (BALANCE, BLOCK, BLOCKS, REVERT, Encoder, addr_const, constructed_var,
                           field_var, ghost_var, key_field, map_type, param_var, proc_const)
from .model import System
from .reference import State, Tx, initial_state


def value_literal(v, t: S.AnyType, system: System) -> L.LExpr:
    if isinstance(t, S.MapType):
        return L.record(map_type(t.value), [(key_field(a), value_literal(v[a], t.value, system))
                                            for a in system.addresses])
    if t == S.BOOL:
        return L.Bool(v)
    if t == S.ADDRESS:
        return L.Var(addr_const(v))
    return L.Real(Fraction(v)) if t == S.REAL else L.Int(v)


def state_literal(st: State, system: System, enc: Encoder) -> L.LExpr:
    values = {BALANCE: value_literal(st.balance, S.MapType(enc.amount), system),
              REVERT: L.Bool(st.revert), BLOCK: L.Int(st.block_num)}
    for c in system.contracts:
        values[constructed_var(c.name)] = L.Bool(st.constructed[c.name])
        for f in c.fields:
            values[field_var(c.name, f.name)] = value_literal(st.fields[(c.name, f.name)],
                                                              f.type, system)
    for key, t in enc.ghosts.items():           # parameterized mode: the exact sums
        m = st.balance if key == BALANCE else st.fields[key]
        values[ghost_var(key)] = value_literal(sum(m.values()), t, system)
    return L.record("St", [(n, values[n]) for n, _ in enc.state_fields()])


def tx_literal(tx: Tx, system: System, enc: Encoder, default) -> L.LExpr:
    """The transaction as a Tx record; `default(type)` gives the parameters of the other
    procedures (Trans does not depend on them)."""
    values = {"sender": L.Var(addr_const(tx.sender)), "cx": L.Var(addr_const(tx.contract)),
              "fx": L.Var(proc_const(*tx.method)),
              "value": value_literal(tx.value, enc.amount, system),
              BLOCKS: L.Int(tx.blocks)}
    for v in system.param_vars:
        arg = tx.args.get(v.name) if (v.contract, v.proc) == tx.method else None
        values[param_var(v.contract, v.proc, v.name)] = value_literal(
            arg if arg is not None else default(v.type), v.type, system)
    return L.record("Tx", [(n, values[n]) for n, _ in enc.tx_fields()])


def python_value(v):
    """A value of a Kind 2 counterexample (JSON) as a value of the reference interpreter."""
    if isinstance(v, dict) and set(v) == {"num", "den"}:
        return Fraction(v["num"], v["den"])
    if isinstance(v, str) and v.startswith("A_"):
        return v[2:]                        # an address constant
    return v


def state_from_values(values: Dict[str, object], system: System, enc: Encoder) -> State:
    """The reference state with the values of the record `s` of a Kind 2 counterexample,
    given by path (`s.f` or `s.f.k_a`), e.g. a free state of a check of `invariants.py`."""
    fields = {}
    for c in system.contracts:
        for f in c.fields:
            fields[field_var(c.name, f.name)] = (c.name, f.name, f.type)
    st = initial_state(system, {})
    st.constructed = {c.name: False for c in system.contracts}
    for path, v in values.items():
        parts = path.split(".")
        if parts[0] != "s" or len(parts) < 2:
            continue
        name, key = parts[1], (parts[2][2:] if len(parts) > 2 else None)
        v = python_value(v)
        if name == BALANCE and key is not None:
            st.balance[key] = v
        elif name == REVERT:
            st.revert = v
        elif name == BLOCK:
            st.block_num = v
        elif name.startswith("constructed_"):
            st.constructed[name[len("constructed_"):]] = v
        elif name in fields:
            c, f, t = fields[name]
            if key is None:
                st.fields[(c, f)] = v
            else:
                st.fields[(c, f)][key] = v
    return st


def describe_tx(tx: Tx) -> str:
    args = ", ".join(f"{k}={_show(v)}" for k, v in tx.args.items())
    value = f" $ {_show(tx.value)}" if tx.value else ""
    blocks = f" @ {tx.blocks}" if tx.blocks else ""
    return f"{tx.sender} : {tx.method[0]}.{tx.method[1]}({args}){value}{blocks}"


def _show(v) -> str:
    if isinstance(v, Fraction):
        return str(v.numerator) if v.denominator == 1 else f"{v.numerator}/{v.denominator}"
    return str(v)
