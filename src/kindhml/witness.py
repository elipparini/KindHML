"""Candidate witnesses of existentials over a method and its arguments (milestone D; DESIGN.md,
Sect. 7.8).

A property `... exists f : method . exists args : calldataargs . << s : C.f(args) >> psi ...`
holds if one of its instances holds, where f is a procedure p of C and args are terms: a proof of
an instance is a proof of the property (the instance implies it, by the introduction of the
existentials). The instance has no existential over methods or arguments, so it may have a cutoff
where the property has none (lending-simple-real Liquidation_defence_exists: in its negation,
the liquidator b is existential under the universal over args; its instance with repay(debt[a])
is the property Liquidation_defence, proved for every number of users).

The arguments are terms of the type of each parameter, built from the state and the variables in
scope: for a number, the entries of the maps of that type at the address variables in scope, and
the scalar fields of that type (uint ones for an int parameter too, never int ones for a uint
parameter: `_fits`); for an address, the address variables in scope, the contracts and
null; for a boolean, true and false. Only the first such existential in positive position is
instantiated.

Before them come the guard terms of each procedure (`guard_terms`): the terms t of the
conjuncts `t >= x`, `x <= t` and `x == t` of the requires that start its body, for a numeric
parameter x, with msg.sender replaced by the sender of the modality. A guard often names the
amount that a strategy needs: on lending-real, the defence against liquidation is
repay(sdebt[a] * idx), the whole debt, which is a product, not a field (2026-10-25).
"""

from __future__ import annotations

import itertools
from typing import Dict, List, Optional, Tuple

from . import pretty
from . import syntax as S

MAX_INSTANCES = 64


def _fits(u, t) -> bool:
    """Whether a field of type u gives values of the parameter type t in every reachable state:
    the same type, or a uint for an int (an assignment of a negative number to a uint field
    reverts, `desugar.py`). An int term for a uint parameter does not fit: a negative value
    makes the call revert by its uint guard, while the arguments of the property range over
    the naturals, so the instance would not imply the property (a false property was proved
    that way, tests/contracts/witness/uint.sol)."""
    return u == t or (t == S.INT and u == S.UINT)


def _type(program: S.Program, e: S.Expr, scope: List[str]) -> Optional[S.Type]:
    """The type of a term built from the fields of the state, the entries of maps at the
    address variables in `scope` or at contracts, +, - and *; None for any other term. A
    difference is int even of uints (it may be negative), as is a sum or a product of an int
    and a uint."""
    if isinstance(e, S.Field):
        t = program.contract(e.contract).field_decl(e.name).type
        return None if isinstance(t, S.MapType) else t
    if isinstance(e, S.Index) and isinstance(e.map, S.Field):
        t = program.contract(e.map.contract).field_decl(e.map.name).type
        key_ok = ((isinstance(e.key, S.QVar) and e.key.name in scope)
                  or isinstance(e.key, S.ContractAddr))
        return t.value if isinstance(t, S.MapType) and key_ok else None
    if isinstance(e, S.BinOp) and e.op in ("+", "-", "*"):
        a, b = _type(program, e.left, scope), _type(program, e.right, scope)
        if a is None or b is None:
            return None
        if a == b == S.REAL:
            return S.REAL
        if S.REAL in (a, b):
            return None
        return S.UINT if a == b == S.UINT and e.op != "-" else S.INT
    return None


def _with_sender(e, sender: S.Expr):
    """e with msg.sender replaced by `sender`."""
    if isinstance(e, S.Sender):
        return sender
    if not hasattr(e, "__dataclass_fields__") or isinstance(e, (S.Type, S.MapType)):
        return e
    changes = {n: _with_sender(getattr(e, n), sender) for n in e.__dataclass_fields__
               if isinstance(getattr(e, n), S.Expr)}
    changes = {n: v for n, v in changes.items() if v is not getattr(e, n)}
    if not changes:
        return e
    return type(e)(**{**{n: getattr(e, n) for n in e.__dataclass_fields__}, **changes})


def _conjuncts(e: S.Expr) -> List[S.Expr]:
    if isinstance(e, S.BinOp) and e.op == "&&":
        return _conjuncts(e.left) + _conjuncts(e.right)
    return [e]


def guard_terms(program: S.Program, p: S.Procedure, x: S.VarDecl, sender: Optional[S.Expr],
                scope: List[str]) -> List[S.Expr]:
    """The guard terms of the parameter x of p (module docstring) that fit its type
    (`_fits`), msg.sender replaced by `sender` (None: terms with msg.sender are skipped)."""
    stmts = p.body.stmts if isinstance(p.body, S.Seq) else (p.body,)
    out: List[S.Expr] = []
    for stmt in stmts:
        if not isinstance(stmt, S.Require):
            break
        for g in _conjuncts(stmt.cond):
            is_x = lambda e: isinstance(e, S.Param) and e.name == x.name
            t = None
            if isinstance(g, S.BinOp) and g.op in (">=", "==") and is_x(g.right):
                t = g.left
            elif isinstance(g, S.BinOp) and g.op in ("<=", "==") and is_x(g.left):
                t = g.right
            if t is None or (sender is None and _has_sender(t)):
                continue
            t = _with_sender(t, sender) if sender is not None else t
            u = _type(program, t, scope)
            if u is not None and _fits(u, x.type) \
                    and pretty.expr(t) not in [pretty.expr(o) for o in out]:
                out.append(t)
    return out


def _has_sender(e) -> bool:
    if isinstance(e, S.Sender):
        return True
    return any(_has_sender(getattr(e, n)) for n in getattr(e, "__dataclass_fields__", ())
               if isinstance(getattr(e, n), S.Expr))


def _sender(e, fvar: str) -> Optional[S.Expr]:
    """The sender of the first modality that calls the method variable `fvar`."""
    if isinstance(e, S.Modal) and isinstance(e.proc, S.QVar) and e.proc.name == fvar:
        return e.sender
    for n in getattr(e, "__dataclass_fields__", ()):
        v = getattr(e, n)
        for x in (v if isinstance(v, tuple) else (v,)):
            if isinstance(x, S.Expr):
                found = _sender(x, fvar)
                if found is not None:
                    return found
    return None


def candidates(program: S.Program, t, scope: List[str]) -> List[S.Expr]:
    """The terms of type t for an argument (module docstring)."""
    if t == S.BOOL:
        return [S.BoolLit(True), S.BoolLit(False)]
    if t == S.ADDRESS:
        return ([S.QVar(a, S.ADDRESS) for a in scope] + [S.ContractAddr(c.name)
                for c in program.contracts] + [S.NullLit()])
    if t not in (S.INT, S.UINT, S.REAL):
        return []
    out: List[S.Expr] = []
    for c in program.contracts:
        for f in c.fields:
            if isinstance(f.type, S.MapType) and _fits(f.type.value, t):
                out += [S.Index(S.Field(c.name, f.name), S.QVar(a, S.ADDRESS)) for a in scope]
        for f in c.fields:
            if not isinstance(f.type, S.MapType) and _fits(f.type, t):
                out.append(S.Field(c.name, f.name))
    return out


def _subst(e, mapping: Dict[str, S.Expr], modal: Optional[Tuple[str, str, S.Procedure]],
           args_var: Optional[str], terms: Tuple[S.Expr, ...]):
    """e with the quantified variables of `mapping` replaced, and the modalities that call the
    method variable with the arguments variable `args_var` turned into calls of the procedure."""
    if isinstance(e, S.QVar) and e.name in mapping:
        return mapping[e.name]
    if isinstance(e, S.Modal) and modal is not None and isinstance(e.proc, S.QVar) \
            and e.proc.name in mapping and len(e.args) == 1 \
            and isinstance(e.args[0], S.QVar) and e.args[0].name == args_var:
        rec = lambda x: _subst(x, mapping, modal, args_var, terms)
        return S.Modal(rec(e.sender), e.contract, mapping[e.proc.name], terms, rec(e.value),
                       rec(e.blocks), rec(e.body), e.pos)
    if not hasattr(e, "__dataclass_fields__") or isinstance(e, (S.Type, S.MapType)):
        return e
    changes = {}
    for name in e.__dataclass_fields__:
        v = getattr(e, name)
        if isinstance(v, tuple):
            new = tuple(_subst(x, mapping, modal, args_var, terms) if isinstance(x, S.Expr) else x
                        for x in v)
        elif isinstance(v, S.Expr):
            new = _subst(v, mapping, modal, args_var, terms)
        else:
            continue
        if new is not v:
            changes[name] = new
    if not changes:
        return e
    return type(e)(**{**{n: getattr(e, n) for n in e.__dataclass_fields__}, **changes})


def _site(e, scope: List[str], positive: bool = True):
    """The first existential over a method in positive position, with the address variables in
    scope there: (the quantifier, its arguments quantifier or None, scope), or None."""
    if isinstance(e, S.Quant):
        if positive and e.kind == "exists" and e.type == S.METHOD:
            inner = e.body
            if isinstance(inner, S.Quant) and inner.kind == "exists" and inner.type == S.ARGS:
                return e, inner, scope
            return e, None, scope
        if e.kind == "forall" or not positive:
            more = scope + [e.var] if e.type == S.ADDRESS else scope
            return _site(e.body, more, positive)
        return None
    if isinstance(e, S.BinOp) and e.op in ("&&", "||"):
        return _site(e.left, scope, positive) or _site(e.right, scope, positive)
    if isinstance(e, S.BinOp) and e.op == "->":
        return _site(e.right, scope, positive)
    if isinstance(e, S.Modal):
        return _site(e.body, scope, positive)
    return None


def _plain_uses(e, fvar: str, avar: Optional[str], under: bool) -> bool:
    """Whether the method variable `fvar` and the arguments variable `avar` occur in e only as
    the method and the arguments of modalities `<< _ : C.fvar(avar) >>` that are not under
    another modality (`under`): the terms that replace the arguments are then evaluated at the
    state of the existential, where they denote fixed values, so that an instance implies the
    property. Under a modality, they would denote values of a later state."""
    if isinstance(e, S.QVar):
        return e.name not in (fvar, avar)
    if isinstance(e, S.Modal) and isinstance(e.proc, S.QVar) and e.proc.name == fvar:
        if under or avar is None or len(e.args) != 1 or not isinstance(e.args[0], S.QVar) \
                or e.args[0].name != avar:
            return False
        return (all(_plain_uses(x, fvar, avar, under) for x in (e.sender, e.value, e.blocks)
                    if isinstance(x, S.Expr)) and _plain_uses(e.body, fvar, avar, True))
    for name in getattr(e, "__dataclass_fields__", ()):
        v = getattr(e, name)
        # the body of a modality is at a later state, its other parts at this one
        later = under or (isinstance(e, S.Modal) and name == "body")
        for x in (v if isinstance(v, tuple) else (v,)):
            if isinstance(x, S.Expr) and not _plain_uses(x, fvar, avar, later):
                return False
    return True


def _binds(e) -> set:
    """The names of the variables quantified in e."""
    out = {e.var} if isinstance(e, S.Quant) else set()
    for name in getattr(e, "__dataclass_fields__", ()):
        v = getattr(e, name)
        for x in (v if isinstance(v, tuple) else (v,)):
            if isinstance(x, S.Expr):
                out |= _binds(x)
    return out


def instances(program: S.Program, prop: S.Property,
              limit: int = MAX_INSTANCES) -> List[Tuple[str, S.Property]]:
    """The instances of the first existential over a method of `prop` (module docstring), each
    with a description, at most `limit` (in the order of the procedures and of the candidate
    terms); [] if there is none."""
    site = _site(prop.formula, [])
    if site is None:
        return []
    fq, aq, scope = site
    body = aq.body if aq is not None else fq.body
    if not _plain_uses(body, fq.var, aq.var if aq is not None else None, False) \
            or _binds(body) & set(scope + [fq.var] + ([aq.var] if aq is not None else [])):
        return []                       # a variable of the terms would be captured
    out: List[Tuple[str, S.Property]] = []
    seen: set = set()
    # the sender of the call, if a term at the state of the existential: it replaces msg.sender
    # in the guard terms
    sender = _sender(body, fq.var)
    if not (isinstance(sender, S.ContractAddr)
            or (isinstance(sender, S.QVar) and sender.name in scope)):
        sender = None

    def calls(guards: bool):
        """The calls with their choices of terms: with `guards`, those of the procedures with
        guard terms (the other parameters with the generic terms); the procedures with fewer
        combinations first, so that the limit cuts the procedures with many parameters."""
        found = []
        for c in program.contracts:
            for p in c.procs:
                if p.name == S.CONSTRUCTOR:
                    continue
                choices = [candidates(program, v.type, scope) for v in p.params]
                if guards:
                    own = [guard_terms(program, p, v, sender, scope) for v in p.params]
                    if not any(own):
                        continue
                    choices = [g or ch for g, ch in zip(own, choices)]
                if all(choices):
                    size = 1
                    for ch in choices:
                        size *= len(ch)
                    found.append((size, c, p, choices))
        return sorted(found, key=lambda x: x[0])

    for guards in (True, False):
        for _, c, p, choices in calls(guards):
            for terms in itertools.product(*choices):
                text = f"{p.name}({', '.join(pretty.expr(t) for t in terms)})"
                if text in seen:
                    continue
                seen.add(text)
                mapping = {fq.var: S.ProcConst(c.name, p.name)}
                new_body = _subst(body, mapping, (c.name, p.name, p),
                                  aq.var if aq is not None else None, tuple(terms))
                formula = _replace(prop.formula, fq, new_body)
                out.append((text, S.Property(f"{prop.name}__w{len(out)}", formula, None,
                                             prop.pos)))
                if len(out) >= limit:
                    return out
    return out


def _replace(e, old, new):
    """e with the node `old` (by identity) replaced by `new`."""
    if e is old:
        return new
    if not hasattr(e, "__dataclass_fields__") or isinstance(e, (S.Type, S.MapType)):
        return e
    changes = {}
    for name in e.__dataclass_fields__:
        v = getattr(e, name)
        if isinstance(v, tuple):
            nv = tuple(_replace(x, old, new) for x in v)
            if any(a is not b for a, b in zip(nv, v)):
                changes[name] = nv
        elif hasattr(v, "__dataclass_fields__"):
            nv = _replace(v, old, new)
            if nv is not v:
                changes[name] = nv
    if not changes:
        return e
    return type(e)(**{**{n: getattr(e, n) for n in e.__dataclass_fields__}, **changes})
