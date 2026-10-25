"""Saving the SMT-LIB instances of a run (options --smt_trace and --smt_trace_logics).

KindHML asks SMT queries in two ways: through Kind 2 (`kind2.run`), which writes, with its
flag --smt_trace, one incremental script per solver process (BMC, k-induction, IC3, invariant
generation, ...); and through z3 directly (`direct.Query`), one script per query. With tracing
on, the scripts are saved in a directory, in two forms:
* incremental/: a Kind 2 script as the solver received it, cleaned: the responses (comments),
  the options, and the commands that do not change the assertions (`get-value`, `apply`,
  `echo`, ...) are removed; a truncated last command (Kind 2 killed at its timeout) is
  dropped; the answer of each check-sat, when the trace has it, is recorded with
  `(set-info :status ...)`; the logic is the one computed below;
* standalone/: one script per check-sat, with the declarations, definitions and assertions
  live at that point (after the pushes and pops), the assumptions of `check-sat-assuming`
  asserted, and one `check-sat`.

Pruning of standalone scripts. Kind 2 guards assertions with activation literals,
`(assert (=> a φ))`, retires them with `(assert (not a))`, and declares the variables of
every unrolling. A Boolean constant a whose only occurrences in the live assertions and the
assumptions (through definitions too) are as the guard of such implications, or in
`(assert (not a))`, is set to false, which drops these assertions (repeated until nothing
changes). Then the declarations and definitions that the rest does not use are dropped.
Both steps preserve satisfiability: a model of what is left, extended with a = false, is a
model of the whole. So a standalone script has the answer of its check-sat in the trace.

Logic. The logic of a script is computed from its commands, not taken from its `set-logic`
(Kind 2 declares NIA for linear scripts): quantifiers (forall, exists), the sorts Int and
Real, arrays, bit-vectors, uninterpreted functions (declared with arguments), and
nonlinearity: a product with two non-constant factors, or a division, `div` or `mod` by a
non-constant term. A term is constant if it has no free symbol: literals, and builtin
operators applied to constant terms. A symbol bound by `let`, or defined by a nullary
`define-fun`, to a constant term is constant; quantified variables and parameters are not;
an application of a defined function is not (conservatively). `abs` is linear. The name
follows SMT-LIB: [QF_][A][UF][BV][N|L][IA|RA|IRA] (e.g. QF_NIA, NIA, QF_LIA; QF_UF without
arithmetic). A standalone script has the features of its own commands, so its logic may be
smaller than the one of its trace. With --smt_trace_logics, only the files whose logic is in
the list are written, and a trace is split only if one of its sub-logics is in the list.

Each file is named after its origin (`Tracer.stem`): the task (family, version, property, or
"invariants" for the invariant phase of a contract), the number of the solver call in the
task and the function of `verify.py` that made it, the Kind 2 engine (the name of its trace),
the solver, the index of the check-sat for a standalone file, and the logic. A file with the
same content as one already written (same body, whatever the origin) is not written again;
MANIFEST.csv has one row per file found, with `duplicate_of`. Every process appends its rows,
so the shards of a run may share the directory. The Lustre input of each Kind 2 call with a
row in the manifest is saved in sources/.
"""

from __future__ import annotations

import csv
import hashlib
import io
import itertools
import os
import re
import sys
from dataclasses import dataclass
from typing import Dict, FrozenSet, Iterable, List, Optional, Sequence, Tuple

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# atoms: comments, parentheses, quoted symbols, strings, other tokens
_TOKEN = re.compile(r';[^\n]*|\(|\)|\|[^|]*\||"(?:[^"]|"")*"|[^\s()|";]+')
_ANSWER = re.compile(r';+\s*(sat|unsat|unknown)\b', re.IGNORECASE)
_BV_BUILTIN = re.compile(r'bv([a-z]+|\d+)$')    # bit-vector operators, and bvN in (_ bvN m)
_BV_LITERAL = re.compile(r'bv\d+$')

# builtin operators (applications of them to constants are constant) and other reserved words
_OPS = frozenset("""
    true false not and or xor => = distinct ite + - * / div mod abs < <= > >= to_real to_int
    is_int select store let forall exists ! _ as par Bool Int Real Array BitVec concat extract
    repeat zero_extend sign_extend rotate_left rotate_right""".split())
_TOKEN_FEATURES = {"Int": "I", "Real": "R", "Array": "A", "BitVec": "BV", "forall": "Q",
                   "exists": "Q", "to_real": "IR", "to_int": "IR", "is_int": "IR"}

DECLARATIONS = frozenset({"declare-fun", "declare-const", "define-fun", "define-fun-rec",
                          "define-funs-rec", "declare-sort", "define-sort",
                          "declare-datatype", "declare-datatypes"})
CHECKS = frozenset({"check-sat", "check-sat-assuming", "check-sat-using"})
_MISSING = object()


# ------------------------------------------------------------------ parsing

@dataclass
class Command:
    """A top-level command of a script, as written (`text`), with what the splitting and the
    logic need."""
    text: str
    head: str
    name: str = ""                      # the symbol declared or defined
    symbols: FrozenSet[str] = frozenset()   # the symbols used (not `name`, nor `guard`)
    features: FrozenSet[str] = frozenset()  # Q, A, UF, BV, N, I, R
    bool_constant: bool = False         # a declaration of a nullary Boolean symbol
    guard: str = ""                     # (assert (=> guard φ)), guard not in φ
    negated: str = ""                   # (assert (not negated))
    assumptions: Tuple[Tuple[str, bool], ...] = ()     # check-sat-assuming: (symbol, polarity)
    status: str = ""                    # check: the answer recorded after it


class _Frame:
    """An open parenthesis while parsing a command."""
    __slots__ = ("head", "kind", "items", "argc", "nonconst", "late", "last_const", "args",
                 "bound", "saved")

    def __init__(self, kind: str):
        self.head: Optional[str] = None     # the first item, if a token
        self.kind = kind                    # app, bindings, binding, binders, binder
        self.items = 0
        self.argc = 0                       # the items after the head
        self.nonconst = 0                   # arguments that are not constant
        self.late = False                   # an argument after the first is not constant
        self.last_const = True
        self.args: list = []                # the first arguments: (token, const, empty, shape)
        self.bound: list = []               # bindings, binders: (name, const) to activate
        self.saved: list = []               # names bound by this frame: (name, previous value)

    def add(self, token: Optional[str], const: bool, empty: bool = False, shape=None):
        if token is not None and self.items == 0:
            self.head = token
        else:
            if not const:
                self.nonconst += 1
                self.late = self.late or self.argc >= 1
            if self.argc < 4:
                self.args.append((token, const, empty, shape))
            self.last_const = const
            self.argc += 1
        self.items += 1


def _kind(parent: Optional[_Frame], top: bool) -> str:
    if parent is None:
        return "app"
    if parent.kind == "bindings":
        return "binding"
    if parent.kind == "binders":
        return "binder"
    if parent.items == 1 and (parent.head == "let"):
        return "bindings"
    if parent.items == 1 and parent.head in ("forall", "exists"):
        return "binders"
    if top and parent.head in ("define-fun", "define-fun-rec") and parent.argc == 1:
        return "binders"
    return "app"


def _is_symbol(token: str) -> bool:
    return not (token[0].isdigit() or token[0] in ':#"' or token in _OPS
                or _BV_BUILTIN.match(token))


def _token_const(token: str, consts: dict) -> bool:
    if token[0].isdigit() or token[0] in ':#"' or token in ("true", "false") \
            or _BV_LITERAL.match(token):
        return True
    return consts.get(token, False) is True


def parse(script: str) -> Tuple[List[Command], bool]:
    """The commands of a script, and whether it ends inside a command (truncated)."""
    commands: List[Command] = []
    stack: List[_Frame] = []
    consts: dict = {}                   # constant symbols (nullary define-fun, let) -> True
    counts: Dict[str, int] = {}
    feats: set = set()
    start = 0
    pending: Optional[Command] = None   # a check waiting for its answer
    for m in _TOKEN.finditer(script):
        tok = m.group()
        c = tok[0]
        if c == ";":
            if not stack and pending is not None:
                a = _ANSWER.match(tok)
                if a:
                    pending.status = a.group(1).lower()
                    pending = None
            continue
        if c == "(":
            if not stack:
                start, counts, feats, pending = m.start(), {}, set(), None
            parent = stack[-1] if stack else None
            stack.append(_Frame(_kind(parent, len(stack) == 1)))
            continue
        if c == ")":
            if not stack:
                continue
            f = stack.pop()
            for name, prev in reversed(f.saved):
                if prev is _MISSING:
                    consts.pop(name, None)
                else:
                    consts[name] = prev
            if not stack:
                cmd = _command(script[start:m.end()], f, counts, feats, consts)
                commands.append(cmd)
                pending = cmd if cmd.head in CHECKS else None
                continue
            parent = stack[-1]
            if f.kind in ("bindings", "binders"):
                for name, value in f.bound:
                    parent.saved.append((name, consts.get(name, _MISSING)))
                    consts[name] = value
            elif f.kind == "binding":
                parent.bound.append((f.head, bool(f.args) and f.args[0][1]))
            elif f.kind == "binder":
                parent.bound.append((f.head, False))
            const = _close(f, feats)
            shape = None
            if f.head in ("=>", "not") and f.argc == (2 if f.head == "=>" else 1) \
                    and f.args[0][0] is not None:
                shape = (f.head, f.args[0][0])
            parent.add(None, const, f.head is None and f.argc == 0, shape)
            continue
        if not stack:
            continue                    # a stray atom
        feature = _TOKEN_FEATURES.get(tok)
        if feature:
            feats.update(("I", "R") if feature == "IR" else (feature,))
        elif c.isdigit() and "." in tok:
            feats.add("R")
        elif c == "#":
            feats.add("BV")
        if _is_symbol(tok):
            counts[tok] = counts.get(tok, 0) + 1
        stack[-1].add(tok, _token_const(tok, consts))
    return commands, bool(stack)


def _close(f: _Frame, feats: set) -> bool:
    """Whether the term of a closed frame is constant; records its nonlinearity."""
    if f.head == "*" and f.nonconst >= 2:
        feats.add("N")
    elif f.head in ("/", "div", "mod") and f.late:
        feats.add("N")
    if f.kind != "app":
        return False
    if f.head == "let":
        return f.last_const
    if f.head == "!":
        return bool(f.args) and f.args[0][1]
    if f.head in ("forall", "exists"):
        return False
    return (f.head is None or f.head in _OPS) and f.nonconst == 0


def _command(text: str, f: _Frame, counts: Dict[str, int], feats: set,
             consts: dict) -> Command:
    head = f.head or ""
    args = f.args + [(None, False, False, None)] * (4 - len(f.args))
    cmd = Command(text, head, symbols=frozenset(counts))
    if head in DECLARATIONS:
        cmd.name = args[0][0] or ""
        cmd.symbols = frozenset(s for s in counts if s != cmd.name)
        if head == "declare-fun":
            if not args[1][2]:
                feats.add("UF")
            cmd.bool_constant = args[1][2] and args[2][0] == "Bool"
        elif head == "declare-const":
            cmd.bool_constant = args[1][0] == "Bool"
        elif head == "define-fun" and args[1][2] and args[3][1]:
            consts[cmd.name] = True
    elif head == "assert" and args[0][3] is not None:
        shape, s = args[0][3]
        if counts.get(s) == 1 and shape == "=>":
            cmd.guard = s
            cmd.symbols = frozenset(x for x in counts if x != s)
        elif counts.get(s) == 1:
            cmd.negated = s
    elif head == "check-sat-assuming":
        inner = text[text.index("(", 1) + 1:text.rindex(")", 0, len(text) - 1)]
        cmd.assumptions = tuple(
            (neg or pos, not neg)
            for neg, pos in re.findall(r'\(\s*not\s+([^\s()]+)\s*\)|([^\s()]+)', inner))
    cmd.features = frozenset(feats)
    return cmd


# ------------------------------------------------------------------ logics

FEATURES = ("Q", "A", "UF", "BV", "N", "I", "R")


def logic_name(features: Iterable[str]) -> str:
    fs = set(features)
    name = ("" if "Q" in fs else "QF_") + ("A" if "A" in fs else "") \
        + ("UF" if "UF" in fs else "") + ("BV" if "BV" in fs else "")
    arith = "IRA" if {"I", "R"} <= fs else "IA" if "I" in fs else "RA" if "R" in fs else ""
    if arith:
        return name + ("N" if "N" in fs else "L") + arith
    if name.endswith("A"):
        return name + "X"
    return name + "UF" if name in ("", "QF_") else name


def sublogics(features: Iterable[str]) -> set:
    """The names of the logics of the subsets of `features`."""
    fs = sorted(set(features))
    return {logic_name(sub) for k in range(len(fs) + 1) for sub in itertools.combinations(fs, k)}


# ------------------------------------------------------------------ splitting

def _closure(start: Iterable[str], definitions: Dict[str, Command]) -> set:
    """The symbols in `start`, and those used by the definitions of the symbols reached."""
    seen: set = set()
    todo = list(start)
    while todo:
        s = todo.pop()
        if s in seen:
            continue
        seen.add(s)
        d = definitions.get(s)
        if d is not None:
            todo.extend(d.symbols)
    return seen


def standalone(commands: Sequence[Command], live: Sequence[int], check: Command
               ) -> Tuple[List[str], FrozenSet[str]]:
    """The commands of the standalone script of `check` (the indices `live` of the commands
    in scope), pruned (module docstring), with the assumptions asserted; and its features."""
    definitions = {commands[i].name: commands[i] for i in live
                   if commands[i].head in DECLARATIONS and commands[i].symbols}
    bools = {commands[i].name for i in live if commands[i].bool_constant}
    asserts = [commands[i] for i in live if commands[i].head == "assert"]
    guarded = [a for a in asserts if a.guard in bools]
    negated = [a for a in asserts if a.negated in bools]
    general = [a for a in asserts if a.guard not in bools and a.negated not in bools]
    base = set().union(*(a.symbols | ({a.guard} if a.guard else set()) for a in general))
    base |= {s for s, positive in check.assumptions if positive}
    base |= {s for s, positive in check.assumptions if not positive and s not in bools}
    kept = guarded
    while True:
        blocked = _closure(base.union(*(g.symbols for g in kept)), definitions)
        false = bools - blocked
        smaller = [g for g in kept if g.guard not in false]
        if len(smaller) == len(kept):
            break
        kept = smaller
    kept_ids = {id(a) for a in general + kept + [a for a in negated if a.negated not in false]}
    needed = _closure(blocked | {g.guard for g in kept}
                      | {a.negated for a in negated if a.negated not in false}, definitions)
    lines, feats = [], set()
    for i in live:
        c = commands[i]
        if (c.head == "assert" and id(c) in kept_ids) or (c.head in DECLARATIONS and (
                not c.name or c.name in needed or c.head in ("declare-sort", "define-sort"))):
            lines.append(c.text)
            feats |= c.features
    for s, positive in check.assumptions:
        if positive:
            lines.append(f"(assert {s})")
        elif s not in false:
            lines.append(f"(assert (not {s}))")
    return lines, frozenset(feats)


def replay(commands: Sequence[Command]) -> Iterable[Tuple[int, Command, List[int]]]:
    """The checks of a script in order: (index of the check, check, indices of the
    declarations and assertions in scope)."""
    frames: List[List[int]] = [[]]
    k = 0
    for i, c in enumerate(commands):
        if c.head in DECLARATIONS or c.head == "assert":
            frames[-1].append(i)
        elif c.head in ("push", "pop"):
            n = _scope_count(c.text)
            for _ in range(n):
                if c.head == "push":
                    frames.append([])
                elif len(frames) > 1:
                    frames.pop()
        elif c.head in CHECKS:
            k += 1
            yield k, c, [j for f in frames for j in f]


def _scope_count(text: str) -> int:
    m = re.search(r'\d+', text)
    return int(m.group()) if m else 1


def incremental(commands: Sequence[Command]) -> Tuple[List[str], FrozenSet[str], int]:
    """The commands of the cleaned incremental script, its features, its number of checks."""
    lines, feats, checks = [], set(), 0
    for c in commands:
        if c.head in DECLARATIONS or c.head in ("assert", "push", "pop"):
            lines.append(c.text)
            feats |= c.features
        elif c.head in CHECKS:
            checks += 1
            if c.status in ("sat", "unsat"):
                lines.append(f"(set-info :status {c.status})")
            lines.append(c.text if c.head == "check-sat-assuming" else "(check-sat)")
    return lines, frozenset(feats), checks


# ------------------------------------------------------------------ the directory

MANIFEST_FIELDS = ["file", "kind", "logic", "status", "check_sats", "bytes", "duplicate_of",
                   "task", "contract", "property", "call", "stage", "engine", "solver", "query",
                   "source", "note"]


def _safe(name: str) -> str:
    return re.sub(r'[^A-Za-z0-9_.+-]', '-', name)


class Tracer:
    """The directory of a run, and the task whose queries are being recorded."""

    def __init__(self, directory: str, logics: Optional[Sequence[str]] = None):
        self.dir = directory
        self.logics = {x.strip().upper() for x in logics} if logics else None
        for sub in ("incremental", "standalone", "sources", ".index"):
            os.makedirs(os.path.join(directory, sub), exist_ok=True)
        self.manifest = os.path.join(directory, "MANIFEST.csv")
        try:
            fd = os.open(self.manifest, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.write(fd, (",".join(MANIFEST_FIELDS) + "\n").encode())
            os.close(fd)
        except FileExistsError:
            pass
        self.start_task("", "")

    def start_task(self, contract: str, what: str):
        """The queries that follow belong to `what` (a property, or "invariants") of
        `contract`."""
        self.contract = os.path.relpath(contract, REPO) if contract else ""
        self.what = what
        base = os.path.splitext(os.path.basename(contract))[0]
        m = re.search(r'_v(\d+)$', base)
        family = os.path.basename(os.path.dirname(os.path.abspath(contract))) if contract else ""
        self.task = _safe(f"{family}-v{m.group(1) if m else 1}__{what}") if contract \
            else "task"
        self.calls = 0

    def wanted(self, logic: str) -> bool:
        return self.logics is None or logic in self.logics

    def stem(self, call: int, stage: str) -> str:
        return f"{self.task}__call{call:03d}-{stage}"

    def record(self, script: str, call: int, stage: str, engine: str, solver: str,
               source: str, split_only: bool = False, status: str = "") -> int:
        """Write the files of one script (a Kind 2 trace or a direct query); the number of
        rows added to the manifest."""
        commands, truncated = parse(script)
        lines, feats, checks = incremental(commands)
        if not checks:
            return 0
        rows = 0
        origin = dict(task=self.task, contract=self.contract, property=self.what, call=call,
                      stage=stage, engine=engine, solver=solver, source=source)
        stem = f"{self.stem(call, stage)}__{_safe(engine)}__{solver}"
        logic = logic_name(feats)
        if not split_only and self.wanted(logic):
            rows += self._write("incremental", f"{stem}__{logic}", lines, logic, "", checks,
                                dict(origin, note="truncated" if truncated else ""))
        if self.logics is not None and not (sublogics(feats) & self.logics):
            return rows
        for k, check, live in replay(commands):
            body, fs = standalone(commands, live, check)
            logic = logic_name(fs)
            if self.wanted(logic):
                rows += self._write("standalone", f"{stem}__q{k:04d}__{logic}", body + [
                    "(check-sat)"], logic, status or check.status, 1, dict(origin, query=k))
        return rows

    def _write(self, kind: str, stem: str, lines: List[str], logic: str, status: str,
               checks: int, row: dict) -> int:
        body = "\n".join(lines) + "\n(exit)\n"
        digest = hashlib.sha256(f"{kind}\n{logic}\n{status}\n{body}".encode()).hexdigest()
        name = f"{kind}/{stem}.smt2"
        index = os.path.join(self.dir, ".index", digest)
        duplicate = ""
        try:
            fd = os.open(index, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.write(fd, name.encode())
            os.close(fd)
        except FileExistsError:
            with open(index) as f:
                duplicate = f.read()
        if not duplicate:
            where = (f"contract {row['contract']}, {row['property']}, call {row['call']} "
                     f"({row['stage']}), engine {row['engine']}, solver {row['solver']}"
                     + (f", check-sat {row['query']} of the trace"
                        if row.get("query") and row["engine"] != "direct" else ""))
            header = ("(set-info :smt-lib-version 2.6)\n"
                      f"(set-info :source |Generated by KindHML: {where.replace('|', '/')}.|)\n"
                      f"(set-logic {logic})\n"
                      + (f"(set-info :status {status})\n"
                         if status in ("sat", "unsat") and kind == "standalone" else ""))
            with open(os.path.join(self.dir, name), "w") as f:
                f.write(header + body)
        out = io.StringIO()
        csv.DictWriter(out, fieldnames=MANIFEST_FIELDS).writerow(dict(
            row, file="" if duplicate else name, kind=kind, logic=logic, status=status,
            check_sats=checks, bytes=len(body), duplicate_of=duplicate))
        fd = os.open(self.manifest, os.O_WRONLY | os.O_APPEND)
        os.write(fd, out.getvalue().encode())
        os.close(fd)
        return 1


TRACER: Optional[Tracer] = None


def configure(directory: Optional[str], logics: Optional[str] = None):
    """Turn tracing on (`directory`), with a comma-separated list of logics (None: all)."""
    global TRACER
    TRACER = Tracer(directory, logics.split(",") if logics else None) if directory else None


def start_task(contract: str, what: str):
    if TRACER is not None:
        TRACER.start_task(contract, what)


def kind2_args() -> List[str]:
    return ["--smt_trace"] if TRACER is not None else []


def _stage() -> str:
    """The function that made the solver call: the first caller outside this module,
    `kind2.py` and `direct.py`."""
    f = sys._getframe(1)
    here = {os.path.join(os.path.dirname(os.path.abspath(__file__)), x)
            for x in ("smt_trace.py", "kind2.py", "direct.py")}
    while f is not None and os.path.abspath(f.f_code.co_filename) in here:
        f = f.f_back
    return f.f_code.co_name.strip("_").replace("_", "-") if f is not None else "main"


def record_kind2(output_dir: str, lustre: str, solver: str):
    """Record the traces that Kind 2 wrote in `output_dir` (its --output_dir)."""
    if TRACER is None:
        return
    TRACER.calls += 1
    call, stage = TRACER.calls, _stage()
    source = f"sources/{TRACER.stem(call, stage)}.lus"
    rows = 0
    traces = []
    for root, _, files in os.walk(os.path.join(output_dir, "smt_trace")):
        traces += [os.path.join(root, x) for x in files if x.endswith(".smt2")]
    for path in sorted(traces, key=_engine_order):
        engine = re.sub(r'^.*?\.lus\.', '', os.path.basename(path))[:-len(".smt2")]
        try:
            with open(path, errors="replace") as f:
                rows += TRACER.record(f.read(), call, stage, engine.replace(".", "-"), solver,
                                      source)
        except (OSError, ValueError, RecursionError) as e:
            print(f"smt_trace: {path}: {e}", file=sys.stderr)
    if rows:
        with open(os.path.join(TRACER.dir, source), "w") as f:
            f.write(lustre)


def _engine_order(path: str):
    """Traces by engine, then by number (invgenos.2 before invgenos.10)."""
    return [int(x) if x.isdigit() else x for x in re.split(r'(\d+)', os.path.basename(path))]


def record_query(script: str, status: str):
    """Record a query of `direct.py` (one check; `status` sat, unsat or unknown)."""
    if TRACER is None:
        return
    TRACER.calls += 1
    TRACER.record(script, TRACER.calls, _stage(), "direct", "z3", "", split_only=True,
                  status=status)
