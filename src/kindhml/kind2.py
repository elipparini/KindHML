"""Running Kind 2 and reading its JSON output."""

from __future__ import annotations

import json
import os
import re
import shutil
import signal
import subprocess
import sys
import threading
import uuid
import tempfile
from dataclasses import dataclass, field
from typing import List, Optional, Tuple

from .colors import PLAIN, Palette

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def _exit_on_sigterm(signum, frame):
    """SIGTERM (e.g. from `timeout`) raises SystemExit, so that `run` stops Kind 2 and its
    solvers in its `finally` (by default Python exits at once, leaving them running)."""
    sys.exit(128 + signum)


if threading.current_thread() is threading.main_thread() \
        and signal.getsignal(signal.SIGTERM) == signal.SIG_DFL:
    signal.signal(signal.SIGTERM, _exit_on_sigterm)


def find_kind2() -> str:
    """$KIND2, else ./kind2/kind2 in the repository, else `kind2` on the PATH."""
    candidates = [os.environ.get("KIND2"), os.path.join(REPO, "kind2", "kind2"),
                  shutil.which("kind2")]
    for c in candidates:
        if c and os.path.isfile(c) and os.access(c, os.X_OK):
            return c
    raise FileNotFoundError("Kind 2 not found: set $KIND2 or put the binary in kind2/kind2")


@dataclass
class PropertyResult:
    name: str
    status: str                 # 'valid', 'invalid', 'unknown', 'timeout', 'error'
    k: Optional[int] = None     # valid: induction depth; invalid: counterexample length
    engine: Optional[str] = None
    time: Optional[float] = None
    true_up_to: Optional[int] = None
    counterexample: Optional[list] = None

    def describe(self, c: Palette = PLAIN) -> str:
        t = f", {self.time:.3f}s" if self.time is not None else ""
        status = c.status(self.status)
        if self.status == "valid":
            k = f" (k={self.k})" if self.k is not None else ""
            return f"{status}{k} by {self.engine}{t}"
        if self.status == "invalid":
            return f"{status} after {self.k} steps{t}"
        if self.true_up_to is not None:
            return f"{status}, true up to {self.true_up_to} steps{t}"
        return f"{status}{t}"


@dataclass
class Kind2Output:
    properties: List[PropertyResult]
    errors: List[str] = field(default_factory=list)
    raw: str = ""
    memory_killed: bool = False
    # Kind 2 stopped at its time limit: its timeout message, its timeout exception (raised
    # when the limit expires before the analysis, e.g. while parsing a large program, and
    # reported as an error), or killed by `run` after the limit
    timed_out: bool = False


MEMORY_LIMIT_GB = 3     # for Kind 2 and its solvers together (per process as a fallback)
_HAVE_SCOPE: Optional[bool] = None


def memory_limit_mb() -> int:
    """The memory limit of a run: $KINDHML_MEMORY_GB if set, else the smaller of
    MEMORY_LIMIT_GB and half of the memory available now. A fixed limit is not enough: a
    run allowed 3 GB on a machine with less available memory caused a global OOM."""
    if os.environ.get("KINDHML_MEMORY_GB"):
        return int(float(os.environ["KINDHML_MEMORY_GB"]) * 1024)
    limit = MEMORY_LIMIT_GB * 1024
    try:
        with open("/proc/meminfo") as f:
            info = dict(line.split(":", 1) for line in f)
        available = int(info["MemAvailable"].split()[0]) // 1024
        limit = min(limit, max(available // 2, 256))
    except (OSError, KeyError, ValueError):
        pass
    return limit


def _memory_scope() -> List[str]:
    """A `systemd-run` prefix limiting the memory of Kind 2 and all its solvers together,
    or [] if systemd user scopes are not available."""
    global _HAVE_SCOPE
    scope = ["systemd-run", "--user", "--scope", "-q",
             "-p", f"MemoryMax={memory_limit_mb()}M", "-p", "MemorySwapMax=0"]
    if _HAVE_SCOPE is None:
        try:
            _HAVE_SCOPE = bool(shutil.which("systemd-run") and subprocess.run(
                scope + ["true"], capture_output=True, timeout=10).returncode == 0)
        except (OSError, subprocess.TimeoutExpired):
            _HAVE_SCOPE = False
    return scope if _HAVE_SCOPE else []


def _limit_memory():
    """Fallback limit (the address-space limit cannot be used: OCaml 5 reserves a large
    virtual heap at start-up)."""
    import resource
    limit = memory_limit_mb() * 1024 ** 2
    resource.setrlimit(resource.RLIMIT_DATA, (limit, limit))


def _children() -> dict:
    """ppid -> list of pids, from /proc."""
    out: dict = {}
    for name in os.listdir("/proc"):
        if name.isdigit():
            try:
                with open(f"/proc/{name}/stat") as f:
                    ppid = int(f.read().rsplit(")", 1)[1].split()[1])
                out.setdefault(ppid, []).append(int(name))
            except (OSError, IndexError, ValueError):
                pass
    return out


def _descendants(pid: int) -> List[int]:
    children, todo, seen = _children(), [pid], []
    while todo:
        p = todo.pop()
        for c in children.get(p, []):
            seen.append(c)
            todo.append(c)
    return seen


class _Watcher(threading.Thread):
    """Records the descendants of a process while it runs: Kind 2 starts its solvers in
    other process groups, and solvers it leaves behind are reparented when it exits."""

    def __init__(self, pid: int):
        super().__init__(daemon=True)
        self.pid, self.seen, self.done = pid, set(), threading.Event()
        self.events: Optional[str] = None   # memory.events of the scope's cgroup
        self.oom_kills = 0                  # processes killed by the scope's memory limit

    def run(self):
        while not self.done.wait(0.2):
            self.seen.update(_descendants(self.pid))
            self._poll_memory()

    def _poll_memory(self):
        try:
            if self.events is None:
                with open(f"/proc/{self.pid}/cgroup") as f:
                    path = f.read().strip().split("::", 1)[1]
                self.events = f"/sys/fs/cgroup{path}/memory.events"
            with open(self.events) as f:
                for line in f:
                    key, value = line.split()
                    if key == "oom_kill":
                        self.oom_kills = max(self.oom_kills, int(value))
        except (OSError, IndexError, ValueError):
            pass


def _cleanup(proc: subprocess.Popen, unit: Optional[str], watcher: "_Watcher"):
    """Kill Kind 2 and every process it started: the whole systemd scope if there is one,
    and in any case the process groups and the recorded descendants."""
    watcher.done.set()
    if unit:
        subprocess.run(["systemctl", "--user", "kill", "--signal=SIGKILL", unit + ".scope"],
                       capture_output=True, timeout=10)
        subprocess.run(["systemctl", "--user", "stop", unit + ".scope"],
                       capture_output=True, timeout=10)
    for pid in [proc.pid] + _descendants(proc.pid) + sorted(watcher.seen):
        for kill in (lambda p: os.killpg(os.getpgid(p), signal.SIGKILL),
                     lambda p: os.kill(p, signal.SIGKILL)):
            try:
                if pid != os.getpid() and os.getpgid(pid) != os.getpgid(0):
                    kill(pid)
            except (ProcessLookupError, PermissionError):
                pass


def kill_runs(pid: int, alive: bool) -> None:
    """Kill the Kind 2 runs of process `pid` (`run`), with their solvers, when `pid` was stopped
    before `run` could clean up: their systemd scopes and, if `pid` is still alive (otherwise
    its number may be reused), its descendants."""
    if alive:
        for p in _descendants(pid):
            try:
                os.kill(p, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass
    if _HAVE_SCOPE is not False and shutil.which("systemctl"):
        try:
            subprocess.run(["systemctl", "--user", "kill", "--signal=SIGKILL",
                            f"kindhml-{pid}-*.scope"], capture_output=True, timeout=10)
        except (OSError, subprocess.TimeoutExpired):
            pass


SOLVERS = ("z3", "cvc5")


def find_z3() -> str:
    """$Z3, then the z3 next to the Python interpreter (pip package z3-solver), then z3 on
    the PATH."""
    bin_dir = os.path.dirname(os.path.abspath(sys.executable))
    for c in (os.environ.get("Z3"), os.path.join(bin_dir, "z3"), shutil.which("z3")):
        if c and os.path.isfile(c):
            return c
    raise FileNotFoundError("z3 not found: set $Z3 or pip install z3-solver")


def solver_args(solver: str) -> List[str]:
    """Kind 2 options selecting the SMT solver (z3: `find_z3`)."""
    if solver == "cvc5":
        return ["--smt_solver", "cvc5"]
    if solver == "z3":
        return ["--smt_solver", "z3", "--z3_bin", find_z3()]
    raise ValueError(f"unknown solver {solver}")


def run(lustre: str, timeout: Optional[float], extra_args: Optional[List[str]] = None,
        kind2: Optional[str] = None, save_to: Optional[str] = None,
        solver: str = "z3", cex: bool = False) -> Kind2Output:
    """Check all properties of a Lustre program. `timeout` is Kind 2's own timeout (s), or
    None for no limit; Kind 2 is killed, with its solvers, if it has not stopped 10 s later.
    `memory_killed` in the result tells whether the memory limit killed a process.
    With `cex`, Kind 2's JSON output is read, which contains the counterexamples. Without,
    the plain-text output is read, with counterexamples disabled: Kind 2 always builds them
    in JSON mode, which can take longer than finding them (and cannot be interrupted)."""
    kind2 = kind2 or find_kind2()
    with tempfile.TemporaryDirectory(prefix="kindhml_") as tmp:
        path = os.path.join(tmp, "task.lus")
        with open(path, "w") as f:
            f.write(lustre)
        output = ["-json"] if cex else ["--color", "false", "--print_cex", "false"]
        limit = ["--timeout", str(timeout)] if timeout is not None else []
        raw, err, killed, oom_kills = run_command(
            [kind2] + output + solver_args(solver) + limit + ["--output_dir", tmp]
            + (extra_args or []) + [path], timeout + 10 if timeout is not None else None)
    if save_to:
        with open(save_to, "w") as f:
            f.write(raw)
    out = parse_output(raw, err) if cex else parse_text(raw, err)
    if killed:
        out.errors.append("Kind 2 did not stop in time and was killed")
        out.timed_out = True
    if oom_kills:
        out.memory_killed = True
        out.errors.append(f"the memory limit ({memory_limit_mb()} MB) killed"
                          f" {oom_kills} process(es)")
    return out


def run_command(cmd: List[str], timeout: Optional[float]) -> Tuple[str, str, bool, int]:
    """Run a solver command (Kind 2, or z3 for `direct.py`) in a systemd scope named after
    this process (so that `kill_runs` finds it), with the memory limit of `memory_limit_mb`.
    It is killed, with every process it started, after `timeout` seconds (None: no limit).
    Returns (stdout, stderr, whether it was killed at the timeout, processes killed by the
    memory limit)."""
    scope = _memory_scope()
    unit = f"kindhml-{os.getpid()}-{uuid.uuid4().hex[:8]}" if scope else None
    prefix = scope + [f"--unit={unit}"] if scope else []
    proc = subprocess.Popen(prefix + cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, start_new_session=True,
                            preexec_fn=None if scope else _limit_memory)
    watcher = _Watcher(proc.pid)
    watcher.start()
    try:
        raw, err = proc.communicate(timeout=timeout)
        killed = False
    except subprocess.TimeoutExpired:
        _cleanup(proc, unit, watcher)
        raw, err = proc.communicate()
        killed = True
    finally:
        _cleanup(proc, unit, watcher)
    return raw, err, killed, watcher.oom_kills


def _json_objects(raw: str) -> List[dict]:
    """The top-level objects of Kind 2's JSON array, decoded one at a time, so that the
    output of a killed run (truncated) and stray text between objects are tolerated.
    Control characters are allowed in strings (property names may contain newlines)."""
    decoder = json.JSONDecoder(strict=False)
    objects: List[dict] = []
    i = raw.find("{")
    while i >= 0:
        try:
            o, end = decoder.raw_decode(raw, i)
        except json.JSONDecodeError:
            nxt = raw.find("\n{", i + 1)      # top-level objects start a line
            i = nxt + 1 if nxt >= 0 else -1
            continue
        if isinstance(o, dict):
            objects.append(o)
        i = raw.find("{", end)
    return objects


def _no_output(raw: str, stderr: str) -> Kind2Output:
    msg = "no output from Kind 2"
    if stderr.strip():
        msg += ": " + stderr.strip().splitlines()[-1]
    return Kind2Output([], [msg], raw)


def parse_output(raw: str, stderr: str = "") -> Kind2Output:
    """Kind 2's JSON output (option -json)."""
    objects = _json_objects(raw)
    if not objects:
        return _no_output(raw, stderr)
    props: dict = {}
    errors: List[str] = []
    timed_out = False
    for o in objects:
        kind = o.get("objectType")
        if kind == "log" and o.get("level") in ("error", "fatal"):
            errors.append(str(o.get("value")))
        elif kind == "property" and o.get("isCandidate") != "true":
            props[o["name"]] = _property(o)
        if kind == "log" and _TIMEOUT.search(str(o.get("value"))):
            timed_out = True
    return Kind2Output(list(props.values()), errors, raw, timed_out=timed_out)


# Engine names of the plain-text output, abbreviated as in the JSON output.
_ENGINES = {"bounded model checking": "bmc", "inductive step": "ind", "2-induction": "ind2",
            "property directed reachability (IA)": "ic3ia",
            "property directed reachability (QE)": "ic3qe"}
_ANSWER = re.compile(r"<(?:Success|Failure)> Property (\S+) is (valid|invalid) by (.+?)"
                     r"(?: for k=(\d+))? after ([0-9.]+)s\.$")
_SUMMARY = re.compile(r"(\S+): (valid|invalid|true up to|unknown)"
                      r"(?: \(k=(\d+)\)| after (\d+) steps| (\d+) steps)?$")
# Kind 2's timeout: its message, and its exception when the limit expires before the analysis
_TIMEOUT = re.compile(r"Wallclock timeout|Lib\.TimeoutWall")


def parse_text(raw: str, stderr: str = "") -> Kind2Output:
    """Kind 2's plain-text output (options --color false --print_cex false). The answer
    for a property is printed as soon as it is found, and the final summary gives the
    depth up to which an undecided property holds."""
    if not raw.strip():
        return _no_output(raw, stderr)
    props: dict = {}
    errors: List[str] = []
    summary = False
    timed_out = _TIMEOUT.search(raw) is not None
    for line in raw.splitlines():
        answer = _ANSWER.match(line)
        final = summary and _SUMMARY.match(line)
        if answer:
            name, value, engine, k, t = answer.groups()
            props[name] = PropertyResult(name, value, int(k) if k else None,
                                         _ENGINES.get(engine, engine), float(t))
        elif final:
            name, word, k_valid, k_invalid, up_to = final.groups()
            status = word if word in ("valid", "invalid") else "unknown"
            p = props.setdefault(name, PropertyResult(name, status))
            if p.k is None and (k_valid or k_invalid):
                p.k = int(k_valid or k_invalid)
            if up_to:
                p.true_up_to = int(up_to)
        elif line.startswith(("<Error>", "<Timeout>")):
            errors.append(line.split("> ", 1)[1])
        elif line.startswith("Summary of properties:"):
            summary = True
    return Kind2Output(list(props.values()), errors, raw, timed_out=timed_out)


def _property(o: dict) -> PropertyResult:
    answer = o.get("answer", {})
    value = answer.get("value")
    runtime = o.get("runtime", {})
    time = runtime.get("value")
    status = {"valid": "valid", "falsifiable": "invalid", "reachable": "invalid",
              "unknown": "unknown"}.get(value, "error")
    if status == "unknown" and runtime.get("timeout"):
        status = "timeout"
    k = o.get("k")
    if status == "invalid" and o.get("counterExample"):
        k = _trace_length(o["counterExample"]) - 1
    return PropertyResult(o.get("name", "?"), status, k, answer.get("source"), time,
                          o.get("trueFor"), o.get("counterExample"))


def format_counterexample(cex: list, main: str = "main", c: Palette = PLAIN) -> str:
    """The streams of the main node, one column per step (inputs t, ib and the state s)."""
    rows, steps = [], 0
    for block in cex:
        if block.get("name") != main:
            continue
        for stream in block.get("streams", []):
            values = {int(k): v for k, v in stream.get("instantValues", [])}
            steps = max(steps, len(values))
            rows.append((stream["name"], values))
    if not rows:
        return ""
    width = max(len(n) for n, _ in rows)
    lines = [c.bold(" " * width + "".join(f" | step {k:<6}" for k in range(steps)))]
    for name, values in sorted(rows, key=lambda r: (not r[0].startswith("t."), r[0])):
        lines.append(name.ljust(width) + "".join(f" | {_value(values.get(k, '')):<11}"
                                                 for k in range(steps)))
    return "\n".join(lines)


def _value(v) -> str:
    """A value of a stream; Kind 2 writes a real as {"num": n, "den": d}."""
    if isinstance(v, dict) and set(v) == {"num", "den"}:
        return str(v["num"]) if v["den"] == 1 else f"{v['num']}/{v['den']}"
    return str(v)


def _trace_length(cex: list) -> int:
    for block in cex:
        for stream in block.get("streams", []):
            return len(stream.get("instantValues", []))
    return 0
