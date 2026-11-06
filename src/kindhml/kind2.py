"""Running Kind 2 and reading its JSON output."""

from __future__ import annotations

import atexit
import functools
import glob
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

from . import smt_trace
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


_VERSION = re.compile(r"\bv(\d+)\.(\d+)\.(\d+)")


def parse_version(text: str) -> Tuple[int, ...]:
    """The version in the output of `kind2 --version` ("kind2 v3.0.0", or "kind2
    v2.3.0-ge8216dd" for a development build after v2.3.0), or (0, 0, 0)."""
    m = _VERSION.search(text)
    return tuple(int(x) for x in m.groups()) if m else (0, 0, 0)


@functools.lru_cache(maxsize=None)
def version(kind2: str) -> Tuple[int, ...]:
    """The version of the Kind 2 binary `kind2`, read once per binary."""
    try:
        out = subprocess.run([kind2, "--version"], capture_output=True, text=True, timeout=30)
        return parse_version(out.stdout + out.stderr)
    except (OSError, subprocess.SubprocessError):
        return (0, 0, 0)


def text_args(kind2: str) -> List[str]:
    """Options of the plain-text output read by `parse_text`. From v3.0.0, the summary also
    prints the expression of each property (megabytes for large properties), unless
    --show_props false, an option that earlier versions reject."""
    return (["--color", "false", "--print_cex", "false"]
            + (["--show_props", "false"] if version(kind2) >= (3,) else []))


def default_args(kind2: str) -> List[str]:
    """Options that restore, in later versions, the defaults of the snapshot v2.3.0-ge8216dd.
    From v3.0.0, BMC no longer checks that each unrolling is satisfiable before it searches
    for a falsification (--bmc_check_unroll false): z3 then first gets a check-sat-assuming,
    on which it can get stuck (amm_real_v4 Sandwich: a free check refuted at k = 0 in 0.1 s
    after the plain check-sat, no answer in 60 s without it; z3 5.3.2, 2026-10-29)."""
    return ["--bmc_check_unroll", "true"] if version(kind2) >= (3,) else []


@dataclass
class PropertyResult:
    name: str
    status: str                 # 'valid', 'invalid', 'unknown', 'timeout', 'error'
    k: Optional[int] = None     # valid: induction depth; invalid: the steps of the
                                # counterexample after its initial state
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
            # a step of the transition system s = Init -> pre Trans(s, t) is a transaction,
            # constructor calls included (Kind 2's k, text and JSON outputs alike: a trace of 3
            # instants has k = 2); the fuzzer counts its transactions the same way
            k = (f" after {self.k} transaction{'' if self.k == 1 else 's'}"
                 if self.k is not None else "")
            return f"{status}{k}{t}"
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
    # Kind 2 stopped at its time limit before it had read the program ("Error opening input
    # file ...: Lib.TimeoutWall"): the front end needs more time than the run had
    front_end: bool = False


MEMORY_LIMIT_GB = 3     # for Kind 2 and its solvers together (per process as a fallback)
_HAVE_SCOPE: Optional[bool] = None

# The task this process works for (`set_root`): the systemd scopes of its solver runs are named
# kindhml-{ROOT}-{pid}-{id} and placed in the slice kindhml-{ROOT}.slice, so that the runs of a
# task, from any of the processes it forks, are found (`kill_runs`), measured (`slice_cpu`) and
# stopped (`stop_slice`) together. None: this process is its own root.
ROOT: Optional[int] = None


def root() -> int:
    return ROOT if ROOT is not None else os.getpid()


def slice_name(pid: Optional[int] = None) -> str:
    return f"kindhml-{root() if pid is None else pid}.slice"


def set_root(pid: Optional[int] = None, memory_mb: Optional[int] = None) -> None:
    """Make this process (or `pid`) the root of a task (see ROOT); with `memory_mb`, the
    slice of the task limits the memory of all its solver runs together (the slice is
    created first, with an empty scope, so that the limit holds from its first run)."""
    global ROOT
    ROOT = os.getpid() if pid is None else pid
    if memory_mb is not None and _memory_scope():
        for cmd in (_memory_scope() + ["true"],
                    ["systemctl", "--user", "set-property", "--runtime", slice_name(),
                     f"MemoryMax={memory_mb}M"]):
            try:
                subprocess.run(cmd, capture_output=True, timeout=10)
            except (OSError, subprocess.TimeoutExpired):
                pass


def slice_cpu(pid: int) -> Optional[float]:
    """The CPU time (s) used so far by the solver runs of the task rooted at `pid` (the
    cpu.stat of its slice, which includes solvers left behind by Kind 2), or None (no slice:
    no systemd user scopes, or no run)."""
    for path in glob.glob(f"/sys/fs/cgroup/user.slice/user-*.slice/user@*.service/"
                          f"kindhml.slice/{slice_name(pid)}/cpu.stat"):
        try:
            with open(path) as f:
                for line in f:
                    key, value = line.split()
                    if key == "usage_usec":
                        return int(value) / 1e6
        except (OSError, ValueError):
            pass
    return None


_AT_EXIT: dict = {}         # the slices to stop when this process exits, by the owner pid


def _stop_at_exit() -> None:
    for name in _AT_EXIT.get(os.getpid(), ()):
        try:
            subprocess.run(["systemctl", "--user", "stop", name], capture_output=True,
                           timeout=10)
        except (OSError, subprocess.TimeoutExpired):
            pass


def _note_slice() -> None:
    """The slice of this process's runs is stopped when it exits normally, unless it belongs
    to a task whose root stops it (`set_root`; a forked task or worker ends by `os._exit`,
    which skips this). Without it, every process that ran a solver (a pytest shard, a script)
    left an empty slice behind."""
    if ROOT is None and os.getpid() not in _AT_EXIT:
        if not _AT_EXIT:
            atexit.register(_stop_at_exit)
        _AT_EXIT[os.getpid()] = {slice_name()}


def stop_slice(pid: int) -> None:
    """Stop the slice of the task rooted at `pid`, with every process still in it (slices
    are not removed when their runs end: one per task would accumulate)."""
    if _HAVE_SCOPE is not False and shutil.which("systemctl"):
        try:
            subprocess.run(["systemctl", "--user", "stop", slice_name(pid)],
                           capture_output=True, timeout=10)
        except (OSError, subprocess.TimeoutExpired):
            pass


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
    scope = ["systemd-run", "--user", "--scope", "-q", f"--slice={slice_name()}",
             "-p", f"MemoryMax={memory_limit_mb()}M", "-p", "MemorySwapMax=0"]
    if _HAVE_SCOPE is None:
        try:
            # without the slice: a process that only probes must not leave a slice behind
            _HAVE_SCOPE = bool(shutil.which("systemd-run") and subprocess.run(
                ["systemd-run", "--user", "--scope", "-q", "true"], capture_output=True,
                timeout=10).returncode == 0)
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


def _uptime() -> float:
    try:
        with open("/proc/uptime") as f:
            return float(f.read().split()[0])
    except (OSError, ValueError, IndexError):
        return 0.0


def _belongs(pid: int, unit: Optional[str], since: float) -> bool:
    """Whether `pid` is still a process of a run: in its scope `unit`, or, without a scope,
    started after the run (at `since`, seconds since boot). A recorded pid may have been
    reused by another process, e.g. a solver of another worker of the same task."""
    try:
        if unit:
            with open(f"/proc/{pid}/cgroup") as f:
                return f"/{unit}.scope" in f.read()
        with open(f"/proc/{pid}/stat") as f:
            start = int(f.read().rsplit(")", 1)[1].split()[19]) / os.sysconf("SC_CLK_TCK")
        return start >= since - 1
    except (OSError, IndexError, ValueError):
        return False


def _cleanup(proc: subprocess.Popen, unit: Optional[str], watcher: "_Watcher",
             since: float = 0.0):
    """Kill Kind 2 and every process it started: the whole systemd scope if there is one,
    and in any case the process groups and the recorded descendants that still belong to
    the run (`_belongs`). The watcher thread is joined: a process forked later must not
    have it."""
    watcher.done.set()
    if watcher is not threading.current_thread():
        watcher.join(2)
    if unit:
        subprocess.run(["systemctl", "--user", "kill", "--signal=SIGKILL", unit + ".scope"],
                       capture_output=True, timeout=10)
        subprocess.run(["systemctl", "--user", "stop", unit + ".scope"],
                       capture_output=True, timeout=10)
    for pid in [proc.pid] + _descendants(proc.pid) + sorted(watcher.seen):
        if not _belongs(pid, unit, since):
            continue
        for kill in (lambda p: os.killpg(os.getpgid(p), signal.SIGKILL),
                     lambda p: os.kill(p, signal.SIGKILL)):
            try:
                if pid != os.getpid() and os.getpgid(pid) != os.getpgid(0):
                    kill(pid)
            except (ProcessLookupError, PermissionError):
                pass


def kill_runs(pid: int, alive: bool) -> None:
    """Kill the Kind 2 runs of process `pid` (`run`), with their solvers, when `pid` was stopped
    before `run` could clean up: their systemd scopes (those of the processes it forked too,
    if `pid` is the root of a task: `set_root`) and, if `pid` is still alive (otherwise its
    number may be reused), its descendants."""
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
    stop_slice(pid)


SOLVERS = ("z3", "cvc5", "cvc5-mbqi")


def find_z3() -> str:
    """$Z3, then the z3 next to the Python interpreter (pip package z3-solver), then z3 on
    the PATH."""
    bin_dir = os.path.dirname(os.path.abspath(sys.executable))
    for c in (os.environ.get("Z3"), os.path.join(bin_dir, "z3"), shutil.which("z3")):
        if c and os.path.isfile(c):
            return c
    raise FileNotFoundError("z3 not found: set $Z3 or pip install z3-solver")


def find_cvc5() -> Optional[str]:
    """$CVC5, then cvc5 on the PATH; None if neither exists."""
    for c in (os.environ.get("CVC5"), shutil.which("cvc5")):
        if c and os.path.isfile(c) and os.access(c, os.X_OK):
            return c
    return None


# cvc5 with MBQI alone (solver "cvc5-mbqi"), the script passed to Kind 2 with --cvc5_bin
CVC5_WRAPPER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bin", "cvc5-mbqi")


def cvc5_mbqi() -> bool:
    """Whether the solver "cvc5-mbqi" is cvc5 through `CVC5_WRAPPER`, which adds --no-cegqi
    --no-sygus-inst to Kind 2's options: MBQI alone, the strategy of cvc5's portfolio for
    quantified nonlinear integer arithmetic (the portfolio itself is off in incremental mode,
    the only mode Kind 2 uses). It finds models that Kind 2's options do not, and loses proofs
    that need CEGQI (DESIGN.md, "Solvers"). KINDHML_CVC5_OPTIONS=kind2: "cvc5-mbqi" is cvc5
    with Kind 2's options, as "cvc5"."""
    return os.environ.get("KINDHML_CVC5_OPTIONS", "mbqi") != "kind2" and find_cvc5() is not None


def solver_args(solver: str) -> List[str]:
    """Kind 2 options selecting the SMT solver (z3: `find_z3`; cvc5: Kind 2's options;
    cvc5-mbqi: `cvc5_mbqi`)."""
    if solver == "cvc5-mbqi" and cvc5_mbqi():
        return ["--smt_solver", "cvc5", "--cvc5_bin", CVC5_WRAPPER]
    if solver in ("cvc5", "cvc5-mbqi"):
        return ["--smt_solver", "cvc5"]
    if solver == "z3":
        return ["--smt_solver", "z3", "--z3_bin", find_z3()]
    raise ValueError(f"unknown solver {solver}")


def solver_env(solver: str) -> Optional[dict]:
    """The environment of Kind 2 for `solver`: with `CVC5_WRAPPER`, the cvc5 it runs; None
    (this process's environment) otherwise."""
    if solver == "cvc5-mbqi" and cvc5_mbqi():
        return {**os.environ, "KINDHML_CVC5_REAL": find_cvc5()}
    return None


# program (its hash) -> the largest time limit of a run that ended in the front end (`run`)
_FRONT_END_BUDGETS: dict = {}


def front_end_floor(lustre: str) -> float:
    """The least time limit worth a run of Kind 2 on `lustre`, learned from its earlier runs:
    twice the largest limit of a run that ended in the front end (0 if none). A run with that
    limit or less ends there too, and the budgets of the rounds double. On the transition
    system of lending_simple_int_v2 Liquidation_attack_any (16.9 MB), the front end of Kind 2
    v3.0.0 took 120-240 s, and the runs of 3-64 s of a 600 s check gave nothing
    (2026-11-05)."""
    return 2 * _FRONT_END_BUDGETS.get(hash(lustre), 0.0)


def note_front_end(lustre: str, timeout: Optional[float], out: "Kind2Output") -> None:
    """Records the time limit of a run on `lustre` whose output `out` ended in the front end."""
    if out.front_end and timeout is not None:
        key = hash(lustre)
        _FRONT_END_BUDGETS[key] = max(_FRONT_END_BUDGETS.get(key, 0.0), timeout)


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
        output = ["-json"] if cex else text_args(kind2)
        limit = ["--timeout", str(timeout)] if timeout is not None else []
        raw, err, killed, oom_kills = run_command(
            [kind2] + output + default_args(kind2) + solver_args(solver) + limit
            + ["--output_dir", tmp]
            + smt_trace.kind2_args() + (extra_args or []) + [path],
            timeout + 10 if timeout is not None else None, solver_env(solver))
        smt_trace.record_kind2(tmp, lustre, solver)
    if save_to:
        with open(save_to, "w") as f:
            f.write(raw)
    out = parse_output(raw, err) if cex else parse_text(raw, err)
    note_front_end(lustre, timeout, out)
    if killed:
        out.errors.append("Kind 2 did not stop in time and was killed")
        out.timed_out = True
    if oom_kills:
        out.memory_killed = True
        out.errors.append(f"the memory limit ({memory_limit_mb()} MB) killed"
                          f" {oom_kills} process(es)")
    return out


def run_command(cmd: List[str], timeout: Optional[float],
                env: Optional[dict] = None) -> Tuple[str, str, bool, int]:
    """Run a solver command (Kind 2, or z3 for `direct.py`) in a systemd scope named after
    the root of the task and this process, in the slice of the task (so that `kill_runs`
    finds it, and `slice_cpu` measures it), with the memory limit of `memory_limit_mb`,
    in the environment `env` (None: this process's). It is killed, with every process it
    started, after `timeout` seconds (None: no limit). Returns (stdout, stderr, whether it was
    killed at the timeout, processes killed by the memory limit)."""
    scope = _memory_scope()
    if scope:
        _note_slice()
    unit = f"kindhml-{root()}-{os.getpid()}-{uuid.uuid4().hex[:8]}" if scope else None
    prefix = scope + [f"--unit={unit}"] if scope else []
    since = _uptime()
    proc = subprocess.Popen(prefix + cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, start_new_session=True, env=env,
                            preexec_fn=None if scope else _limit_memory)
    watcher = _Watcher(proc.pid)
    watcher.start()
    try:
        raw, err = proc.communicate(timeout=timeout)
        killed = False
    except subprocess.TimeoutExpired:
        _cleanup(proc, unit, watcher, since)
        raw, err = proc.communicate()
        killed = True
    finally:
        _cleanup(proc, unit, watcher, since)
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
    return _front_end(Kind2Output(list(props.values()), errors, raw, timed_out=timed_out))


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
# the limit expired in the front end: Kind 2 reports its timeout exception as an error in
# opening the input file (v2.3 and v3.0.0)
_FRONT_END = re.compile(r"Error opening input file[^\n]*\s*Lib\.TimeoutWall")


def _front_end(out: Kind2Output) -> Kind2Output:
    """`out`, with `front_end` set, and its error replaced by a readable one, if the time
    limit expired in the front end."""
    if _FRONT_END.search(out.raw) or any(_FRONT_END.search(e) for e in out.errors):
        out.front_end = out.timed_out = True
        out.errors = [e for e in out.errors if "Error opening input file" not in e]
        out.errors.append("Kind 2 did not finish reading the program within its time limit")
    return out


def parse_text(raw: str, stderr: str = "") -> Kind2Output:
    """Kind 2's plain-text output (options of `text_args`). The answer for a property is
    printed as soon as it is found, and the final summary gives the depth up to which an
    undecided property holds (its heading is "Summary of Properties:" from v3.0.0)."""
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
        elif line.lower().startswith("summary of properties:"):
            summary = True
    return _front_end(Kind2Output(list(props.values()), errors, raw, timed_out=timed_out))


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
    """The streams of the main node, one column per step (inputs t, ib and the state s). The
    transaction t of a step leads to the state of the next one: that of the last step is not
    taken, and its cells are blank."""
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
        shown = steps - 1 if name.startswith("t.") else steps
        lines.append(name.ljust(width) + "".join(
            f" | {_value(values.get(k, '')) if k < shown else '':<11}" for k in range(steps)))
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
