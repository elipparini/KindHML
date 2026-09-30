"""Running Kind 2 and reading its JSON output."""

from __future__ import annotations

import json
import os
import shutil
import signal
import subprocess
import tempfile
from dataclasses import dataclass, field
from typing import List, Optional

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


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

    def describe(self) -> str:
        t = f", {self.time:.3f}s" if self.time is not None else ""
        if self.status == "valid":
            k = f" (k={self.k})" if self.k is not None else ""
            return f"valid{k} by {self.engine}{t}"
        if self.status == "invalid":
            return f"invalid after {self.k} steps{t}"
        if self.true_up_to is not None:
            return f"{self.status}, true up to {self.true_up_to} steps{t}"
        return f"{self.status}{t}"


@dataclass
class Kind2Output:
    properties: List[PropertyResult]
    errors: List[str] = field(default_factory=list)
    raw: str = ""


MEMORY_LIMIT_GB = 3     # for Kind 2 and its solvers together (per process as a fallback)
_SCOPE: Optional[List[str]] = None


def _memory_scope() -> List[str]:
    """A `systemd-run` prefix limiting the memory of Kind 2 and all its solvers together,
    or [] if systemd user scopes are not available."""
    global _SCOPE
    if _SCOPE is None:
        scope = ["systemd-run", "--user", "--scope", "-q",
                 "-p", f"MemoryMax={MEMORY_LIMIT_GB}G", "-p", "MemorySwapMax=0"]
        try:
            ok = shutil.which("systemd-run") and subprocess.run(
                scope + ["true"], capture_output=True, timeout=10).returncode == 0
        except (OSError, subprocess.TimeoutExpired):
            ok = False
        _SCOPE = scope if ok else []
    return _SCOPE


def _limit_memory():
    """Fallback limit (the address-space limit cannot be used: OCaml 5 reserves a large
    virtual heap at start-up)."""
    import resource
    limit = MEMORY_LIMIT_GB * 1024 ** 3
    resource.setrlimit(resource.RLIMIT_DATA, (limit, limit))


def _kill_group(proc: subprocess.Popen):
    """Kill Kind 2 and every solver process it started (they share its process group)."""
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def run(lustre: str, timeout: float, extra_args: Optional[List[str]] = None,
        kind2: Optional[str] = None, save_to: Optional[str] = None) -> Kind2Output:
    """Check all properties of a Lustre program. `timeout` is Kind 2's own timeout (s);
    Kind 2 is killed, with its solvers, if it has not stopped 10 s later."""
    kind2 = kind2 or find_kind2()
    with tempfile.TemporaryDirectory(prefix="kindhml_") as tmp:
        path = os.path.join(tmp, "task.lus")
        with open(path, "w") as f:
            f.write(lustre)
        scope = _memory_scope()
        cmd = scope + [kind2, "-json", "--smt_solver", "cvc5", "--timeout", str(timeout),
                       "--output_dir", tmp] + (extra_args or []) + [path]
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                start_new_session=True,
                                preexec_fn=None if scope else _limit_memory)
        try:
            raw, _ = proc.communicate(timeout=timeout + 10)
            killed = False
        except subprocess.TimeoutExpired:
            _kill_group(proc)
            raw, _ = proc.communicate()
            killed = True
        finally:
            _kill_group(proc)
    if save_to:
        with open(save_to, "w") as f:
            f.write(raw)
    out = parse_output(raw)
    if killed:
        out.errors.append("Kind 2 did not stop in time and was killed")
    return out


def parse_output(raw: str) -> Kind2Output:
    try:
        objects = json.loads(raw)
    except json.JSONDecodeError:
        # Output of a killed run: keep the complete objects printed so far.
        cut = raw.rfind("\n}")
        try:
            objects = json.loads(raw[:cut + 2].rstrip().rstrip(",") + "\n]") if cut >= 0 else []
        except json.JSONDecodeError:
            return Kind2Output([], ["cannot parse the output of Kind 2"], raw)
    props: dict = {}
    errors: List[str] = []
    true_up_to: dict = {}
    for o in objects:
        kind = o.get("objectType")
        if kind == "log" and o.get("level") in ("error", "fatal"):
            errors.append(str(o.get("value")))
        elif kind == "kind2Output":
            continue
        elif kind == "property" and o.get("isCandidate") != "true":
            props[o["name"]] = _property(o)
        elif kind == "progress" and "k" in o:
            pass
    for name, p in props.items():
        if name in true_up_to and p.status != "valid":
            p.true_up_to = true_up_to[name]
    return Kind2Output(list(props.values()), errors, raw)


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


def _trace_length(cex: list) -> int:
    for block in cex:
        for stream in block.get("streams", []):
            return len(stream.get("instantValues", []))
    return 0
