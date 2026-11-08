"""Solver runs of a task (`kind2.run_command`): systemd scopes in the slice of the task, CPU
time, cleanup (`kind2.kill_runs`), and the cores of a task (`cpu.py`). Fake commands stand
for Kind 2."""

import os
import signal
import subprocess
import sys
import time

import pytest

from kindhml import cpu
from kindhml import kind2

needs_scopes = pytest.mark.skipif(not kind2._memory_scope(),
                                  reason="no systemd user scopes")


def _in_slice(root: int) -> list:
    """The processes in the slice of the task rooted at `root`."""
    out = []
    for name in os.listdir("/proc"):
        if name.isdigit():
            try:
                with open(f"/proc/{name}/cgroup") as f:
                    if f"/{kind2.slice_name(root)}/" in f.read():
                        out.append(int(name))
            except OSError:
                pass
    return out


def test_the_cores_of_a_task():
    n = len(cpu.available())
    assert cpu.resolve("auto") == max(1, n - 1)
    assert cpu.resolve("0") is None
    assert cpu.resolve("1") == 1
    assert cpu.resolve(str(n + 5)) == n
    with pytest.raises(ValueError):
        cpu.resolve("-1")


@needs_scopes
def test_a_run_stopped_at_its_limit_leaves_no_process():
    kind2.set_root()
    try:
        _, _, killed, _ = kind2.run_command(["sh", "-c", "sleep 100 & sleep 100"], 1)
        assert killed
        time.sleep(0.5)
        assert _in_slice(os.getpid()) == []
        assert kind2._descendants(os.getpid()) == []
    finally:
        kind2.stop_slice(os.getpid())
        kind2.ROOT = None


@needs_scopes
def test_the_cpu_time_of_the_runs_of_a_task():
    """A busy loop of 2 s of CPU time in a run: the slice of the task counts 2 s. (Bounded by
    the wall time, the loop got 1.3 s of CPU in a suite of 8 shards on 8 CPUs, 2026-11-08.)"""
    kind2.set_root()
    try:
        # the slice of this process may hold the runs of earlier tests
        before = kind2.slice_cpu(os.getpid()) or 0.0
        kind2.run_command([sys.executable, "-c",
                           "import time\nt = time.process_time()\n"
                           "while time.process_time() - t < 2: pass"], 30)
        used = (kind2.slice_cpu(os.getpid()) or 0.0) - before
        assert 1.8 <= used <= 2.4, used
    finally:
        kind2.stop_slice(os.getpid())
        kind2.ROOT = None


@needs_scopes
def test_the_runs_of_a_killed_task_are_stopped():
    """A task killed by SIGKILL during a run cannot clean up: `kill_runs` stops its runs."""
    pid = os.fork()
    if pid == 0:
        try:
            kind2.set_root()
            kind2.run_command(["sleep", "100"], None)
        finally:
            os._exit(0)
    try:
        for _ in range(50):
            if _in_slice(pid):
                break
            time.sleep(0.1)
        assert _in_slice(pid), "the run did not start"
        os.kill(pid, signal.SIGKILL)
        os.waitpid(pid, 0)
        assert _in_slice(pid)                           # the run survives its task
        kind2.kill_runs(pid, alive=False)
        time.sleep(0.5)
        assert _in_slice(pid) == []
    finally:
        kind2.stop_slice(pid)


def test_a_reused_pid_is_not_killed():
    """`_belongs`: a process of another run (another scope, or started before the run) is not
    one of this run's."""
    proc = subprocess.Popen(["sleep", "30"])
    try:
        assert not kind2._belongs(proc.pid, "kindhml-0-0-nothere", 0.0)
        assert not kind2._belongs(proc.pid, None, kind2._uptime() + 60)
        assert kind2._belongs(proc.pid, None, kind2._uptime() - 60)
    finally:
        proc.kill()
        proc.wait()
