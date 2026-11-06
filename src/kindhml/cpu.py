"""Cores and CPU time of a verification task.

A task may use several cores (`--cores`): it is pinned to N CPUs of its affinity set
(`pin`), and the processes it starts (Kind 2, its solvers, the workers of the parallel
portfolio) inherit them, so that the number of cores is the number actually used.

The CPU time of a task (user + system) is that of its Python processes (`python_seconds`: each
counts its own time, RUSAGE_SELF, and the workers it waited for) plus that of its solver runs,
read from the systemd slice of the task (`kind2.slice_cpu`). The `os.wait4` of a process does not
do: Kind 2's solvers are not waited for by Kind 2, and on a row with a wall time of 6.1 s the slice
counted 8.3 s of solvers, `os.wait4` 2.8 s in all (2026-11-06). Without systemd scopes, the
`os.wait4` time is the fallback.
"""

from __future__ import annotations

import os
import resource
from typing import List, Optional


def available() -> List[int]:
    """The CPUs this process may run on (its affinity set, as set by `taskset`)."""
    try:
        return sorted(os.sched_getaffinity(0))
    except (AttributeError, OSError):
        return list(range(os.cpu_count() or 1))


def resolve(spec: str) -> Optional[int]:
    """The number of cores of `--cores`: "auto", every available CPU but one (at least
    one); "0", none (unpinned, one process: the behaviour before the option existed);
    N >= 1, at most the available CPUs."""
    n = len(available())
    if spec == "auto":
        return max(1, n - 1)
    k = int(spec)
    if k < 0:
        raise ValueError(f"--cores: {spec}")
    return None if k == 0 else min(k, n)


def pin(cores: Optional[int]) -> List[int]:
    """Pin this process to the first `cores` CPUs of its affinity set; the CPUs used (all
    of them with None)."""
    cpus = available()
    if cores is None:
        return cpus
    chosen = cpus[:cores]
    try:
        os.sched_setaffinity(0, chosen)
    except (AttributeError, OSError):
        return cpus
    return chosen


# the CPU time of the worker processes of the parallel portfolio this process waited for (each
# reports its own `python_seconds`)
WORKERS = 0.0


def python_seconds() -> float:
    """The CPU time of this process (not of its children) and of the workers it waited for."""
    return rusage_seconds(resource.getrusage(resource.RUSAGE_SELF)) + WORKERS


def proc_seconds(pid: int) -> Optional[float]:
    """The CPU time of the live process `pid` so far (not of its children), from /proc."""
    try:
        with open(f"/proc/{pid}/stat") as f:
            fields = f.read().rsplit(")", 1)[1].split()
        return (int(fields[11]) + int(fields[12])) / os.sysconf("SC_CLK_TCK")
    except (OSError, IndexError, ValueError):
        return None


def rusage_seconds(ru) -> float:
    """User + system time of a `resource.struct_rusage`."""
    return ru.ru_utime + ru.ru_stime
