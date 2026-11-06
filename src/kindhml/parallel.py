"""Several cores for one check (DESIGN.md, Sect. 6, "Several cores"): the sides of a check
(`verify._CombinedCombiner`, `verify._AnyCombiner`) run in worker processes, forked from the
process of the check (the coordinator), which applies the same combiner as the serial drivers.

Placement: the N CPUs of the check (its affinity set, `cpu.pin`) are split among the workers;
each worker is pinned to its own CPUs (Kind 2 and its solvers inherit them, so that Kind 2,
with its parallel engines, cannot take the CPUs of the others) and runs one side, or several
in turn when there are more sides than CPUs (one round each, as the serial drivers do; a side
is then `alone` when it is the only live side of its worker). A free CPU starts the next side
with more users early (`_AnyCombiner.spare_side`), one at a time.

Messages (small, over pipes; no `multiprocessing.Queue`, whose feeder thread would make later
forks unsafe): a worker sends ("end", side, outcome) when a side ends (the outcome without its
property, re-attached here: a deep formula exceeds the recursion limit of pickle), and
("bye", its CPU time, the progress of its Houdinis) when it has no live side; the coordinator
sends ("close", side) to stop a side of a worker with several. A worker with no other live side
is stopped by SIGTERM, which raises SystemExit (`kind2.py`), so that its Kind 2 runs are stopped
in their `finally`; SIGKILL follows after GRACE seconds, and `kind2.kill_runs` stops whatever
is left in the slice of the check. A worker dies with the coordinator (PR_SET_PDEATHSIG). A side
that raises, or whose worker dies without a result, ends with status "error"; the other sides go
on.
"""

from __future__ import annotations

import ctypes
import os
import signal
import threading
import time
from dataclasses import dataclass, field, replace
from multiprocessing import Pipe
from multiprocessing.connection import Connection, wait
from typing import Callable, Dict, List, Optional

from . import cpu

GRACE = 5.0                 # seconds for a worker to stop after SIGTERM (then SIGKILL)
DEADLINE_GRACE = 30.0       # seconds after the deadline before live workers are stopped
PR_SET_PDEATHSIG = 1


def _die_with_parent(parent: int) -> None:
    """SIGTERM to this process when its parent dies (Linux), and exit if it already has."""
    try:
        ctypes.CDLL("libc.so.6", use_errno=True).prctl(PR_SET_PDEATHSIG, signal.SIGTERM)
    except (OSError, AttributeError):
        pass
    if os.getppid() != parent:
        os._exit(1)


def merge_progress(reports: List[dict]) -> dict:
    """One progress per Houdini (`verify.houdini_progress`) from the reports of several
    workers: a finished one (proved is not None) first, else the one with more candidates
    dropped (Houdini only drops candidates)."""
    best: dict = {}
    for report in reports:
        for key, p in report.items():
            candidates, dropped, proved = p[0], p[1], p[2]
            rank = (proved is not None, len(dropped or ()))
            if key not in best or rank > best[key][0]:
                best[key] = (rank, p)
    return {k: p for k, (_, p) in best.items()}


@dataclass
class _Worker:
    pid: int
    conn: Connection
    sides: List[int]
    cpus: List[int]
    alive: bool = True
    said_bye: bool = False


@dataclass
class Coordinator:
    """The parallel driver of one check: `drive(comb)` with a combiner made with
    `stop=self.stop`."""
    cores: int
    deadline: Optional[float]
    prop: object                        # S.Property, re-attached to the outcomes
    context: dict
    step: Callable                      # verify._step
    progress: Callable                  # verify.houdini_progress
    resume: Callable                    # verify.resume_houdini
    failed: Callable                    # (prop, status, message) -> an Outcome
    cpus: List[int] = field(default_factory=list)
    workers: List[_Worker] = field(default_factory=list)
    ids: Dict[int, object] = field(default_factory=dict)        # side id -> _Side
    where: Dict[int, _Worker] = field(default_factory=dict)     # side id -> its worker
    reports: List[dict] = field(default_factory=list)

    def __post_init__(self):
        self.cpus = cpu.available()[:self.cores]

    # ------------------------------------------------------------ the combiner's side

    def stop(self, side) -> None:
        """Stop a side (a side covered by a proof, or every side at a verdict)."""
        i = id(side)
        w = self.where.get(i)
        if w is None or not w.alive:
            return
        others = [j for j in w.sides if j != i and self.ids[j].outcome is None]
        if others:
            try:
                w.conn.send(("close", i))
            except (BrokenPipeError, OSError):
                pass
        else:
            self._terminate(w)

    # ------------------------------------------------------------ workers

    def _free(self) -> List[int]:
        used = {c for w in self.workers if w.alive for c in w.cpus}
        return [c for c in self.cpus if c not in used]

    def _start(self, sides: list, cpus: List[int]) -> None:
        """Fork a worker for `sides`, pinned to `cpus`."""
        assert threading.active_count() == 1, "fork with other threads alive"
        for s in sides:
            self.ids[id(s)] = s
        recv, send = Pipe()
        parent = os.getpid()
        pid = os.fork()
        if pid == 0:
            try:
                recv.close()
                _die_with_parent(parent)
                os.sched_setaffinity(0, cpus)
                self._work(send, sides)
            finally:
                os._exit(0)
        send.close()
        w = _Worker(pid, recv, [id(s) for s in sides], list(cpus))
        self.workers.append(w)
        for s in sides:
            self.where[id(s)] = w

    def _work(self, conn: Connection, sides: list) -> None:
        """The loop of a worker: one round of each live side in turn."""
        live = {id(s): s for s in sides}
        for s in sides:
            s.alone = lambda: len(live) == 1
        while live:
            for i, s in list(live.items()):
                while conn.poll():
                    what, j = conn.recv()
                    if what == "close" and j in live:
                        live.pop(j).gen.close()
                if i not in live:
                    continue
                try:
                    ended = self.step(s)
                except Exception as e:              # a bug: the side fails, not the check
                    s.outcome = self.failed(s.prop or self.prop, "error",
                                            f"side failed: {type(e).__name__}: {e}")
                    ended = True
                if ended:
                    del live[i]
                    conn.send(("end", i, replace(s.outcome, prop=None)))
        conn.send(("bye", cpu.python_seconds(), self.progress(self.context)))

    def _terminate(self, w: _Worker) -> None:
        """Stop a worker: SIGTERM, GRACE seconds, SIGKILL; reap it."""
        if not w.alive:
            return
        w.alive = False
        used = cpu.proc_seconds(w.pid)
        try:
            os.kill(w.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        end = time.time() + GRACE
        while time.time() < end:
            if os.waitpid(w.pid, os.WNOHANG)[0] == w.pid:
                break
            time.sleep(0.05)
        else:
            try:
                os.kill(w.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            os.waitpid(w.pid, 0)
        if not w.said_bye and used is not None:
            cpu.WORKERS += used
        w.conn.close()

    def _ended_worker(self, w: _Worker, comb) -> Optional[object]:
        """A worker closed its pipe: reap it; its sides still live end with status "error"."""
        if w.alive:
            w.alive = False
            try:
                _, status = os.waitpid(w.pid, 0)
            except ChildProcessError:
                status = None
            w.conn.close()
            for i in w.sides:
                s = self.ids[i]
                if s.outcome is None:
                    s.outcome = self.failed(self.prop, "error",
                                            f"worker ended without a result (status {status})")
                    v = comb.ended(s)
                    if v is not None:
                        return v
        return None

    # ------------------------------------------------------------ the driver

    def _place(self, sides: list) -> None:
        """The first workers: one per side while there are CPUs (sides in turn otherwise),
        the CPUs split evenly."""
        free = self._free() or self.cpus
        n = min(len(sides), len(free))
        if n == 0:
            return
        groups = [sides[k::n] for k in range(n)]
        size, extra = divmod(len(free), n)
        at = 0
        for k, group in enumerate(groups):
            take = size + (1 if k < extra else 0)
            self._start(group, free[at:at + take])
            at += take

    def drive(self, comb) -> object:
        """The outcome of the check, as the serial driver of `comb` would give."""
        try:
            sides = comb.live()
            if len(sides) < len(self.cpus) and hasattr(comb, "spare_side"):
                s = comb.spare_side()
                if s is not None:
                    sides = sides + [s]
            self._place(sides)
            while True:
                live = [w for w in self.workers if w.alive]
                if not live:
                    break
                wait_for = None
                if self.deadline is not None:
                    wait_for = max(0.0, self.deadline + DEADLINE_GRACE - time.time())
                ready = wait([w.conn for w in live], timeout=wait_for)
                if not ready:                       # past the deadline and its grace
                    break
                for conn in ready:
                    w = next(x for x in live if x.conn is conn)
                    try:
                        msg = conn.recv()
                    except (EOFError, OSError):
                        v = self._ended_worker(w, comb)
                        if v is not None:
                            comb.close()
                            return v
                        continue
                    if msg[0] == "end":
                        s = self.ids[msg[1]]
                        if s.outcome is not None:   # stopped meanwhile (covered)
                            continue
                        s.outcome = replace(msg[2], prop=self.prop)
                        v = comb.ended(s)
                        if v is not None:
                            comb.close()
                            return v
                    elif msg[0] == "bye":
                        w.said_bye = True
                        cpu.WORKERS += msg[1]
                        self.reports.append(msg[2])
                        self._terminate(w)
                self._more(comb)
            return comb.final() if comb.done() else self._unfinished(comb)
        finally:
            for w in self.workers:
                self._terminate(w)
            self.resume(self.context, merge_progress(self.reports))

    def _more(self, comb) -> None:
        """New sides on free CPUs: the next side due (`next_side`), else one side with more
        users early (`spare_side`)."""
        free = self._free()
        if not free:
            return
        s = comb.next_side() if hasattr(comb, "next_side") else None
        if s is None and hasattr(comb, "spare_side"):
            s = comb.spare_side()
        if s is not None:
            self._start([s], free)

    def _unfinished(self, comb) -> object:
        """Past the deadline and its grace with sides still live (a side ends by itself at
        the deadline: this is a guard): they end without a verdict."""
        for s in comb.live():
            s.outcome = self.failed(self.prop, "unknown", "stopped after the time limit")
        return comb.final()
