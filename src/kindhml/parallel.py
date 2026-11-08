"""Several cores for one check (DESIGN.md, Sect. 6, "Several cores"): the sides of a check
(`verify._CombinedCombiner`, `verify._AnyCombiner`), and the tasks of a side (its lanes), run
in worker processes forked from the process of the check (the coordinator), which applies the
same combiner as the serial drivers.

Placement (`_plan`): every live side gets a worker; with more sides than CPUs, a worker runs
several whole sides in turn (one round each, as the serial drivers do; a side is then `alone`
when it is the only live side of its worker). The CPUs left split sides into lanes
(`verify._Side.lanes`: Kind 2 first, then the proofs, then the fuzzer, then the completion),
the sides in order, one more lane at a time; then they start the next side with more users
early (`_AnyCombiner.spare_side`, one at a time); the rest go to the workers that run Kind 2,
whose engines run in parallel. Each worker is pinned to its own CPUs among those of the check
(Kind 2 and its solvers inherit them, so that Kind 2 cannot take the CPUs of the others).
The CPUs of the workers that end go first to a side that is due (`next_side`, `spare_side`);
the others are lent to the live workers that run Kind 2 (`_lend`: the worker, Kind 2 and its
solvers are pinned again), and taken back when a side becomes due (`_reclaim`). On vault_v3
`Two_steps_drainability`, the proof for n >= 5 came at 20 s, and the exact sides with 3 and 4
users then ran Kind 2 on one CPU each until 208 s, with 6 CPUs idle (2026-11-08).

Lanes: a side split into lanes runs `verify._rounds` with a `verify._Lane` in each of its
workers; a decided outcome of a lane is the outcome of the side (the other lanes stop), and the
outcomes of lanes without a verdict merge into one when all have ended (`merge`). The facts of
a lane (the counterexample to induction of the proofs, the end of the searches) go to the
coordinator, which sends them to the other lanes of the side.

Messages (small, over pipes; no `multiprocessing.Queue`, whose feeder thread would make later
forks unsafe): ("end", side, lane, outcome) when a side or a lane ends (lane None for a whole
side; the outcome without its property, re-attached here: a deep formula exceeds the recursion
limit of pickle), ("fact", side, lane, fact), and ("bye", CPU time, the progress of its
Houdinis) when a worker has no live side; to a worker, ("close", side) for a side of a worker
with several, ("fact", fact) for a lane. A worker with nothing else to do is stopped by
SIGTERM, which raises SystemExit (`kind2.py`), so that its Kind 2 runs stop in their `finally`;
SIGKILL follows after GRACE seconds, and the slice of the check is stopped at its end. The
workers stopped together (the lanes of a side, all of them at a verdict) share their GRACE. A worker
dies with the coordinator (PR_SET_PDEATHSIG). A side or lane that raises, or whose worker dies
without a result, ends with status "error"; the others go on.
"""

from __future__ import annotations

import copy
import ctypes
import os
import signal
import threading
import time
from dataclasses import dataclass, field, replace
from multiprocessing import Pipe
from multiprocessing.connection import Connection, wait
from typing import Callable, Dict, FrozenSet, List, Optional, Tuple

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


def _reaped(pid: int, options: int) -> bool:
    """waitpid: whether the child `pid` has ended (and is reaped), or was reaped before."""
    try:
        return os.waitpid(pid, options)[0] == pid
    except ChildProcessError:
        return True


def merge_progress(reports: List[dict]) -> dict:
    """One progress per Houdini (`verify.houdini_progress`) from the reports of several
    workers: a finished one (proved is not None) first, else the one with more candidates
    dropped (Houdini only drops candidates)."""
    best: dict = {}
    for report in reports:
        for key, p in report.items():
            dropped, proved = p[1], p[2]
            rank = (proved is not None, len(dropped or ()))
            if key not in best or rank > best[key][0]:
                best[key] = (rank, p)
    return {k: p for k, (_, p) in best.items()}


def lane_groups(lanes: List[FrozenSet[str]], k: int) -> List[FrozenSet[str]]:
    """The task groups of a side split into k workers: its first k - 1 lanes alone, the
    others together."""
    k = max(1, min(k, len(lanes)))
    rest = frozenset().union(*lanes[k - 1:]) if lanes[k - 1:] else frozenset()
    return list(lanes[:k - 1]) + ([rest] if rest else [])


class _Board:
    """The facts sent to a lane, read from its pipe."""

    def __init__(self, conn: Connection):
        self.conn, self.facts = conn, []

    def _drain(self) -> None:
        while self.conn.poll():
            what, fact = self.conn.recv()
            if what == "fact":
                self.facts.append(fact)

    def pull(self) -> List[dict]:
        self._drain()
        out, self.facts = self.facts, []
        return out

    def waiting(self) -> bool:
        self._drain()
        return bool(self.facts)


@dataclass
class _Job:
    """What one worker runs: whole sides, or one lane (task group) of a side."""
    sides: list
    tasks: Optional[FrozenSet[str]] = None      # a lane: its tasks; None: whole sides
    lane: Optional[int] = None                  # the index of the lane in its side
    cpus: List[int] = field(default_factory=list)

    def runs_kind2(self) -> bool:
        return (self.tasks is not None and "kind2" in self.tasks) or \
            (self.tasks is None and any(getattr(s, "kind2", False) for s in self.sides))


@dataclass
class _Worker:
    pid: int
    conn: Connection
    job: _Job
    alive: bool = True
    said_bye: bool = False
    used: Optional[float] = None        # its CPU time when it was stopped
    lent: List[int] = field(default_factory=list)   # CPUs lent to it (`Coordinator._lend`)


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
    merge: Callable                     # verify._merge_lanes: {tasks: outcome} -> an Outcome
    make_lane: Callable                 # verify._Lane
    cpus: List[int] = field(default_factory=list)
    workers: List[_Worker] = field(default_factory=list)
    ids: Dict[int, object] = field(default_factory=dict)            # side id -> _Side
    where: Dict[int, List[_Worker]] = field(default_factory=dict)   # side id -> its workers
    lanes: Dict[int, Dict[int, object]] = field(default_factory=dict)   # side -> lane -> outcome
    groups: Dict[int, List[FrozenSet[str]]] = field(default_factory=dict)
    reports: List[dict] = field(default_factory=list)

    def __post_init__(self):
        self.cpus = cpu.available()[:self.cores]

    # ------------------------------------------------------------ the combiner's side

    def stop(self, side) -> None:
        """Stop a side (a side covered by a proof, or every side at a verdict)."""
        i = id(side)
        ending = []
        for w in self.where.get(i, []):
            if not w.alive:
                continue
            others = [s for s in w.job.sides if id(s) != i and s.outcome is None]
            if w.job.tasks is None and others:
                try:
                    w.conn.send(("close", i))
                except (BrokenPipeError, OSError):
                    pass
            else:
                ending.append(w)
        self._terminate_all(ending)

    # ------------------------------------------------------------ placement

    def _free(self) -> List[int]:
        used = {c for w in self.workers if w.alive for c in w.job.cpus + w.lent}
        return [c for c in self.cpus if c not in used]

    def _lend(self) -> None:
        """The free CPUs to the live workers that run Kind 2, the fewest CPUs first."""
        free = self._free()
        takers = [w for w in self.workers if w.alive and w.job.runs_kind2()]
        if not free or not takers:
            return
        changed = set()
        for c in free:
            w = min(takers, key=lambda x: len(x.job.cpus) + len(x.lent))
            w.lent.append(c)
            changed.add(id(w))
        for w in takers:
            if id(w) in changed:
                cpu.pin_tree(w.pid, w.job.cpus + w.lent)

    def _reclaim(self) -> None:
        """The CPUs lent, back from their workers."""
        for w in self.workers:
            if w.alive and w.lent:
                w.lent = []
                cpu.pin_tree(w.pid, w.job.cpus)

    def _plan(self, sides: list, n: int) -> Tuple[List[_Job], int]:
        """The jobs of `sides` on n CPUs, and the CPUs left."""
        if n <= 0 or not sides:
            return [], max(n, 0)
        if n < len(sides):
            return [_Job(sides[k::n]) for k in range(n)], 0
        k = {id(s): 1 for s in sides}
        extra, more = n - len(sides), True
        while extra > 0 and more:
            more = False
            for s in sides:
                if extra > 0 and s.make_gen is not None and k[id(s)] < len(s.lanes):
                    k[id(s)] += 1
                    extra, more = extra - 1, True
        jobs = []
        for s in sides:
            if k[id(s)] == 1:
                jobs.append(_Job([s]))
            else:
                groups = lane_groups(s.lanes, k[id(s)])
                self.groups[id(s)] = groups
                self.lanes[id(s)] = {}
                jobs += [_Job([s], g, j) for j, g in enumerate(groups)]
        return jobs, extra

    def _launch(self, jobs: List[_Job], extra: int) -> None:
        """One CPU per job; the CPUs left to the jobs that run Kind 2 (else to all)."""
        free = self._free()
        for job in jobs:
            job.cpus = [free.pop(0)] if free else list(self.cpus[:1])
        takers = [j for j in jobs if j.runs_kind2()] or jobs
        k = 0
        while free and takers and extra > 0:
            takers[k % len(takers)].cpus.append(free.pop(0))
            k, extra = k + 1, extra - 1
        for job in jobs:
            self._start(job)

    # ------------------------------------------------------------ workers

    def _start(self, job: _Job) -> None:
        """Fork a worker for `job`, pinned to its CPUs."""
        assert threading.active_count() == 1, "fork with other threads alive"
        for s in job.sides:
            self.ids[id(s)] = s
        recv, send = Pipe()
        parent = os.getpid()
        pid = os.fork()
        if pid == 0:
            try:
                recv.close()
                _die_with_parent(parent)
                os.sched_setaffinity(0, job.cpus)
                if job.tasks is None:
                    self._work(send, job.sides)
                else:
                    self._work_lane(send, job)
            finally:
                os._exit(0)
        send.close()
        w = _Worker(pid, recv, job)
        self.workers.append(w)
        for s in job.sides:
            self.where.setdefault(id(s), []).append(w)

    def _step(self, s) -> bool:
        """One round of a side; a side that raises (a bug) fails, not the check."""
        try:
            return self.step(s)
        except Exception as e:
            s.outcome = self.failed(s.prop or self.prop, "error",
                                    f"side failed: {type(e).__name__}: {e}")
            return True

    def _work(self, conn: Connection, sides: list) -> None:
        """A worker of whole sides: one round of each live side in turn."""
        live = {id(s): s for s in sides}
        for s in sides:
            s.alone = lambda: len(live) == 1
            s.publish = lambda fact, i=id(s): conn.send(("fact", i, None, fact))
        while live:
            for i, s in list(live.items()):
                while conn.poll():
                    what, j = conn.recv()
                    if what == "close" and j in live:
                        live.pop(j).gen.close()
                    elif what == "fact" and j.get("witness"):
                        # a target of the witness side: the fuzz tasks read it (`_rounds`)
                        self.context.setdefault(("witness targets", self.prop.name),
                                                []).append(j)
                if i not in live:
                    continue
                if self._step(s):
                    del live[i]
                    conn.send(("end", i, None, replace(s.outcome, prop=None)))
        conn.send(("bye", cpu.python_seconds(), self.progress(self.context)))

    def _work_lane(self, conn: Connection, job: _Job) -> None:
        """A worker of one lane of a side."""
        side = job.sides[0]
        board = _Board(conn)
        lane = self.make_lane(job.tasks, pull=board.pull, waiting=board.waiting,
                              publish=lambda fact: conn.send(("fact", id(side), job.lane,
                                                              fact)))
        s = copy.copy(side)
        s.alone = lambda: True
        s.gen = side.make_gen(lane)
        while not self._step(s):
            pass
        conn.send(("end", id(side), job.lane, replace(s.outcome, prop=None)))
        conn.send(("bye", cpu.python_seconds(), self.progress(self.context)))

    def _terminate(self, w: _Worker) -> None:
        self._terminate_all([w])

    def _terminate_all(self, ws: List[_Worker]) -> None:
        """Stop workers at once: SIGTERM to each, GRACE seconds for all of them together,
        SIGKILL to those left; reap them."""
        ws = [w for w in ws if w.alive]
        for w in ws:
            w.alive = False
            w.used = cpu.proc_seconds(w.pid)
            try:
                os.kill(w.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        left, end = list(ws), time.time() + GRACE
        while left:
            left = [w for w in left if not _reaped(w.pid, os.WNOHANG)]
            if not left or time.time() >= end:
                break
            time.sleep(0.01)
        for w in left:
            try:
                os.kill(w.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            _reaped(w.pid, 0)
        for w in ws:
            if not w.said_bye and w.used is not None:
                cpu.WORKERS += w.used
            w.conn.close()

    # ------------------------------------------------------------ outcomes

    def _side_ended(self, s, o, lane: Optional[int], comb):
        """A side, or a lane of it, ended with `o`: the verdict of the check, if any."""
        if s.outcome is not None:           # stopped meanwhile (covered, or decided)
            return None
        if lane is not None:
            outs = self.lanes[id(s)]
            outs[lane] = o
            if o.status not in ("valid", "invalid"):
                if len(outs) < len(self.groups[id(s)]):
                    return None             # its other lanes go on
                o = self.merge({self.groups[id(s)][j]: x for j, x in outs.items()})
            self.stop(s)                    # its other lanes, if any
        s.outcome = o
        return comb.ended(s)

    def _ended_worker(self, w: _Worker, comb):
        """A worker closed its pipe: reap it; its sides (or its lane) still live end with
        status "error"."""
        if not w.alive:
            return None
        w.alive = False
        try:
            _, status = os.waitpid(w.pid, 0)
        except ChildProcessError:
            status = None
        w.conn.close()
        for s in w.job.sides:
            if s.outcome is None:
                v = self._side_ended(s, self.failed(self.prop, "error", f"worker ended without"
                                                    f" a result (status {status})"),
                                     w.job.lane, comb)
                if v is not None:
                    return v
        return None

    # ------------------------------------------------------------ the driver

    def drive(self, comb) -> object:
        """The outcome of the check, as the serial driver of `comb` would give."""
        try:
            jobs, extra = self._plan(comb.live(), len(self.cpus))
            if extra > 0 and hasattr(comb, "spare_side"):
                s = comb.spare_side()
                if s is not None:
                    more, extra = self._plan([s], extra)
                    jobs += more
            self._launch(jobs, extra)
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
                    if not w.alive:
                        continue                    # stopped by an earlier message
                    try:
                        msg = conn.recv()
                    except (EOFError, OSError):
                        v = self._ended_worker(w, comb)
                        if v is not None:
                            self._terminate_all(self.workers)
                            comb.close()
                            return v
                        continue
                    if msg[0] == "end":
                        v = self._side_ended(self.ids[msg[1]],
                                             replace(msg[3], prop=self.prop), msg[2], comb)
                        if v is not None:
                            self._terminate_all(self.workers)
                            comb.close()
                            return v
                    elif msg[0] == "fact":
                        self._relay(w, msg[1], msg[3])
                    elif msg[0] == "bye":
                        w.said_bye = True
                        cpu.WORKERS += msg[1]
                        self.reports.append(msg[2])
                        self._terminate(w)
                self._more(comb)
            return comb.final() if comb.done() else self._unfinished(comb)
        finally:
            self._terminate_all(self.workers)
            self.resume(self.context, merge_progress(self.reports))

    def _relay(self, sender: _Worker, side: int, fact: dict) -> None:
        """A fact of a lane to the other lanes of its side; a target of the witness side to
        every worker that searches (and to the workers forked later, through `context`)."""
        if fact.get("witness"):
            self.context.setdefault(("witness targets", self.prop.name), []).append(fact)
            to = [w for w in self.workers if w is not sender and w.alive
                  and (w.job.tasks is None or "fuzz" in w.job.tasks)]
        else:
            to = [w for w in self.where.get(side, []) if w is not sender and w.alive
                  and w.job.tasks is not None]
        for w in to:
            try:
                w.conn.send(("fact", fact))
            except (BrokenPipeError, OSError):
                pass

    def _more(self, comb) -> None:
        """New sides on free CPUs, or on CPUs lent and taken back: the next side due
        (`next_side`), else one side with more users early (`spare_side`); the CPUs left are
        lent to the workers that run Kind 2."""
        lent = any(w.lent for w in self.workers if w.alive)
        if not self._free() and not lent:
            return
        s = comb.next_side() if hasattr(comb, "next_side") else None
        if s is None and hasattr(comb, "spare_side"):
            s = comb.spare_side()
        if s is not None:
            if lent:
                self._reclaim()
            jobs, extra = self._plan([s], len(self._free()))
            self._launch(jobs, extra)
        self._lend()

    def _unfinished(self, comb) -> object:
        """Past the deadline and its grace with sides still live (a side ends by itself at
        the deadline: this is a guard): they end without a verdict."""
        for s in comb.live():
            s.outcome = self.failed(self.prop, "unknown", "stopped after the time limit")
        return comb.final()
