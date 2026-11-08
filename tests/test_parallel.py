"""The parallel driver of the sides (`parallel.py`), with scripted sides in worker processes
(no Kind 2), and what a forked worker relies on: z3 timeouts and SIGALRM after a fork."""

import os
import signal
import time

import pytest

from kindhml import fuzz
from kindhml import parallel
from kindhml import verify as V
from test_users_modes import PROGRAM, UNIVERSAL, outcome

FAR = time.time() + 3600                # a deadline that does not pass in a test


def slow(rounds: int, o, delay: float = 0.05, fail=None):
    """A side that ends with `o` after `rounds` rounds of `delay` seconds; `fail`: "raise"
    or "exit" at its last round."""
    for _ in range(rounds):
        time.sleep(delay)
        yield
    if fail == "raise":
        raise RuntimeError("a bug")
    if fail == "exit":
        os._exit(3)
    return o


def coordinator(cores: int = 4, deadline=FAR) -> parallel.Coordinator:
    return parallel.Coordinator(cores, deadline, UNIVERSAL, {}, V._step, V.houdini_progress,
                                V.resume_houdini, V._failed, V._merge_lanes, V._Lane)


def any_mode(script, c, cores=4, wit=None):
    """`_AnyCombiner` driven in parallel; script: (users, ghost) -> (rounds, outcome[, fail])."""
    coord = coordinator(cores)
    made = []

    def side(users, ghost, goal, cut, **flags):
        rounds, o, *fail = script.get((users, ghost), (1000, outcome("unknown")))
        made.append((users, ghost))
        s = V._Side(users, ghost, goal, **flags)
        s.prop = UNIVERSAL
        s.gen = slow(rounds, o, fail=fail[0] if fail else None)
        return s

    comb = V._AnyCombiner(PROGRAM, UNIVERSAL, None, c, side, FAR, wit, stop=coord.stop)
    return coord.drive(comb), made, coord


def gone(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return True
    return False


def test_a_proof_for_every_n():
    script = {(3, True): (2, outcome("valid", "invariants", 3)),
              (1, False): (1, outcome("valid", "invariants")),
              (2, False): (3, outcome("valid", "invariants"))}
    o, _, coord = any_mode(script, 3)
    assert o.status == "valid", o.describe()
    assert o.scope.startswith("n >= 3 by invariants") and o.prop is UNIVERSAL
    assert all(gone(w.pid) for w in coord.workers)


def test_the_first_counterexample_wins_and_the_others_stop():
    script = {(3, True): (1000, outcome("unknown")),
              (2, False): (2, outcome("invalid", "fuzz"))}
    start = time.time()
    o, _, coord = any_mode(script, 3)
    assert (o.status, o.scope) == ("invalid", "counterexample with 2 users")
    assert time.time() - start < 10
    assert all(gone(w.pid) for w in coord.workers)


def test_a_failing_side_is_an_error_and_the_others_go_on():
    script = {(1, False): (1, outcome("unknown"), "raise"),
              (2, False): (1, outcome("unknown"), "exit"),
              (3, True): (3, outcome("valid", "invariants", 1))}
    o, _, coord = any_mode(script, 3)
    assert o.status == "valid", o.describe()        # P proves every n >= 1
    # combined mode: without a verdict, the outcome of the exact side, here its error
    coord = coordinator(2)
    param, exact = V._Side(2, True, 5), V._Side(5, False, 5)
    param.prop = exact.prop = UNIVERSAL
    param.gen = slow(3, outcome("unknown"))
    exact.gen = slow(1, outcome("unknown"), fail="raise")
    o = coord.drive(V._CombinedCombiner(param, exact, "", stop=coord.stop))
    assert o.status == "error" and "side failed: RuntimeError: a bug" in o.errors[0]


def test_free_cpus_start_a_side_with_more_users():
    """Without a cutoff: the side with 1 user, and, on a free CPU, the one with 2 users,
    which finds the counterexample while the first side is still running."""
    script = {(1, False): (1000, outcome("unknown")),
              (2, False): (2, outcome("invalid", "fuzz"))}
    o, made, _ = any_mode(script, None, cores=2)
    assert (o.status, o.scope) == ("invalid", "counterexample with 2 users")
    assert made == [(1, False), (2, False)]


def test_the_workers_die_with_the_coordinator():
    recv, send = os.pipe()
    pid = os.fork()
    if pid == 0:
        try:
            coord = coordinator(2)
            orig = coord._start

            def start(job):
                orig(job)
                os.write(send, f"{coord.workers[-1].pid}\n".encode())
            coord._start = start
            comb = V._AnyCombiner(PROGRAM, UNIVERSAL, None, None, lambda *a, **k: _forever(),
                                  FAR, None, stop=coord.stop)
            coord.drive(comb)
        finally:
            os._exit(0)
    os.close(send)
    time.sleep(1.0)
    pids = [int(x) for x in os.read(recv, 1000).split()]
    os.kill(pid, signal.SIGKILL)
    os.waitpid(pid, 0)
    assert pids
    for _ in range(50):
        if all(gone(p) for p in pids):
            break
        time.sleep(0.1)
    assert all(gone(p) for p in pids)


def _forever():
    s = V._Side(1, False, None)
    s.prop = UNIVERSAL
    s.gen = slow(100000, outcome("unknown"), delay=0.1)
    return s


def test_the_progress_of_houdini_from_several_workers():
    a = (["x", "y"], ["z"], None, 2, None, False)
    b = (["x"], ["y", "z"], None, 2, None, False)
    done = (["x"], ["y", "z"], ["x"], 2, None, True)
    assert parallel.merge_progress([{"k": a}, {"k": b}]) == {"k": b}
    assert parallel.merge_progress([{"k": done}, {"k": a}]) == {"k": done}


def test_z3_timeouts_after_a_fork():
    """The completion runs z3 in its process (`extend.py`) with a timeout; a worker is forked
    from a process that may have used z3 with a timeout before."""
    import z3

    def hard(seconds):
        x, y, z_ = z3.Ints("x y z")
        s = z3.Solver()
        s.set("timeout", int(seconds * 1000))
        s.add(x * x * x + y * y * y == z_ * z_ * z_ + 3, x > 1000, y > 1000)
        return s.check()

    hard(0.2)
    pid = os.fork()
    if pid == 0:
        try:
            start = time.time()
            hard(1.0)
            os._exit(0 if time.time() - start < 3 else 1)
        finally:
            os._exit(2)
    deadline = time.time() + 30
    while time.time() < deadline:
        done, status = os.waitpid(pid, os.WNOHANG)
        if done == pid:
            assert os.WEXITSTATUS(status) == 0
            return
        time.sleep(0.1)
    os.kill(pid, signal.SIGKILL)
    os.waitpid(pid, 0)
    pytest.fail("z3 did not stop at its timeout in a forked process")


def test_sigalrm_in_a_forked_worker():
    """The bounded evaluation of the fuzzer stops a slow evaluation with SIGALRM."""
    pid = os.fork()
    if pid == 0:
        try:
            signal.signal(signal.SIGALRM, fuzz._alarm)
            signal.setitimer(signal.ITIMER_REAL, 0.2)
            try:
                while True:
                    pass
            except fuzz._TooSlow:
                os._exit(0)
        finally:
            os._exit(1)
    _, status = os.waitpid(pid, 0)
    assert os.WEXITSTATUS(status) == 0


# ------------------------------------------------------------------ lanes

K, P, F, E = frozenset({"kind2"}), V.PROOF_LANE, frozenset({"fuzz"}), frozenset({"extend"})


def test_lane_groups():
    """Kind 2 is split off first, then the proofs, then the fuzzer."""
    assert parallel.lane_groups([K, P, F, E], 1) == [K | P | F | E]
    assert parallel.lane_groups([K, P, F, E], 2) == [K, P | F | E]
    assert parallel.lane_groups([K, P, F, E], 3) == [K, P, F | E]
    assert parallel.lane_groups([K, P, F, E], 9) == [K, P, F, E]
    assert parallel.lane_groups([P, F], 2) == [P, F]


def lane_side(script):
    """A side whose lanes run script(tasks, lane), a generator."""
    s = V._Side(1, False, None)
    s.prop = UNIVERSAL
    s.lanes = [K, P, F, E]
    s.make_gen = lambda lane=None: script(lane.tasks if lane else None, lane)
    s.gen = s.make_gen()
    return s


def test_the_fuzzer_lane_gets_the_counterexample_to_induction_of_the_proof_lane():
    def script(tasks, lane):
        if tasks == P:
            yield
            lane.publish({"target_users": 1, "guide": {("C", "x"): 3}, "inputs": {},
                          "cti": "x = 3", "direct": False})
            return outcome("unknown")
        if tasks == F:
            while True:
                if any(f.get("guide") for f in lane.pull()):
                    return outcome("invalid", "fuzz")
                time.sleep(0.05)
                yield
        while True:                     # Kind 2 and the completion: no verdict
            time.sleep(0.05)
            yield

    coord = coordinator(4)
    o = coord.drive(V._OneCombiner(lane_side(script), coord.stop))
    assert (o.status, o.method) == ("invalid", "fuzz")
    assert len(coord.workers) == 4 and all(gone(w.pid) for w in coord.workers)


def test_lanes_without_a_verdict_merge():
    """The outcome of Kind 2's lane (its proofs with fewer users), with the counterexample to
    induction of the proof lane."""
    def script(tasks, lane):
        yield
        o = outcome("unknown")
        if tasks == K:
            o.true_for = "up to 2 users"
        if tasks == P:
            o.cti = "x = 3"
        return o

    coord = coordinator(4)
    o = coord.drive(V._OneCombiner(lane_side(script), coord.stop))
    assert (o.status, o.true_for, o.cti) == ("unknown", "up to 2 users", "x = 3")


def test_the_merge_of_lanes():
    k, p, f = outcome("unknown"), outcome("unknown"), outcome("error")
    p.cti, f.errors = "x = 3", ["side failed: RuntimeError: a bug"]
    k.memory_killed = False
    f.memory_killed = True
    o = V._merge_lanes({K: k, P: p, F: f})
    assert o.cti == "x = 3" and o.memory_killed and o.status == "unknown"
    assert o.errors == ["side failed: RuntimeError: a bug"]


def test_a_target_of_the_witness_side_reaches_the_fuzzer_of_another_side():
    """The witness side publishes a state where no call defends; the fuzzer lane of the
    exact side with 1 user receives it and finds a counterexample with 2 users, whose scope
    says so."""
    def wit_gen(s):
        yield
        s.publish({"target_users": 2, "guide": {("C", "x"): 1}, "inputs": {}, "cti": "x = 1",
                   "direct": False, "witness": True})
        while True:
            time.sleep(0.05)
            yield

    def script(tasks, lane):
        if tasks is not None and "fuzz" in tasks:
            while True:
                if any(f.get("witness") for f in lane.pull()):
                    o = outcome("invalid", "fuzz")
                    o.users = 2
                    return o
                time.sleep(0.05)
                yield
        while True:
            time.sleep(0.05)
            yield

    def side(users, ghost, goal, cut, **flags):
        s = lane_side(script)
        s.users, s.ghost, s.goal = users, ghost, goal
        return s

    wit = V._Side(1, True, None, kind2=False, search=False)
    wit.prop = UNIVERSAL
    wit.gen = wit_gen(wit)
    coord = coordinator(4)
    o = coord.drive(V._AnyCombiner(PROGRAM, UNIVERSAL, None, None, side, FAR, wit,
                                   stop=coord.stop))
    assert (o.status, o.scope) == ("invalid", "counterexample with 2 users")
    assert coord.context[("witness targets", UNIVERSAL.name)][0]["cti"] == "x = 1"


# ------------------------------------------------------------------ stopping workers

def test_sigterm_during_a_finalizer():
    """SIGTERM handled during a finalizer (as the `__del__` of a z3 object) raises a SystemExit
    that Python discards: the process stops anyway, once the finalizer has returned (before:
    it went on until SIGKILL). The hooks are set in the child, as at the import of `kind2`
    outside pytest (which replaces `sys.unraisablehook` during a test)."""
    import sys
    from kindhml import kind2
    recv, send = os.pipe()
    pid = os.fork()
    if pid == 0:
        try:
            signal.signal(signal.SIGTERM, kind2._exit_on_sigterm)
            sys.unraisablehook = kind2._unraisable

            class Slow:
                def __del__(self):
                    os.write(send, b"x")
                    end = time.time() + 1.0
                    while time.time() < end:
                        pass

            x = Slow()
            del x                       # the finalizer runs here; SIGTERM arrives in it
            end = time.time() + 30
            while time.time() < end:
                pass
            os._exit(0)                 # not stopped
        finally:
            os._exit(1)                 # stopped by the SystemExit of SIGTERM
    os.close(send)
    assert os.read(recv, 1) == b"x"
    start = time.time()
    os.kill(pid, signal.SIGTERM)
    _, status = os.waitpid(pid, 0)
    assert time.time() - start < 5
    assert os.WEXITSTATUS(status) == 1


def test_workers_stopped_together_share_their_grace(monkeypatch):
    """Workers that ignore SIGTERM are killed after one GRACE for all of them, not one each."""
    monkeypatch.setattr(parallel, "GRACE", 0.5)
    coord = coordinator(4)
    ws = []
    for _ in range(3):
        recv, send = parallel.Pipe()
        pid = os.fork()
        if pid == 0:
            try:
                signal.signal(signal.SIGTERM, signal.SIG_IGN)
                time.sleep(60)
            finally:
                os._exit(0)
        send.close()
        ws.append(parallel._Worker(pid, recv, parallel._Job([])))
    time.sleep(0.2)
    start = time.time()
    coord._terminate_all(ws)
    assert time.time() - start < 1.2
    assert all(gone(w.pid) and not w.alive for w in ws)
