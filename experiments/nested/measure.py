"""Milestone B, step 1: the size (as a tree: what the Lustre text contains) and the time of the
next-state terms of the modalities, encoding the free-state check (Checks._property) of the
properties given, each with a time limit. Usage: measure.py FILE USERS SECONDS PROP..."""
import signal, sys, time
sys.path.insert(0, "src")
from kindhml import lustre as L, verify as V
from kindhml.encode_formula import FormulaEncoder
from kindhml.invariants import Checks

path, users, secs, names = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4:]


def tree_size(e, memo):
    k = id(e)
    if k not in memo:
        n = 1
        for name in getattr(e, "__dataclass_fields__", ()):
            v = getattr(e, name)
            for x in (v if isinstance(v, tuple) else (v,)):
                if isinstance(x, tuple):
                    x = x[-1]
                if isinstance(x, L.LExpr):
                    n += tree_size(x, memo)
        memo[k] = n
    return memo[k]


log = []
orig = FormulaEncoder.trans_term


def traced(self, e, state, tx):
    t0 = time.time()
    r = orig(self, e, state, tx)
    log.append((tree_size(state, {}), tree_size(r, {}), time.time() - t0))
    return r


FormulaEncoder.trans_term = traced


class Late(Exception):
    pass


def alarm(*_):
    raise Late()


signal.signal(signal.SIGALRM, alarm)
program, _ = V.load(path, lemmas=False)
for name in names:
    log.clear()
    c = Checks(program, users, "inline", ("address", "method"))
    t0 = time.time()
    signal.alarm(secs)
    try:
        e = c._property(program.prop(name), L.Var("s"), True)
        signal.alarm(0)
        res = f"{time.time() - t0:.1f}s, property tree {tree_size(e, {})}"
    except Late:
        res = f"> {secs}s"
    biggest = sorted(log, key=lambda x: -x[1])[:3]
    print(f"{name} {users} users: {res}; {len(log)} trans_term, total {sum(x[2] for x in log):.1f}s;"
          f" largest (state, next, s): {[(s, n, round(t, 2)) for s, n, t in biggest]}", flush=True)
