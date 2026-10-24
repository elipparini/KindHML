"""Milestone B: for every property with nested modalities (benchmark families, regressions, test
contracts), the largest next state (as a tree) that a nested modality takes as input, and the
largest last one, encoding its free-state check with U users, without binding (bounds off).
N workers, one task per (property, users); the tasks already in OUT are skipped (resume); a task
stopped at the time limit reports the sizes seen so far. Usage: sizes.py SECONDS N OUT USERS..."""
import glob, multiprocessing, os, signal, sys
os.environ["KINDHML_INLINE_BOUND"] = os.environ["KINDHML_LAST_BOUND"] = str(10 ** 12)
sys.path.insert(0, "src")
from kindhml import lustre as L, verify as V
from kindhml import encode_formula as E
from kindhml.invariants import Checks

records = []
orig = E.FormulaEncoder.trans_term


def traced(self, e, state, tx):
    r = orig(self, e, state, tx)
    records.append((E._has_modality(e.body), E.tree_size(r)))
    return r


E.FormulaEncoder.trans_term = traced


class Late(Exception):
    pass


def alarm(*_):
    raise Late()


def nested(e) -> bool:
    if isinstance(e, E.S.Modal):
        return E._has_modality(e.body)
    return any(isinstance(x, E.S.Expr) and nested(x)
               for name in getattr(e, "__dataclass_fields__", ())
               for v in [getattr(e, name)] for x in (v if isinstance(v, tuple) else (v,)))


def task(arg):
    path, name, users, secs = arg
    records.clear()
    signal.signal(signal.SIGALRM, alarm)
    signal.alarm(secs)
    try:
        p = V.load(path)[0]
        c = Checks(p, users, V.DEFAULT_MODE, V.DEFAULT_EXPAND)
        c._property(p.prop(name), L.Var("s"), True)
        note = ""
    except Late:
        note = " TIMEOUT"
    finally:
        signal.alarm(0)
    inner = max([s for m, s in records if m], default=0)
    last = max([s for m, s in records if not m], default=0)
    return f"{path} {name} {users} users: input {inner}, last {last}{note}"


if __name__ == "__main__":
    secs, n, out, users = (int(sys.argv[1]), int(sys.argv[2]), sys.argv[3],
                           [int(u) for u in sys.argv[4:]])
    done = set()
    if os.path.exists(out):
        done = {tuple(line.split()[:3]) for line in open(out) if " users:" in line}
    todo = []
    for path in sorted(glob.glob("contracts/*/*.sol") + glob.glob("tests/contracts/*.sol")
                       + glob.glob("experiments/nested/*.sol")):
        try:
            prog = V.load(path)[0]
        except Exception:
            continue
        todo += [(path, r.name, u, secs) for r in prog.properties if nested(r.formula)
                 for u in users if (path, r.name, str(u)) not in done]
    print(f"{len(todo)} tasks", file=sys.stderr, flush=True)
    with open(out, "a") as f, multiprocessing.Pool(n) as pool:
        for line in pool.imap_unordered(task, todo):
            f.write(line + "\n")
            f.flush()
