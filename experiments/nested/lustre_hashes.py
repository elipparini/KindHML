"""Milestone B: a hash of the Lustre text of every property of the benchmark families and of the
regressions (the transition system with 2 users, and the free-state check with the declared
invariants, 2 users, with and without ghost sums), each with a time limit, to compare two
versions of the encoder. N worker processes, one task per property; the properties already in
OUT are skipped (resume). Usage: lustre_hashes.py SECONDS N OUT"""
import glob, hashlib, multiprocessing, os, signal, sys
sys.path.insert(0, "src")
from kindhml import verify as V
from kindhml.invariants import Checks


class Late(Exception):
    pass


def alarm(*_):
    raise Late()


_programs: dict = {}


def program(path):
    if path not in _programs:
        _programs[path] = V.load(path)[0]
    return _programs[path]


def task(arg):
    path, name, secs = arg
    signal.signal(signal.SIGALRM, alarm)
    signal.alarm(secs)
    try:
        p = program(path)
        prop = p.prop(name)
        invs = [r.name for r in p.properties if r.invariant]
        parts = [V.lustre_for(p, prop, 2)]
        for ghost in (False, True):
            try:
                c = Checks(p, 2, V.DEFAULT_MODE, V.DEFAULT_EXPAND, ghost_sums=ghost)
                parts.append(c.property_check(prop, invs)[0])
            except Late:
                raise
            except Exception as e:
                parts.append(f"ERROR {type(e).__name__}")
        h = hashlib.sha1("\n".join(parts).encode()).hexdigest()[:12]
    except Late:
        h = "TIMEOUT"
    except Exception as e:
        h = f"ERROR-{type(e).__name__}"
    finally:
        signal.alarm(0)
    return f"{path} {name} {h}"


if __name__ == "__main__":
    secs, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    done = set()
    if os.path.exists(out):
        done = {tuple(line.split()[:2]) for line in open(out) if len(line.split()) == 3}
    todo = []
    for path in sorted(glob.glob("contracts/*/*.sol") + glob.glob("tests/contracts/*.sol")):
        try:
            names = [r.name for r in V.load(path)[0].properties]
        except Exception as e:
            print(f"{path} LOAD-ERROR {type(e).__name__}", file=sys.stderr)
            continue
        todo += [(path, nm, secs) for nm in names if (path, nm) not in done]
    print(f"{len(done)} done, {len(todo)} to do, {n} workers", file=sys.stderr, flush=True)
    with open(out, "a") as f, multiprocessing.Pool(n, maxtasksperchild=20) as pool:
        for line in pool.imap_unordered(task, todo):
            f.write(line + "\n")
            f.flush()
