"""Milestone D: the witness side alone on a property (`verify._witness_rounds`), with the time of
each round and the statuses of the instances in each Kind 2 run. Usage: debug.py FILE PROPERTY"""
import sys, time
sys.path.insert(0, "src")
from kindhml import kind2, verify as V

path, name = sys.argv[1:3]
program, _ = V.load(path)
prop = program.prop(name)
context: dict = {}
t = time.time()
V.prove_invariants(program, V.ANY, 120, context)
print(f"invariants: {time.time() - t:.1f} s", flush=True)
run = kind2.run


def logged(lustre, timeout, **kw):
    t0 = time.time()
    out = run(lustre, timeout, **kw)
    st = {}
    for p in out.properties:
        st[p.status] = st.get(p.status, 0) + 1
    print(f"  kind2 {kw.get('solver')} budget {timeout:.1f}: {time.time() - t0:.1f} s, {st},"
          f" errors {out.errors[:1]}", flush=True)
    return out


kind2.run = logged
start = time.time()
gen = V._witness_rounds(program, prop, context, V.DEFAULT_MODE, V.DEFAULT_EXPAND, True, True,
                        start, start + 300)
try:
    while True:
        next(gen)
        print(f"round at {time.time() - start:.1f} s", flush=True)
except StopIteration as e:
    print(e.value.describe(), f"{time.time() - start:.1f} s")
