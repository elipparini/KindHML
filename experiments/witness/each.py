"""Milestone D: each instance (`witness.instances`) checked alone on a free state with the
smallest premise set, with a budget: status and time. Usage: each.py FILE PROPERTY [SECONDS]"""
import sys, time
sys.path.insert(0, "src")
from kindhml import verify as V, witness

path, name = sys.argv[1:3]
secs = float(sys.argv[3]) if len(sys.argv) > 3 else 2
program, _ = V.load(path)
context: dict = {}
V.prove_invariants(program, V.ANY, 300, context)
cut = V.cutoff_of(context, program, V.DEFAULT_MODE, V.DEFAULT_EXPAND, True, True)
invs = V._entry(context, program, cut.steps, V.DEFAULT_MODE, V.DEFAULT_EXPAND, True, True, True)
total = time.time()
counts: dict = {}
for text, inst in witness.instances(program, program.prop(name)):
    prem = invs.checks.premises(inst, invs.assumed())[0]
    u = max(1, invs.checks.property_count(prem, inst))
    lus, names = invs.checks_for(u).property_check(inst, prem)
    t = time.time()
    status, _, s = V._free_run(lus, names, secs)
    counts[status] = counts.get(status, 0) + 1
    print(f"{text}: u {u}, {status} {s} {time.time() - t:.1f} s", flush=True)
print(counts, f"{time.time() - total:.1f} s")
