"""Milestone D: the checks on a free state of one instance (`witness.instances`), for each premise
set and form (one property, split into cases), with their cutoffs and times.
Usage: forms.py FILE PROPERTY INSTANCE [SECONDS]"""
import sys, time
sys.path.insert(0, "src")
from kindhml import verify as V, witness

path, name, text = sys.argv[1:4]
secs = float(sys.argv[4]) if len(sys.argv) > 4 else 30
program, _ = V.load(path)
context: dict = {}
V.prove_invariants(program, V.ANY, 300, context)
cut = V.cutoff_of(context, program, V.DEFAULT_MODE, V.DEFAULT_EXPAND, True, True)
invs = V._entry(context, program, cut.steps, V.DEFAULT_MODE, V.DEFAULT_EXPAND, True, True, True)
print("c_H", cut.steps, "users", invs.users, "proved", invs.proved is not None)
inst = dict(witness.instances(program, program.prop(name)))[text]
premises = invs.checks.premises(inst, invs.assumed())
for i, prem in enumerate(premises):
    u = max(1, invs.checks.property_count(prem, inst))
    for split in (False, True):
        lus, names = invs.checks_for(u).property_check(inst, prem, split)
        t = time.time()
        status, refuted, s = V._free_run(lus, names, secs)
        print(f"premises {i} ({len(prem)}), u {u}, split {split}, {len(names)} properties:"
              f" {status} {s} {time.time() - t:.1f} s", flush=True)
