"""Milestone D: the instances of the existentials over methods of a property (`witness.py`), with
their cutoffs and whether a proof with more users gives fewer (Cor. 7.8). Pure Python.
Usage: eligible.py FILE PROPERTY"""
import sys, time
sys.path.insert(0, "src")
from kindhml import verify as V, witness
from kindhml import syntax as S
from kindhml.cutoff import OutOfFragment, Scanner
from kindhml.invariants import Checks
from kindhml.model import System

path, name = sys.argv[1:3]
t = time.time()
program, _ = V.load(path)
prop = program.prop(name)
templates = V.invariant_templates(program)
ext = S.Program(program.contracts, V._with_candidates(program, True) + tuple(templates),
                program.balance_type)
checks = Checks(ext, 1, V.DEFAULT_MODE, V.DEFAULT_EXPAND, ghost_sums=True)
insts = witness.instances(program, prop)
cut = checks.cutoff([prop] + [i for _, i in insts])
print(path, name, "steps", cut.steps, "cutoff", cut.of_property(name), cut.outside.get(name))
eligible = 0
for text, inst in insts:
    try:
        down = Scanner(System.make(program, 1)).idle_needed(inst.formula) == 0
    except OutOfFragment:
        down = None
    c = cut.of_property(inst.name)
    eligible += bool(down and c is not None)
    print(f"  {text}: cutoff {c}, downward {down}" + (f" ({cut.outside.get(inst.name)})" if c is None else ""))
print(f"{eligible} of {len(insts)} eligible; {time.time() - t:.1f} s")
