"""Run KindHML on many files and compare with the ground truth. One Kind 2 job at a time.

Usage:
    .venv/bin/python tests/run_all.py [--timeout 10] [--mode inline] [--expand address,method]
                                      [--csv results.csv] [files or directories ...]

Without files, runs contracts/regression, then the benchmarks.
"""

import argparse
import csv
import glob
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "src"))

from kindhml import verify as V                     # noqa: E402
from kindhml.errors import KindHMLError             # noqa: E402


def files_of(paths):
    out = []
    for p in paths:
        out += sorted(glob.glob(os.path.join(p, "*.sol"))) if os.path.isdir(p) else [p]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="*")
    ap.add_argument("--timeout", type=float, default=10)
    ap.add_argument("--participants", type=int, default=2)
    ap.add_argument("--mode", default=V.DEFAULT_MODE)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--expand", default=",".join(V.DEFAULT_EXPAND))
    ap.add_argument("--rules", default="", help="comma-separated rule names to run (default all)")
    ap.add_argument("--strategy", default="portfolio", choices=V.STRATEGIES)
    ap.add_argument("--no_invgen", action="store_true", help="no generated invariants")
    ap.add_argument("--no_user_invariants", action="store_true",
                    help="ignore the invariants declared in the files")
    ap.add_argument("--print_invariants", action="store_true",
                    help="print the invariants proved for each file")
    ap.add_argument("--invariants_timeout", type=float, default=None,
                    help="time limit of the invariant phase of a file (default: 3 x timeout)")
    ap.add_argument("--csv", default="")
    args = ap.parse_args()
    expand = () if args.expand == "none" else tuple(args.expand.split(","))
    paths = args.paths or [os.path.join(ROOT, "contracts", "regression"),
                           *sorted(glob.glob(os.path.join(ROOT, "contracts", "*")))]
    seen, files = set(), []
    for f in files_of(paths):
        if f not in seen:
            seen.add(f)
            files.append(f)
    only = set(args.rules.split(",")) if args.rules else None

    # The CSV is written row by row, so that an interrupted run keeps its partial results.
    fields = ["file", "rule", "status", "method", "groundtruth", "check", "wall"]
    out_csv = open(args.csv, "w", newline="") if args.csv else None
    writer = csv.DictWriter(out_csv, fieldnames=fields) if out_csv else None
    if writer:
        writer.writeheader()
        out_csv.flush()
    tally = {}
    for f in files:
        try:
            program, _ = V.load(f)
        except KindHMLError as e:
            print(f"{V.stem(f)}: error: {e}")
            continue
        context: dict = {}
        if args.strategy == "portfolio":
            # the invariant phase of the file, with its own time limit
            start = time.time()
            limit = (args.invariants_timeout if args.invariants_timeout is not None
                     else 3 * args.timeout)
            invs = V.prove_invariants(program, args.participants, limit, context,
                                      mode=args.mode, expand=expand,
                                      invgen=not args.no_invgen,
                                      user_invariants=not args.no_user_invariants)
            print(f"{V.stem(f):>18}   {V.invariant_summary(invs)} [{time.time()-start:.1f}s]",
                  flush=True)
        for rule in program.rules:
            if only and rule.name not in only:
                continue
            start = time.time()
            try:
                out = V.verify(program, rule, args.participants, args.timeout,
                               mode=args.mode, expand=expand, solver=args.solver,
                               strategy=args.strategy, context=context,
                               invgen=not args.no_invgen,
                               user_invariants=not args.no_user_invariants)
                gt, desc = out.groundtruth_check(), out.describe()
                status, method = out.status, out.method
            except KindHMLError as e:
                gt, desc, status, method = "error", f"{rule.name}: error: {e}", "error", ""
            wall = time.time() - start
            tally[gt] = tally.get(gt, 0) + 1
            print(f"{V.stem(f):>18} - {desc} [{wall:.1f}s]", flush=True)
            if writer:
                writer.writerow({"file": os.path.relpath(f, ROOT), "rule": rule.name,
                                 "status": status, "method": method,
                                 "groundtruth": rule.groundtruth, "check": gt,
                                 "wall": round(wall, 2)})
                out_csv.flush()
        if args.print_invariants:
            for line in V.invariant_report(context):
                print(f"{V.stem(f):>18}   {line}", flush=True)
    print("summary:", ", ".join(f"{k}: {v}" for k, v in sorted(tally.items())))
    if out_csv:
        out_csv.close()


if __name__ == "__main__":
    main()
