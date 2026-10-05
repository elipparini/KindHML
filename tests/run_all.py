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

    rows, tally = [], {}
    for f in files:
        try:
            program, _ = V.load(f)
        except KindHMLError as e:
            print(f"{V.stem(f)}: error: {e}")
            continue
        context: dict = {}
        for rule in program.rules:
            if only and rule.name not in only:
                continue
            start = time.time()
            try:
                out = V.verify(program, rule, args.participants, args.timeout,
                               mode=args.mode, expand=expand, solver=args.solver,
                               strategy=args.strategy, context=context)
                gt, desc = out.groundtruth_check(), out.describe()
                status = out.status
            except KindHMLError as e:
                gt, desc, status = "error", f"{rule.name}: error: {e}", "error"
            wall = time.time() - start
            tally[gt] = tally.get(gt, 0) + 1
            print(f"{V.stem(f):>18} - {desc} [{wall:.1f}s]", flush=True)
            rows.append({"file": os.path.relpath(f, ROOT), "rule": rule.name, "status": status,
                         "groundtruth": rule.groundtruth, "check": gt, "wall": round(wall, 2)})
    print("summary:", ", ".join(f"{k}: {v}" for k, v in sorted(tally.items())))
    if args.csv:
        with open(args.csv, "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)


if __name__ == "__main__":
    main()
