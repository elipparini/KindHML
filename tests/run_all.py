"""Run KindHML on many verification tasks and compare with the ground truth. One Kind 2 job
at a time. A task is a rule of a contract file (an invariant of a spec included; lemmas
are not tasks).

Usage:
    .venv/bin/python tests/run_all.py [--timeout 10] [--mode inline] [--expand address,method]
                                      [selection options] [--list]
                                      [--csv results.csv] [--out DIR] [files or directories ...]

Without files, runs every task of contracts/regression and of the benchmark families. The
selection options restrict the tasks; they combine (a task must satisfy all of them):
    --families bank,vault     the directory of the file (e.g. contracts/bank)
    --versions 1,3            the version of the file: N for <name>_vN.sol, 1 for <name>.sol
    --rules Liquidity,...     the rule (property) names
    --tasks FILE.csv          the pairs (file, rule) of a CSV file, with columns file (or
                              contract) and rule (or property). The files are relative to
                              the CSV file or to the repository; an empty rule means all the
                              tasks of the file. Without files on the command line, the
                              files are those of the CSV. The results.csv of a run, or a
                              groundtruth.csv, can be given.
--list prints the selected tasks without running them.

With --out DIR, the run is saved in DIR: results.csv (one row per task), run.log (the
output of the run, with the invariants proved for each file) and info.txt (the command,
the date, the git commit and the versions of the tools).
"""

import argparse
import csv
import datetime
import glob
import os
import platform
import re
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "src"))

from kindhml import kind2                            # noqa: E402
from kindhml import verify as V                     # noqa: E402
from kindhml.errors import KindHMLError             # noqa: E402

LOG = None                                          # the log file of --out, if any


def say(line: str, screen: bool = True):
    """Print a line, and write it to the log of the run."""
    if screen:
        print(line, flush=True)
    if LOG:
        LOG.write(line + "\n")
        LOG.flush()


def command_output(cmd) -> str:
    """The first line of the output of a command."""
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT, timeout=30)
        return ((out.stdout or out.stderr).strip().splitlines() or [""])[0]
    except (OSError, subprocess.SubprocessError) as e:
        return f"unavailable ({e})"


def write_info(path: str, args):
    try:
        kind2_version = command_output([kind2.find_kind2(), "--version"])
    except FileNotFoundError:
        kind2_version = "not found"
    dirty = command_output(["git", "status", "--porcelain", "--untracked-files=no"])
    lines = [
        f"command: {' '.join(sys.argv)}",
        f"date: {datetime.datetime.now().isoformat(timespec='seconds')}",
        f"host: {platform.node()} ({platform.platform()})",
        f"git: {command_output(['git', 'rev-parse', 'HEAD'])}"
        + (" (with uncommitted changes)" if dirty else ""),
        f"python: {sys.version.split()[0]}",
        f"kind2: {kind2_version}",
        f"z3: {command_output(['z3', '--version'])}",
        f"cvc5: {command_output(['cvc5', '--version'])}",
        "options: " + ", ".join(f"{k}={v}" for k, v in sorted(vars(args).items())),
    ]
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


def files_of(paths):
    out = []
    for p in paths:
        out += sorted(glob.glob(os.path.join(p, "*.sol"))) if os.path.isdir(p) else [p]
    return out


def family(path: str) -> str:
    """The family of a contract file: the name of its directory."""
    return os.path.basename(os.path.dirname(os.path.abspath(path)))


def version(path: str) -> int:
    """The version of a contract file: N for <name>_vN.sol, 1 for <name>.sol."""
    m = re.search(r"_v(\d+)$", V.stem(path))
    return int(m.group(1)) if m else 1


def read_tasks(path: str):
    """The tasks of a CSV file, as (file, rule) pairs in order; rule None means all of them.
    The file column is `file` or `contract`, the rule column `rule` or `property`."""
    out = []
    with open(path, newline="") as f:
        reader = csv.DictReader(f)
        cols = reader.fieldnames or []
        fcol = next((c for c in ("file", "contract") if c in cols), None)
        rcol = next((c for c in ("rule", "property") if c in cols), None)
        if fcol is None:
            sys.exit(f"{path}: no column file (or contract)")
        for n, row in enumerate(reader, start=2):
            name = row[fcol].strip()
            here = [os.path.join(os.path.dirname(os.path.abspath(path)), name),
                    os.path.join(ROOT, name), name]
            found = next((c for c in here if os.path.isfile(c)), None)
            if found is None:
                sys.exit(f"{path}, line {n}: no file {name}")
            rule = (row.get(rcol) or "").strip() if rcol else ""
            out.append((os.path.realpath(found), rule or None))
    return out


def select(args):
    """The selected tasks, as (file, program, rules) per file, in order."""
    csv_tasks = read_tasks(args.tasks) if args.tasks else None
    if args.paths:
        paths = args.paths
    elif csv_tasks is not None:
        paths = [f for f, _ in csv_tasks]
    else:
        paths = [os.path.join(ROOT, "contracts", "regression"),
                 *sorted(glob.glob(os.path.join(ROOT, "contracts", "*", "")))]
    families = set(args.families.split(",")) if args.families else None
    versions = {int(v) for v in args.versions.split(",")} if args.versions else None
    names = set(args.rules.split(",")) if args.rules else None
    wanted = None                     # file -> rule names (None: all) of the CSV
    if csv_tasks is not None:
        wanted = {}
        for f, r in csv_tasks:
            if r is None or wanted.get(f, set()) is None:
                wanted[f] = None
            else:
                wanted.setdefault(f, set()).add(r)
    seen, out, matched = set(), [], set()
    for f in files_of(paths):
        real = os.path.realpath(f)
        if real in seen:
            continue
        seen.add(real)
        if families is not None and family(f) not in families:
            continue
        if versions is not None and version(f) not in versions:
            continue
        if wanted is not None and real not in wanted:
            continue
        try:
            program, _ = V.load(f, lemmas=not args.no_lemmas)
        except KindHMLError as e:
            say(f"{V.stem(f)}: error: {e}")
            continue
        rules = [r for r in V.tasks(program)
                 if (names is None or r.name in names)
                 and (wanted is None or wanted[real] is None or r.name in wanted[real])]
        matched |= {r.name for r in rules}
        if wanted is not None and wanted[real] is not None:
            for r in sorted(wanted[real] - {r.name for r in V.tasks(program)}):
                say(f"warning: {args.tasks}: {os.path.relpath(f, ROOT)} has no task {r}")
        if rules:
            out.append((f, program, rules))
    for n in sorted((names or set()) - matched):
        say(f"warning: --rules: no selected file has a task {n}")
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
    ap.add_argument("--families", default="",
                    help="comma-separated families (directories, e.g. bank,amm-real) to run")
    ap.add_argument("--versions", default="",
                    help="comma-separated versions to run (N for <name>_vN.sol, 1 for <name>.sol)")
    ap.add_argument("--tasks", default="",
                    help="a CSV file of the tasks to run (columns file and rule)")
    ap.add_argument("--list", action="store_true",
                    help="print the selected tasks, without running them")
    ap.add_argument("--strategy", default="portfolio", choices=V.STRATEGIES)
    ap.add_argument("--no_invgen", action="store_true", help="no generated invariants")
    ap.add_argument("--no_user_invariants", action="store_true",
                    help="ignore the invariants declared in the files (as candidates for"
                         " the proofs; they are still verified)")
    ap.add_argument("--no_lemmas", action="store_true",
                    help="do not load the lemmas files of the benchmark families")
    ap.add_argument("--print_invariants", action="store_true",
                    help="print the invariants proved for each file")
    ap.add_argument("--invariants_timeout", type=float, default=None,
                    help="time limit of the invariant phase of a file (default: 3 x timeout)")
    ap.add_argument("--csv", default="")
    ap.add_argument("--out", default="",
                    help="directory where the run is saved (results.csv, run.log, info.txt)")
    args = ap.parse_args()
    global LOG
    expand = () if args.expand == "none" else tuple(args.expand.split(","))
    if args.list:
        selected = select(args)
        for f, _, rules in selected:
            for r in rules:
                print(f"{os.path.relpath(f, ROOT)},{r.name},{r.groundtruth}")
        print(f"{sum(len(rs) for _, _, rs in selected)} tasks in {len(selected)} files")
        return
    if args.out:
        os.makedirs(args.out, exist_ok=True)
        write_info(os.path.join(args.out, "info.txt"), args)
        LOG = open(os.path.join(args.out, "run.log"), "w")
        args.csv = args.csv or os.path.join(args.out, "results.csv")
    selected = select(args)
    say(f"{sum(len(rs) for _, _, rs in selected)} tasks in {len(selected)} files")

    # The CSV is written row by row, so that an interrupted run keeps its partial results.
    fields = ["file", "rule", "status", "method", "groundtruth", "check", "wall"]
    out_csv = open(args.csv, "w", newline="") if args.csv else None
    writer = csv.DictWriter(out_csv, fieldnames=fields) if out_csv else None
    if writer:
        writer.writeheader()
        out_csv.flush()
    tally = {}
    for f, program, rules in selected:
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
            say(f"{V.stem(f):>18}   {V.invariant_summary(invs)} [{time.time()-start:.1f}s]")
        for rule in rules:
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
            say(f"{V.stem(f):>18} - {desc} [{wall:.1f}s]")
            if writer:
                writer.writerow({"file": os.path.relpath(f, ROOT), "rule": rule.name,
                                 "status": status, "method": method,
                                 "groundtruth": rule.groundtruth, "check": gt,
                                 "wall": round(wall, 2)})
                out_csv.flush()
        if args.print_invariants or LOG:
            # always in the log; on the screen with --print_invariants
            for line in V.invariant_report(context):
                say(f"{V.stem(f):>18}   {line}", screen=args.print_invariants)
    say("summary: " + ", ".join(f"{k}: {v}" for k, v in sorted(tally.items())))
    if out_csv:
        out_csv.close()
    if LOG:
        LOG.close()


if __name__ == "__main__":
    main()
