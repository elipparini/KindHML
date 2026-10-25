"""Run KindHML on many verification tasks and compare with the ground truth. One Kind 2 job
at a time. A task is a property of a contract file (an invariant of a spec included; lemmas
are not tasks).

Usage:
    .venv/bin/python tests/run_all.py [--timeout 10] [--mode inline] [--expand address,method]
                                      [selection options] [--list]
                                      [--csv results.csv] [--out DIR] [files or directories ...]

Without files, runs every task of contracts/regression and of the benchmark families. The
selection options restrict the tasks; they combine (a task must satisfy all of them):
    --families bank,vault     the directory of the file (e.g. contracts/bank); the families
                              run in the order given
    --versions 1,3            the version of the file: N for <name>_vN.sol, 1 for <name>.sol
    --properties Liquidity,...  the property names
    --tasks FILE.csv          the pairs (file, property) of a CSV file, with columns file (or
                              contract) and property. The files are relative to
                              the CSV file or to the repository; an empty property means all the
                              tasks of the file. Without files on the command line, the
                              files are those of the CSV. The results.csv of a run, or a
                              groundtruth.csv, can be given.
--list prints the selected tasks without running them.

Each task runs in a child process, stopped at the hard limit --task_timeout (default
2 x timeout + TASK_MARGIN seconds), with the Kind 2 runs it started: the time limit of a
check is only checked between its steps, and a step can take hours (the encoding of a
property with nested modalities).

With --out DIR, the run is saved in DIR: results.csv (one row per task), run.log (the
output of the run, with the invariants proved for each file) and info.txt (the command,
the date, the git commit and the versions of the tools).
"""

import argparse
import csv
import datetime
import glob
import multiprocessing
import os
import platform
import re
import signal
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "src"))

from kindhml import kind2                            # noqa: E402
from kindhml import smt_trace                        # noqa: E402
from kindhml import verify as V                     # noqa: E402
from kindhml.colors import PLAIN, palette           # noqa: E402
from kindhml.errors import KindHMLError             # noqa: E402

LOG = None                                          # the log file of --out, if any
C = PLAIN                                           # the colors on the screen (--color)

# The checks run past their time limit (the last Kind 2 run, the confirmation of a
# counterexample): by at most 77 s with 600 s in the cluster runs of 2026-10-21 and 22, by
# 147 s with 60 s for lending_simple_real Liquidation_attack_any.
TASK_MARGIN = 300
STOP_GRACE = 30             # seconds for a task to stop, and stop Kind 2, after SIGTERM


def say(line: str, screen: bool = True, colored: str = ""):
    """Print a line (`colored`, if given, on the screen), and write it to the log of the run."""
    if screen:
        print(colored or line, flush=True)
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
    """The tasks of a CSV file, as (file, property) pairs in order; property None means all of
    them. The file column is `file` or `contract`, the property column `property`."""
    out = []
    with open(path, newline="") as f:
        reader = csv.DictReader(f)
        cols = reader.fieldnames or []
        fcol = next((c for c in ("file", "contract") if c in cols), None)
        rcol = next((c for c in ("property",) if c in cols), None)
        if fcol is None:
            sys.exit(f"{path}: no column file (or contract)")
        for n, row in enumerate(reader, start=2):
            name = row[fcol].strip()
            here = [os.path.join(os.path.dirname(os.path.abspath(path)), name),
                    os.path.join(ROOT, name), name]
            found = next((c for c in here if os.path.isfile(c)), None)
            if found is None:
                sys.exit(f"{path}, line {n}: no file {name}")
            prop = (row.get(rcol) or "").strip() if rcol else ""
            out.append((os.path.realpath(found), prop or None))
    return out


def select(args):
    """The selected tasks, as (file, program, properties) per file, in order."""
    csv_tasks = read_tasks(args.tasks) if args.tasks else None
    if args.paths:
        paths = args.paths
    elif csv_tasks is not None:
        paths = [f for f, _ in csv_tasks]
    else:
        paths = [os.path.join(ROOT, "contracts", "regression"),
                 *sorted(glob.glob(os.path.join(ROOT, "contracts", "*", "")))]
    families = args.families.split(",") if args.families else None
    versions = {int(v) for v in args.versions.split(",")} if args.versions else None
    names = set(args.properties.split(",")) if args.properties else None
    wanted = None                     # file -> property names (None: all) of the CSV
    if csv_tasks is not None:
        wanted = {}
        for f, r in csv_tasks:
            if r is None or wanted.get(f, set()) is None:
                wanted[f] = None
            else:
                wanted.setdefault(f, set()).add(r)
    files = files_of(paths)
    if families is not None:
        known = {family(f) for f in files}
        unknown = [x for x in families if x not in known]
        if unknown:
            sys.exit(f"--families: no selected file is in {', '.join(unknown)}"
                     f" (families: {', '.join(sorted(known))})")
    if families is not None:          # the order of --families; stable within a family
        rank = {name: i for i, name in reversed(list(enumerate(families)))}
        files = sorted((f for f in files if family(f) in rank), key=lambda f: rank[family(f)])
    seen, out, matched = set(), [], set()
    for f in files:
        real = os.path.realpath(f)
        if real in seen:
            continue
        seen.add(real)
        if versions is not None and version(f) not in versions:
            continue
        if wanted is not None and real not in wanted:
            continue
        try:
            program, _ = V.load(f, lemmas=not args.no_lemmas)
        except KindHMLError as e:
            say(f"{V.stem(f)}: error: {e}")
            continue
        properties = [r for r in V.tasks(program)
                 if (names is None or r.name in names)
                 and (wanted is None or wanted[real] is None or r.name in wanted[real])]
        matched |= {r.name for r in properties}
        if wanted is not None and wanted[real] is not None:
            for r in sorted(wanted[real] - {r.name for r in V.tasks(program)}):
                say(f"warning: {args.tasks}: {os.path.relpath(f, ROOT)} has no task {r}")
        if properties:
            out.append((f, program, properties))
    for n in sorted((names or set()) - matched):
        say(f"warning: --properties: no selected file has a task {n}")
    return out


def isolated(work, limit: float) -> tuple:
    """work() in a child process (a fork, which shares the state of this one), within `limit`
    seconds (0: no limit): ("done", its value), ("failed", the error), or ("stopped", None) if
    it was stopped at the limit."""
    recv, send = multiprocessing.Pipe(duplex=False)
    pid = os.fork()
    if pid == 0:
        # the child never returns: SIGTERM raises SystemExit (`kind2.py`), even in the inner
        # `finally`, and only one is sent
        try:
            try:
                recv.close()
                try:
                    result = ("done", work())
                except Exception as e:
                    result = ("failed", f"{type(e).__name__}: {e}")
                send.send(result)
            finally:
                os._exit(0)
        finally:
            os._exit(1)
    send.close()
    ended = False                       # the child ends by itself
    try:
        if not recv.poll(limit or None):
            return "stopped", None
        ended = True
        try:
            return recv.recv()
        except EOFError:
            return "failed", "the process of the task ended without a result"
    finally:
        if ended:
            os.waitpid(pid, 0)
        else:
            stop(pid)


def stop(pid: int):
    """Stop the child process `pid`: SIGTERM, on which `kind2.run` stops Kind 2; after
    STOP_GRACE seconds, SIGKILL, for it and its Kind 2 runs."""
    try:
        os.kill(pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    end = time.time() + STOP_GRACE
    while time.time() < end:
        if os.waitpid(pid, os.WNOHANG)[0] == pid:
            kind2.kill_runs(pid, alive=False)
            return
        time.sleep(0.1)
    kind2.kill_runs(pid, alive=True)
    os.kill(pid, signal.SIGKILL)
    os.waitpid(pid, 0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="*")
    ap.add_argument("--timeout", type=float, default=10)
    ap.add_argument("--task_timeout", type=float, default=None,
                    help="hard limit of a task (s), at which its process is stopped (default:"
                         f" 2 x timeout + {TASK_MARGIN}; 0: no limit)")
    ap.add_argument("--participants", type=V.parse_users, default=None,
                    help=f"number of users, or {V.ANY} (every number of users; the default)")
    ap.add_argument("--users_mode", choices=V.USERS_MODES, default=None,
                    help="combined (default): the checks with the cutoff of the checks on free"
                         " values, if it is at most --participants, and with --participants"
                         " users, in turn; exact: --participants users only; parameterized:"
                         " the cutoff only (DESIGN.md, Sect. 7)")
    ap.add_argument("--parameterized", dest="users_mode", action="store_const",
                    const="parameterized", help="the same as --users_mode parameterized")
    ap.add_argument("--mode", default=V.DEFAULT_MODE)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--expand", default=",".join(V.DEFAULT_EXPAND))
    ap.add_argument("--properties", default="",
                    help="comma-separated property names to run (default all)")
    ap.add_argument("--families", default="",
                    help="comma-separated families (directories, e.g. bank,amm-real) to run,"
                         " in this order")
    ap.add_argument("--versions", default="",
                    help="comma-separated versions to run (N for <name>_vN.sol, 1 for <name>.sol)")
    ap.add_argument("--tasks", default="",
                    help="a CSV file of the tasks to run (columns file and property)")
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
    ap.add_argument("--color", choices=("auto", "always", "never"), default="auto",
                    help="colors on the screen (default: auto, on a terminal unless"
                         " $NO_COLOR is set); the log is never colored")
    ap.add_argument("--csv", default="")
    ap.add_argument("--out", default="",
                    help="directory where the run is saved (results.csv, run.log, info.txt)")
    ap.add_argument("--smt_trace", default="", metavar="DIR",
                    help="save the SMT-LIB instances of the solver calls into DIR (incremental "
                         "Kind 2 traces and standalone scripts, one per check-sat; "
                         "src/kindhml/smt_trace.py)")
    ap.add_argument("--smt_trace_logics", default="", metavar="L1,L2,...",
                    help="with --smt_trace, keep only the instances in these logics, e.g. "
                         "QF_NIA,NIA (default: all)")
    args = ap.parse_args()
    if args.task_timeout is None:
        args.task_timeout = 2 * args.timeout + TASK_MARGIN if args.timeout else 0
    args.users_mode = V.users_mode_of(args.users_mode)
    if args.participants is None:
        if args.strategy == "kind2" or args.users_mode == "parameterized":
            ap.error("--strategy kind2 and --users_mode parameterized need --participants N")
        args.participants = V.ANY
    if args.participants == V.ANY and (args.strategy == "kind2"
                                       or args.users_mode == "parameterized"):
        ap.error(f"{V.ANY} needs --strategy portfolio and --users_mode combined or exact")
    global LOG, C
    C = palette(args.color)
    expand = () if args.expand == "none" else tuple(args.expand.split(","))
    if args.list:
        selected = select(args)
        for f, _, properties in selected:
            for r in properties:
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
    if args.smt_trace_logics and not args.smt_trace:
        ap.error("--smt_trace_logics needs --smt_trace")
    smt_trace.configure(os.path.abspath(args.smt_trace) if args.smt_trace else None,
                        args.smt_trace_logics or None)

    # The CSV is written row by row, so that an interrupted run keeps its partial results.
    fields = ["file", "property", "status", "method", "groundtruth", "check", "wall", "scope"]
    out_csv = open(args.csv, "w", newline="") if args.csv else None
    writer = csv.DictWriter(out_csv, fieldnames=fields) if out_csv else None
    if writer:
        writer.writeheader()
        out_csv.flush()
    tally = {}
    for f, program, properties in selected:
        context: dict = {}
        smt_trace.start_task(f, "invariants")
        if args.strategy == "portfolio":
            # the invariant phase of the file, with its own time limit
            start = time.time()
            limit = (args.invariants_timeout if args.invariants_timeout is not None
                     else 3 * args.timeout)
            entries = V.prove_invariants(program, args.participants, limit, context,
                                         mode=args.mode, expand=expand,
                                         invgen=not args.no_invgen,
                                         user_invariants=not args.no_user_invariants,
                                         users_mode=args.users_mode)
            elapsed = f"[{time.time()-start:.1f}s]"
            for invs in entries:
                head = f"({V.invariant_label(invs)}) " if len(entries) > 1 else ""
                say(f"{V.stem(f):>18}   {head}{V.invariant_summary(invs)} {elapsed}",
                    colored=f"{V.stem(f):>18}   {head}{V.invariant_summary(invs, C)}"
                            f" {C.dim(elapsed)}")
        for prop in properties:
            start = time.time()

            def check(prop=prop):
                """The task, in a child process: its outcome, and the progress of Houdini,
                which the next tasks continue."""
                smt_trace.start_task(f, prop.name)
                try:
                    out = V.verify(program, prop, args.participants, args.timeout,
                                   mode=args.mode, expand=expand, solver=args.solver,
                                   strategy=args.strategy, context=context,
                                   invgen=not args.no_invgen,
                                   user_invariants=not args.no_user_invariants,
                                   users_mode=args.users_mode)
                    found = (out.groundtruth_check(), out.describe(), out.describe(C),
                             out.status, out.method, out.scope)
                except KindHMLError as e:
                    found = ("error", f"{prop.name}: error: {e}",
                             f"{C.bold(prop.name)}: {C.magenta('error:')} {e}", "error", "", "")
                return found, V.houdini_progress(context)

            how, value = isolated(check, args.task_timeout)
            if how == "done":
                (gt, desc, colored, status, method, scope), progress = value
                V.resume_houdini(context, progress)
            else:
                why = (f"stopped at the limit of the task ({args.task_timeout:g} s)"
                       if how == "stopped" else f"the task failed: {value}")
                gt, status, method, scope = ("unknown" if how == "stopped" else "error",
                                             "unknown" if how == "stopped" else "error",
                                             "", why)
                desc = f"{prop.name}: {status} ({why})"
                colored = f"{C.bold(prop.name)}: {C.magenta(status)} ({why})"
            wall = time.time() - start
            tally[gt] = tally.get(gt, 0) + 1
            say(f"{V.stem(f):>18} - {desc} [{wall:.1f}s]",
                colored=f"{V.stem(f):>18} - {colored} {C.dim(f'[{wall:.1f}s]')}")
            if writer:
                writer.writerow({"file": os.path.relpath(f, ROOT), "property": prop.name,
                                 "status": status, "method": method,
                                 "groundtruth": prop.groundtruth, "check": gt,
                                 "wall": round(wall, 2), "scope": scope})
                out_csv.flush()
        if args.print_invariants or LOG:
            # always in the log; on the screen with --print_invariants
            for line in V.invariant_report(context):
                say(f"{V.stem(f):>18}   {line}", screen=args.print_invariants)
    say("summary: " + ", ".join(f"{k}: {v}" for k, v in sorted(tally.items())),
        colored="summary: " + ", ".join(f"{C.groundtruth(k)}: {v}"
                                        for k, v in sorted(tally.items())))
    if out_csv:
        out_csv.close()
    if LOG:
        LOG.close()


if __name__ == "__main__":
    main()
