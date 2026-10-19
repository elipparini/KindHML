"""KindHML: verification of CHML properties of contracts with Kind 2.

Usage:
    python3 src/kindHML.py <contract.sol> <Property|ALL> <n_participants|any> <timeout> [--only_lus]

For each property, the Lustre encoding is saved in
out_lus/<contract>_<Property>_<n>_<timeout>.lus and the verdict in
out_results/<contract>_<Property>_<n>_<timeout>.out.
"""

import argparse
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from kindhml import verify as V                     # noqa: E402
from kindhml.colors import palette                  # noqa: E402
from kindhml.encode_formula import METHOD_COPIES, MODES, parse_expand   # noqa: E402
from kindhml.errors import KindHMLError             # noqa: E402
from kindhml.kind2 import SOLVERS, format_counterexample   # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description="Verify CHML properties of a contract with Kind 2.")
    ap.add_argument("contract", help="path of the contract file")
    ap.add_argument("property", help="property name, or ALL")
    ap.add_argument("n_of_participants", type=V.parse_users,
                    help=f"number of user addresses, or {V.ANY} (every number of users)")
    ap.add_argument("timeout", type=float,
                    help="time limit per property, in seconds (0: no limit, the search goes on"
                         " until there is a verdict)")
    ap.add_argument("--strategy", choices=V.STRATEGIES, default="portfolio",
                    help="portfolio (default): invariants, checks on free states, and Kind 2"
                         " on the transition system, in rounds of doubling budgets; kind2:"
                         " Kind 2 on the transition system only")
    ap.add_argument("--no_invgen", action="store_true",
                    help="do not generate candidate invariants (only those of the file)")
    ap.add_argument("--no_user_invariants", action="store_true",
                    help="ignore the invariants declared in the files (as candidates for"
                         " the proofs; they are still verified)")
    ap.add_argument("--no_lemmas", action="store_true",
                    help="do not load the lemmas file of the benchmark family")
    ap.add_argument("--print_invariants", action="store_true",
                    help="print the invariants proved (declared and generated)")
    ap.add_argument("--invariants_timeout", type=float, default=None,
                    help="time limit of the invariant phase, before the properties (default: 3 x"
                         " timeout; 0: no limit)")
    ap.add_argument("--users_mode", choices=V.USERS_MODES, default=None,
                    help="combined (default): the checks with the cutoff of the checks on free"
                         " values, if it is at most n_participants (proofs then hold for every"
                         " number of users from the cutoff on), and with n_participants users,"
                         " in turn; exact: n_participants users only; parameterized: the"
                         " cutoff only (DESIGN.md, Sect. 7)")
    ap.add_argument("--parameterized", dest="users_mode", action="store_const",
                    const="parameterized", help="the same as --users_mode parameterized")
    ap.add_argument("--only_lus", action="store_true", help="only generate the Lustre files")
    ap.add_argument("--cex", action="store_true", help="print counterexamples")
    ap.add_argument("--solver", choices=("auto",) + SOLVERS, default="auto",
                    help="SMT solver used by Kind 2; auto: cvc5 for at most half of the "
                         "timeout, then z3 if there is no verdict (default: auto)")
    ap.add_argument("--mode", choices=MODES, default=V.DEFAULT_MODE,
                    help=f"encoding of modalities (default: {V.DEFAULT_MODE})")
    ap.add_argument("--expand", default=",".join(V.DEFAULT_EXPAND),
                    help="finite types whose quantifiers are expanded, comma-separated "
                         f"(address, method; 'none' for none; default: "
                         f"{','.join(V.DEFAULT_EXPAND)}); method:N expands the method "
                         "quantifiers while their nested copies are at most N (default "
                         f"{METHOD_COPIES})")
    ap.add_argument("--color", choices=("auto", "always", "never"), default="auto",
                    help="colors in the messages (default: auto, on a terminal unless"
                         " $NO_COLOR is set)")
    ap.add_argument("--out_lus", default="out_lus", help="directory for the Lustre files")
    ap.add_argument("--out_results", default="out_results", help="directory for the verdicts")
    args = ap.parse_args()
    args.users_mode = V.users_mode_of(args.users_mode)
    if args.n_of_participants == V.ANY and (args.strategy == "kind2"
                                            or args.users_mode == "parameterized"):
        ap.error(f"{V.ANY} needs --strategy portfolio and --users_mode combined or exact")
    c, ce = palette(args.color), palette(args.color, sys.stderr)

    try:
        program, warnings = V.load(args.contract, lemmas=not args.no_lemmas)
        properties = V.select_properties(program, args.property)
    except KindHMLError as e:
        print(f"{args.contract}: {ce.red('error:')} {e}", file=sys.stderr)
        return 2
    for w in warnings:
        print(f"{args.contract}: {ce.yellow('warning:')} {w}", file=sys.stderr)

    expand = () if args.expand == "none" else tuple(x for x in args.expand.split(",") if x)
    try:
        parse_expand(expand)
    except ValueError as e:
        print(f"{args.contract}: {ce.red('error:')} --expand: {e}", file=sys.stderr)
        return 2
    name = V.stem(args.contract)
    timeout = int(args.timeout) if args.timeout == int(args.timeout) else args.timeout
    os.makedirs(args.out_lus, exist_ok=True)
    context: dict = {}                  # invariants are proved once for all the properties
    if args.strategy == "portfolio" and not args.only_lus:
        start = time.time()
        limit = (args.invariants_timeout if args.invariants_timeout is not None
                 else 3 * args.timeout)
        entries = V.prove_invariants(program, args.n_of_participants, limit or None,
                                     context, mode=args.mode, expand=expand,
                                     invgen=not args.no_invgen,
                                     user_invariants=not args.no_user_invariants,
                                     users_mode=args.users_mode)
        elapsed = c.dim(f"[{time.time() - start:.1f}s]")
        for invs in entries:
            head = f"({V.invariant_label(invs)}) " if len(entries) > 1 else ""
            print(f"{name} - {head}{V.invariant_summary(invs, c)} {elapsed}", flush=True)
    code = 0
    for prop in properties:
        tag = f"{name}_{prop.name}_{args.n_of_participants}_{timeout}"
        lus_path = os.path.join(args.out_lus, tag + ".lus")
        if args.only_lus:
            users, ghost = V.kind2_target(context, program, prop, args.n_of_participants,
                                          args.users_mode, args.mode, expand,
                                          not args.no_invgen, not args.no_user_invariants)
            with open(lus_path, "w") as f:
                f.write(V.lustre_for(program, prop, users, args.mode, expand,
                                     ghost_sums=ghost))
            print(f"{name} - {prop.name}: {lus_path}")
            continue
        outcome = V.verify(program, prop, args.n_of_participants, args.timeout or None,
                           mode=args.mode, expand=expand, lus_path=lus_path,
                           solver=args.solver, cex=args.cex, strategy=args.strategy,
                           context=context, invgen=not args.no_invgen,
                           user_invariants=not args.no_user_invariants,
                           users_mode=args.users_mode)
        print(f"{name} - {outcome.describe(c)}", flush=True)
        if args.cex and outcome.status == "invalid" and outcome.result.counterexample:
            print(format_counterexample(outcome.result.counterexample, c=c), flush=True)
        os.makedirs(args.out_results, exist_ok=True)
        with open(os.path.join(args.out_results, tag + ".out"), "w") as f:
            f.write(f"{name} - {outcome.describe()}\n")      # without colors
        if outcome.status == "error":
            code = 1
    if args.print_invariants:
        for line in V.invariant_report(context):
            print(f"{name} - {line}")
    return code


if __name__ == "__main__":
    sys.exit(main())
