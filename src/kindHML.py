"""KindHML: verification of CHML properties of contracts with Kind 2.

Usage:
    python3 src/kindHML.py <contract.sol> <Rule|ALL> <n_participants> <timeout> [--only_lus]

For each rule, the Lustre encoding is saved in out_lus/<contract>_<Rule>_<n>_<timeout>.lus and
the verdict in out_results/<contract>_<Rule>_<n>_<timeout>.out.
"""

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from kindhml import verify as V                     # noqa: E402
from kindhml.encode_formula import MODES           # noqa: E402
from kindhml.errors import KindHMLError             # noqa: E402
from kindhml.kind2 import SOLVERS, format_counterexample   # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description="Verify CHML rules of a contract with Kind 2.")
    ap.add_argument("contract", help="path of the contract file")
    ap.add_argument("property", help="rule name, or ALL")
    ap.add_argument("n_of_participants", type=int, help="number of user addresses")
    ap.add_argument("timeout", type=float,
                    help="time limit per rule, in seconds (0: no limit, the search goes on"
                         " until there is a verdict)")
    ap.add_argument("--strategy", choices=V.STRATEGIES, default="portfolio",
                    help="portfolio (default): invariants, checks on free states, and Kind 2"
                         " on the transition system, in rounds of doubling budgets; kind2:"
                         " Kind 2 on the transition system only")
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
                         f"{','.join(V.DEFAULT_EXPAND)})")
    ap.add_argument("--out_lus", default="out_lus", help="directory for the Lustre files")
    ap.add_argument("--out_results", default="out_results", help="directory for the verdicts")
    args = ap.parse_args()

    try:
        program, warnings = V.load(args.contract)
        rules = V.select_rules(program, args.property)
    except KindHMLError as e:
        print(f"{args.contract}: error: {e}", file=sys.stderr)
        return 2
    for w in warnings:
        print(f"{args.contract}: warning: {w}", file=sys.stderr)

    expand = () if args.expand == "none" else tuple(x for x in args.expand.split(",") if x)
    name = V.stem(args.contract)
    timeout = int(args.timeout) if args.timeout == int(args.timeout) else args.timeout
    os.makedirs(args.out_lus, exist_ok=True)
    context: dict = {}                  # invariants are proved once for all the rules
    code = 0
    for rule in rules:
        tag = f"{name}_{rule.name}_{args.n_of_participants}_{timeout}"
        lus_path = os.path.join(args.out_lus, tag + ".lus")
        if args.only_lus:
            with open(lus_path, "w") as f:
                f.write(V.lustre_for(program, rule, args.n_of_participants, args.mode, expand))
            print(f"{name} - {rule.name}: {lus_path}")
            continue
        outcome = V.verify(program, rule, args.n_of_participants, args.timeout or None,
                           mode=args.mode, expand=expand, lus_path=lus_path,
                           solver=args.solver, cex=args.cex, strategy=args.strategy,
                           context=context)
        line = f"{name} - {outcome.describe()}"
        print(line, flush=True)
        if args.cex and outcome.status == "invalid" and outcome.result.counterexample:
            print(format_counterexample(outcome.result.counterexample), flush=True)
        os.makedirs(args.out_results, exist_ok=True)
        with open(os.path.join(args.out_results, tag + ".out"), "w") as f:
            f.write(line + "\n")
        if outcome.status == "error":
            code = 1
    return code


if __name__ == "__main__":
    sys.exit(main())
