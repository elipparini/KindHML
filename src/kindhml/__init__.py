import os
import sys


def fix_hash_seed():
    """Runs this program again with PYTHONHASHSEED=0, unless it is already set so: the order of
    the sets of strings, and of what is built from them, is then the same in every run. A
    safeguard: with the seeds 1 and 2, the Lustre programs of all 370 properties, the
    candidate invariants and the traces of the fuzzer were the same (2026-10-29)."""
    if os.environ.get("PYTHONHASHSEED") != "0":
        os.environ["PYTHONHASHSEED"] = "0"
        os.execv(sys.executable, sys.orig_argv)
