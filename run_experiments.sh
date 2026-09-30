#!/bin/sh
# The benchmarks of the paper: every rule of every benchmark contract, 2 participants,
# a budget of 1000 s per rule. Rules are checked one at a time.
# The table of verdicts is written to results/benchmarks.csv.
cd "$(dirname "$0")"
PY=${PYTHON:-.venv/bin/python}
exec "$PY" tests/run_all.py contracts/bank contracts/vault contracts/price-bet \
    --participants 2 --timeout 1000 --csv results/benchmarks.csv
