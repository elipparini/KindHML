#!/bin/sh
# The benchmarks of the paper: every property of every benchmark contract, 2 participants,
# a budget of 1000 s per property, exactly 2 users (the tables of the paper). Properties are
# checked one at a time. The table of verdicts is written to results/benchmarks.csv.
cd "$(dirname "$0")"
PY=${PYTHON:-.venv/bin/python}
exec "$PY" tests/run_all.py contracts/bank contracts/vault contracts/price-bet \
    --participants 2 --users_mode exact --timeout 1000 --csv results/benchmarks.csv
