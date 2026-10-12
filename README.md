# KindHML — verification of smart contracts against CHML properties

KindHML encodes a contract and a CHML rule (a Hennessy–Milner-style formula) into a Lustre
transition system with an invariant property, and checks it with the Kind 2 model checker.
The encoding follows the paper (Sect. "Encoding in first-order logic"); `DESIGN.md` maps the
paper's definitions to the modules and lists the deviations.

## Prerequisites

- Python 3.8 or newer, and the packages in `requirements.txt`:
  `python3 -m venv .venv && .venv/bin/pip install -r requirements.txt`
  (ANTLR runtime 4.13.2, z3, pytest).
- Kind 2 (tested with v2.3.0), as `./kind2/kind2`, or `$KIND2`, or on the `PATH`.
- cvc5 on the `PATH` (Kind 2 calls it); z3 comes with the `z3-solver` package.

## Usage

```
python3 src/kindHML.py <contract.sol> <Rule|ALL> <n_participants> <timeout> [options]
```

- `n_participants`: number of user addresses (EOAs) besides `null` and the contracts.
- `timeout`: time limit per rule, in seconds; 0 for no limit (the search then goes on until
  there is a verdict).

Examples:

```
python3 src/kindHML.py contracts/bank/bank.sol Additivity 2 60
python3 src/kindHML.py contracts/vault/vault_v2.sol ALL 2 30 --cex
```

Options:

- `--only_lus`: only write the Lustre encoding.
- `--cex`: print counterexamples. Kind 2 may need much longer to build a counterexample than
  to find it, so a rule can then need a larger budget.
- `--solver auto|z3|cvc5`: SMT solver used by Kind 2. `auto` (default) runs cvc5 for at most
  half of the budget and, if it gives no verdict, z3 for the rest.
- `--mode inline|levels|exists|subst`: encoding of modalities (default `inline`, see
  `DESIGN.md`).
- `--expand address,method|none`: expand quantifiers over these finite types (default both).
  `method:N` expands the method quantifiers only while the copies of the formula they make
  (the product of the numbers of methods of the nested expanded ones) are at most `N`
  (default 32); the outer quantifiers are expanded first, the others stay quantified.
- `--strategy portfolio|kind2`: `portfolio` (default) proves the file's invariants, checks
  each rule on an arbitrary state satisfying them, searches for the state that refutes it,
  and runs Kind 2 on the transition system, in rounds with doubling budgets; `kind2` only
  runs Kind 2 on the transition system. See `DESIGN.md`, Sect. 6.
- `--no_invgen`: do not generate candidate invariants (only those of the file are used).
- `--no_user_invariants`: do not use the declared invariants (of the file, or of the spec and
  lemmas of a benchmark family) as candidates for the proofs; they are still verified.
- `--no_lemmas`: do not load the lemmas file of a benchmark family.
- `--print_invariants`: print the invariants proved (declared and generated).
- `--invariants_timeout`: time limit of the invariant phase, which runs once before the
  rules (default: 3 times `timeout`).

Each rule's Lustre file is saved in `out_lus/<contract>_<Rule>_<n>_<timeout>.lus`, and its
verdict in `out_results/<contract>_<Rule>_<n>_<timeout>.out`. The verdict is compared with the
ground truth of the rule. For a contract of a benchmark family (a directory with `spec.hml`,
see `contracts/README.md`), the rules and the ground truth come from the files of the family.
Otherwise, the rules follow the contracts in the same file, and the ground truth of a rule is
a comment `// @groundtruth: True|False` right before it, or else the suffix `_true`/`_false` of
its name.

Each Kind 2 run, with its solvers, is placed in a `systemd-run --user` scope, which limits
their memory to the smaller of 3 GB and half of the available memory (or
`$KINDHML_MEMORY_GB`) and is stopped at the end of the run. Without systemd, the processes are
killed at the end of the run and the memory limit is per process.

## Input language

```
contract Bank {
    mapping (address => int) funds;
    function deposit() payable { funds[msg.sender] += msg.value }
    function withdraw(int amount) {
        require(amount > 0 && amount <= funds[msg.sender]);
        funds[msg.sender] -= amount;
        msg.sender.transfer(amount)
    }
}

// @groundtruth: True
rule Liquidity {
    forall a : address . forall n : int .
    (is_EOA(a) && n >= 0 && n <= funds[a]) ->
    exists f : method . exists args : calldataargs .
    << a : Bank . f(args) $ 0 >> balance[a] == old(balance[a] + n)
}
```

Types of fields and parameters: `int`, `uint`, `real`, `bool`, `address`,
`mapping (address => T)`. An `int` can be used where a `real` is expected (the tool
converts it); a `real` cannot be used as an `int`. Real literals are written `0.5`; `%` is
not defined on reals; `a / b` is the division of reals if an operand is real, and the
Euclidean division otherwise (so `r = n / 2` with `n : int` converts `n div 2`, with a
warning). Balances, `msg.value` and amounts are `int`, or `real` if the file starts with
`pragma balance real;` (see `tests/contracts/real_balances.sol`).

Formulas: `forall`/`exists x : T .` with `T` in `int, uint, real, bool, address, method,
calldataargs`; modalities `<< sender : Contract . f(args) $ value @ blocks >> φ`, where
`blocks` (a uint, 0 when omitted) is the increase of the block number made by the
transaction; `old(e)`; `lastReverted`; `is_EOA(e)`; `balance`, `balance[a]`,
`block.number`, contract fields; `sum(m)`, the sum of a mapping `m` (or of `balance`) over
all addresses.

Besides rules, a file may declare invariants, `invariant Name { φ }`, with `φ` without
modalities, required where all contracts are constructed. The tool also generates
candidate invariants from templates (signs, bounds, totals such as `sum(m) == total`, ...).
It proves those that are inductive and assumes them when it checks the other rules (see
`tests/contracts/swap_pool.sol`); this helps much with nonlinear arithmetic.

A file may contain several contracts, which can call each other (no cycles):
`Token.mint(msg.sender, n) $ msg.value` calls `mint` of contract `Token`, transferring
`msg.value` tokens with the call. With several contracts, rules write `C.x` for a field `x` of
`C` and `C.balance` (or `balance[C]`) for its balance; see `tests/contracts/calls.sol`.

## Tests and experiments

```
.venv/bin/pytest -m "not kind2 and not slow"   # front end, Trans differential test (seconds)
.venv/bin/pytest -m slow             # differential test of the formula encoding (minutes)
.venv/bin/pytest -m kind2            # with Kind 2, one job at a time (minutes)
.venv/bin/python tests/run_all.py --timeout 20 [files or directories]
bash run_experiments.sh              # the benchmarks of the paper
```

`tools/gen_parser.sh` regenerates the parser from `src/kindhml/grammar/KindHML.g4`.


// TODO change "rule" into "property"