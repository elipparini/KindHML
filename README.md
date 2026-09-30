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
- `timeout`: time budget per rule, in seconds.

Examples:

```
python3 src/kindHML.py contracts/bank/bank.sol Additivity 2 60
python3 src/kindHML.py contracts/vault/vault_v2.sol ALL 2 30 --cex
```

Options:

- `--only_lus`: only write the Lustre encoding.
- `--cex`: print counterexamples.
- `--solver auto|z3|cvc5`: SMT solver used by Kind 2. `auto` (default) runs cvc5 for at most
  half of the budget and, if it gives no verdict, z3 for the rest.
- `--mode inline|levels|exists|subst`: encoding of modalities (default `inline`, see
  `DESIGN.md`).
- `--expand address,method|none`: expand quantifiers over these finite types (default both).

Each rule's Lustre file is saved in `out_lus/<contract>_<Rule>_<n>_<timeout>.lus`, and its
verdict in `out_results/<contract>_<Rule>_<n>_<timeout>.out`. The verdict is compared with the
ground truth of the rule: a comment `// @groundtruth: True|False` right before it, or else the
suffix `_true`/`_false` of its name.

Kind 2 runs in its own process group, which is killed at the end of each run, and its memory
(with its solvers) is limited to 3 GB when `systemd-run --user` is available.

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

Formulas: `forall`/`exists x : T .` with `T` in `int, uint, bool, address, method,
calldataargs`; modalities `<< sender : Contract . f(args) $ value >> φ`; `old(e)`;
`lastReverted`; `is_EOA(e)`; `balance`, `balance[a]`, contract fields.

## Tests and experiments

```
.venv/bin/pytest -m "not kind2 and not slow"   # front end, Trans differential test (seconds)
.venv/bin/pytest -m slow             # differential test of the formula encoding (minutes)
.venv/bin/pytest -m kind2            # with Kind 2, one job at a time (minutes)
.venv/bin/python tests/run_all.py --timeout 20 [files or directories]
bash run_experiments.sh              # the benchmarks of the paper
```

`tools/gen_parser.sh` regenerates the parser from `src/kindhml/grammar/KindHML.g4`.
