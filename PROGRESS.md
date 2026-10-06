# KindHML v1 — Progress log

Branch `v1` (worktree `~/Desktop/gitlab/KindHML-v1`). The old tool stays on `main`
(`~/Desktop/gitlab/KindHML`) for differential testing. Work stops after each milestone.

## Milestones

- [x] **M1** Worktree, design note (`DESIGN.md`), Kind 2 experiments.
- [x] **M2** Grammar, AST, type checker; parse tests on all benchmarks and regressions.
- [x] **M3** Desugaring, `Trans` encoding, Lustre printer; unit tests; reference evaluator.
- [x] **M4** Formula encoding, full pipeline, regressions imported; all ground truths checked.
- [x] **M5** Contract-to-contract calls; README; `run_experiments.sh`; `\CL` notes in the paper.

## M1 — Kind 2 experiments (Kind 2 v2.3.0-467, cvc5 1.1.1)

The test files are in `experiments/kind2/`; the conclusions are:

1. A property may call a Lustre `function` whose arguments contain quantified variables only if
   the function is *inlinable*. Functions over records, enums, and scalars are inlinable, also
   with local variables and nested calls. Functions over **arrays** are not.
   ⇒ maps are records with one field per address; each level of `S^i` is a local record.
2. Nested modalities as nested calls `trans(trans(s, t1), t2)` work (k-induction proves them).
3. Quantifying over a **record** type (`exists (t: Tx)`) gives correct answers but makes BMC
   and k-induction crash (`Ltree.fold : quantified term`), leaving only IC3.
   ⇒ quantified variables are scalars; `args` variables are expanded.
4. With scalar quantifiers only the invariant generator raises that exception; it is harmless.
5. `-json` output gives, per property: `answer.value` (`valid`/`falsifiable`/...), `answer.source`
   (engine), `k`, `runtime`, and a counterexample.

## M2 — Front end

* `src/kindhml/grammar/KindHML.g4` (ANTLR 4.13.2; regenerate with `tools/gen_parser.sh`),
  `builder.py` (parse tree → raw AST), `syntax.py` (AST), `typecheck.py` (resolution and
  typing), `pretty.py`. Tests: `.venv/bin/pytest tests` (45 tests).
* All 10 benchmark files and 11 regression files parse and type-check.
* Regressions imported in `contracts/regression/` (raw import in commit `58df658`; later
  changes are separate diffs). Ground truth of a rule: the `@groundtruth` comment if present,
  otherwise the `_true`/`_false` suffix of its name.
* Changes to input files: `Pricebet` → `Bet` (price-bet*), `Addittivity` → `Additivity`,
  `st.balance` → `balance` (liquidity4, legacy Solvent syntax).
* `signature_error.sol` tests a bug of the old tool (it checked `donate(1)` against the
  signature of `dummy`); the new checker accepts it, as it should.
* Language choices: a contract without constructor gets an empty one; quantified names must
  be unique within a rule; `x += e` is sugar for `x = x + e`; `if` without `else` has an
  empty `else`; `payable(e)` is `e`.

## M3 — Transition encoding

* `model.py` (addresses, methods, variables), `desugar.py` (guards, `initPay`),
  `encode_trans.py` (Init, S^i, Trans_f, Trans_C, Trans), `lustre.py` (Lustre AST and printer),
  `kind2.py` (runner), `reference.py` (interpreter of the operational semantics),
  `lustre_eval.py` (Python evaluator of the generated Lustre, for tests).
* Tests (`tests/test_trans.py`): on 300 random (state, transaction) pairs per file,
  the generated `trans`, evaluated in Python, equals the interpreter's result (all 22 files,
  incl. `tests/contracts/features.sol`, which exercises nested ifs, divisions, uint, maps of
  bool/address, payable, transfers). Mutations of the encoder are detected. Kind 2 agrees on
  3 samples per file (`pytest -m kind2`, 33 s, one Kind 2 job at a time).
* Kind 2 runner: one process group per run, killed (with its cvc5 children) when the run ends
  or times out; memory capped at 3 GB via a `systemd-run --user` scope (`RLIMIT_AS` cannot be
  used: OCaml 5 reserves a large virtual heap).
* Performance note: every occurrence of `trans(...)` in a property is inlined separately by
  Kind 2; ten closed properties with projections `trans(S,T).f` did not finish in 15 s, while
  binding `trans(S,T)` to a local once per case takes 2 s. Relevant for M4.

### Point to discuss: a gap in the paper (A5(iv))

A5(iv) says that a transaction whose sender is the called contract is not valid "whatever the
amount". The encoding enforces it only through `send_enabled` in the `initPay` of **payable**
procedures; for a non-payable procedure `initPay` is `require(value == 0)`, which does not
exclude `sender = C`. The tool adds an explicit first statement
`require(sender != null && sender != C)` to every procedure (see `desugar.py`).

## M4 — Formula encoding and pipeline

* `encode_formula.py` (Φ, modes `inline` [default], `levels`, `exists`, `subst`; expansion of
  address/method quantifiers), `lustre_subst.py` (substitution, simplification),
  `verify.py` (pipeline), `src/kindHML.py` (CLI, as before plus `--cex --solver --mode
  --expand`), `tests/run_all.py` (batch runner, CSV), `tests/test_formula.py` (differential
  test of Φ against a bounded reference evaluator of the logic, no Kind 2),
  `tests/test_regressions.py` (end-to-end, `-m kind2`).
* Findings (details in DESIGN.md §2): expansion of finite quantifiers is essential; with cvc5,
  Kind 2 crashes on many quantified properties that have a counterexample (z3 does not),
  while cvc5 is faster on many valid rules, so the default strategy `auto` runs cvc5 for half
  of the budget and then z3; nested `trans` calls crash Kind 2's normaliser.
* Regressions (64 rules, budget 20 s): 59 match; open: `division` P1 (nonlinear witness),
  `two-donatees` P2, P4, P2b, P3c (true, need an auxiliary invariant; upstream notes say
  Kind 2 returns unknown).
* Changes to regression files: `is_EOA(a) ->` guards in 14 `_true` rules (address domain);
  `liquidity4` P9, P13, P15 relabelled True (vacuous: contract balance is 0 initially and C4
  has no payable procedure; the same holds for all its rules guarded by `balance > 1`).
* Benchmarks (31 rules): all decided with a budget of 120 s; see `results/v1_benchmarks.csv`.
  Disagreements with the ground truth, all explained:
  - `price-bet` Liquidity, Frontrunning, `price-bet_v3` Liquidity: the constructor may set
    `oracle = null`; then nobody can call `set`. Genuine under the paper's semantics, also
    for the paper's listing (note in examples.tex). To decide.
  - `vault_v3` non-inflation: the file's formula (∃ first tx, ∀ second tx) is true (witness:
    `withdraw(r, 0)`); the paper's formula (`chmlVaultB`, universal) is the intended one.
    The old tool's counterexample (step 0) is spurious. Proposal: use the paper's formula.

## M5 — Contract calls, robustness, documentation

* Contract-to-contract calls by unfolding (`syntax.Unfold`, `desugar.callee`, frames in
  `encode_trans.py`); arguments and value evaluated at the call point; cyclic calls rejected
  (A4). Reference interpreter executes calls natively. Tests: `tests/contracts/calls.sol`
  (differential test of Trans; mutations "callee sees the original sender" and "arguments
  evaluated after the transfer" are detected; unit tests; end-to-end rules).
* Lemma `_lemma_balances_nonnegative` added to every Lustre program (DESIGN.md §2).
* Kind 2 runner: each run in a named systemd scope, stopped at the end (a z3 process had
  survived a run, because Kind 2 runs in its own process group). Plain-text output without
  counterexamples by default (JSON only with `--cex`): building a counterexample can take
  longer than finding it (DESIGN.md §2). The JSON reader tolerates truncated output.
* `\CL` notes in the paper: contract calls (encoding-fol.tex), uint (contracts.tex).
* Results (`results/v1_benchmarks.csv`, budget 120 s; `results/v1_regressions.csv`, budget
  20 s, also `tests/contracts`): the benchmarks give the same verdicts as in M4. The
  regressions also do, except `signature_error` P5_true: it is valid, but z3 (IC3) needs about
  11 s and gets only the second half of the 20 s budget (valid with 60 s, faster with the
  lemma than without). In `calls.sol`, Relay_never_reverts needs a budget of about 30 s for
  the same reason. `pytest -m kind2 tests/test_regressions.py` (budget 30 s, regressions
  and `tests/contracts`): 65 passed, 5 expected failures (the open rules of M4), 7 min 40 s.

## After M5 — consistency of tool and paper (decisions 5–7 below)

* Senders: a transaction starts with `require(is_EOA(sender))` (was: `sender != null &&
  sender != C`); unfolded calls have no such guard, their sender is the calling contract.
  Same verdicts on all single-contract files; test `test_senders_of_transactions_and_of_calls`.
* Init: every balance is nonnegative (contracts included); was: contract balances 0.
* Benchmark files:
  - `liquidity4`: the relabelling of P9, P13, P15 (M4) is undone (now falsified, also for
    users); `is_EOA(addr) ->` guards in P2, P4, P6, P12, P14 (with `addr = C4` the
    transaction reverts, now that `balance > 1` is reachable).
  - `price-bet`, `_v2`, `_v3`: `require(oracle_addr != null)` in the constructor; new mutant
    `price-bet_v4` = the previous `price-bet`.
* Results (`results/v1_benchmarks.csv`, 120 s; `results/v1_regressions.csv`, 30 s, with
  `liquidity4` rerun after the guards):
  - benchmarks: 34 rules; all match except `vault_v3` non-inflation (formula, pending).
    `bank` and `bank_v2` Liquidity were unknown in the batch: alone, `bank` is valid in 37 s,
    and `bank_v2` needs 54 s of cvc5, at the edge of cvc5's half of 120 s (it was 58 s in M5).
  - regressions and `tests/contracts`: 65 of 70 match; `two-donatees` P2b_true now matches
    (IC3, 30 s). Open: `division` P1, `two-donatees` P2, P4, P3c, and `signature_error`
    P5_true. The last one is valid, but at the edge: with 60 s, the current encoding was once
    unknown and once valid (48 s, z3 16 s); with the old guard or the old Init, valid in 52 s
    and 47 s (one run each). So the time varies between runs.
  - `pytest -m kind2 tests/test_regressions.py` (30 s): 64 passed, 5 expected failures,
    1 unexpected pass (`two-donatees` P2b_true), 7 min 39 s.

## After M5 — block number as an increase (decision 8 below)

* Modalities `<< s : C . f(args) $ v @ d >>`: `d` (uint, 0 when omitted) is the increase of
  the block number made by the transaction. A transaction starts with `require(d >= 0);
  block_num := block_num + d`; Init: `block_num` any value >= 0; the environment assumption
  `Tx.block_num >= block_num` and the existential block of every modality are gone.
* Vault files: the same two rules for all mutants, with explicit increases (drainability:
  `∃d1, d2 : int`; non-inflation: `∀d1, d2 : int. d1 + d2 < wait_time -> ...`, any
  senders), exactly the formulae now in the paper (`tab-properties.tex`); a negative
  increase only makes the transaction revert, so no guard is needed.
  price-bet_v2 rules unchanged (all steps in one block).
* Paper: the block number is now in the formal model (syntax, state, initial states,
  transaction rule, modal operator and its typing, encoding, appendix); the `\CL` notes on
  it are removed, except the one on reverted transactions.
* Tests: `test_transactions_increase_the_block_number`, `test_block_increase_in_modality`;
  Trans differential test with negative increases; Kind 2 Trans test: 24 passed.
* Benchmarks (`results/v1_benchmarks.csv`, 120 s; Vault rows with the `int` increases):
  32 of 34 match; vault_v3 non-inflation is now false, as in the paper's table.
  bank_v2 Liquidity: unknown at the edge of cvc5's half of the budget (see above).
  vault drainability: valid in 52 s with `uint` increases; with `int`, in the batch cvc5 did
  not finish within its 60 s and the run ended after 260 s with an error (Kind 2 should
  have been stopped at about 140 s; not reproduced); run again alone, valid in 42 s with
  the default strategy and in 45 s with cvc5 only. Regression files do not use the block
  number, so their encoding is unchanged.

## After M5 — real variables (decision 9 below)

* Type `real` for fields, mapping values, parameters and quantified variables; real
  literals; implicit conversion int → real; `pragma balance real;` makes balances, values
  and amounts real (the block number stays int). Details and the Kind 2 points in DESIGN.md,
  Sect. 5.
* The Lustre output of all 104 existing rules is unchanged (compared before and after).
* Tests: front end (conversions, `%` on reals, real into int, pragma, warning), encoding
  (guard `<> 0.0`, `/`, literals, real balances), counterexample values; the Trans and
  formula differential tests now cover `tests/contracts/reals.sol` and
  `tests/contracts/real_balances.sol` (values: halves; real quantifiers: the integer domain
  and its midpoints). 15 new rules, all matching their ground truth with Kind 2 (20 s
  budget). With integer balances (the file without the pragma), `Split_is_fair` and
  `Small_payment` become invalid, as expected.

## After M5 — AMM and lending use cases, part 1: invariants (decisions 10–11 below)

* Experiments on a constant-product AMM in reals (contracts/amm/amm.sol, 8 rules): with
  Kind 2 on the transition system, 2 rules proved, 6 unknown after 30 s with both solvers.
  With Kind 2's default engines, nonlinear runs exceeded the memory: a run with a 3 GB cap,
  on a machine with 1.7 GB available, caused a global OOM (the editor was killed). Since
  commit 22dd6ff the cap is the smaller of 3 GB and half of MemAvailable.
* Diagnosis: rules hold because of invariants of the reachable states (nonnegative wallets and
  reserves), which Kind 2 does not find through nonlinear transitions. Checked on a free
  state with these invariants as premise, a rule is a single SMT query: the swap-pool round
  trip is proved in 1 s, and the inductive step of the invariant in 0.8 s.
* New: `invariant` declarations, Houdini, checks on free states, BMC search for the state
  that refutes a rule, portfolio strategy in rounds (DESIGN.md, Sect. 6); the runner
  reports when the memory limit killed a solver. Test contract `tests/contracts/swap_pool.sol`.
* Then: random testing with exact confirmation (`fuzz.py`), hoisting of universal
  quantifiers, invariants required after construction, Houdini per procedure and
  incremental, use cases `contracts/{amm,amm-simple,lending,lending-simple}` (DESIGN.md,
  Sect. 6). The batch of the 182 use-case rules with the final tool was stopped when the
  session ended (its log was in the scratchpad); to be rerun with logs in `runs/`.

## Planned (agreed with the user, 2026-10-06): better search for counterexamples

The search for the state s* that refutes a rule on a free state (task 3 of the portfolio)
asks BMC for a state equal to s* in every field, through the whole Trans at every step;
in the runs so far it found 7 counterexamples, fuzzing most of the others. Plan, in this
order (experiments first, on the false lending rules still unknown, whose counterexamples
need about six specific steps; then implementation; then the 182-rule batch, logged in
`runs/`):
1. Generalise s*: search only the fields read by the rule (possibly the constraints of its
   premise instead of exact values), as IC3 generalises its counterexamples to induction.
2. Guided fuzzing: score reachable states by their distance to the target (s*, or the
   premise of the rule) and extend the best traces first (hill climbing or evolutionary).
3. Symbolic search over fixed sequences of procedures: senders and arguments symbolic,
   one SMT query per sequence ("do these transactions reach a state where φ fails?"),
   built with the modality encoding (one procedure unfolded per step); sequences limited
   to the procedures that write the fields of the rule, or proposed by the fuzzer.
4. Later, mostly for linear contracts: prove s* unreachable with k-induction or IC3 on
   `s ≠ s*` and add the invariants that Kind 2 prints to the assumed ones (refinement).

## Decisions taken after M1 (with the user)

1. **Domain of `address` quantifiers:** all addresses except `null` (users and contracts).
   A new predicate `is_EOA(e)` holds iff `e` is a user address (not `null`, not a contract).
   Rules whose ground truth assumes users only (e.g. `mapping1` `P1_true`) get an explicit
   `is_EOA(a) ->` guard; every such change of a benchmark is listed in M4.
2. **Unconstructed states:** `φ` is checked in the reachable states where every contract is
   constructed (the property is `(∧_C constructed_C) → Φ(φ)`).
3. **Contract names in modalities:** an unknown name is a type error; `Pricebet` (price-bet)
   and `Addittivity` (regression additivity) are corrected in the files.
4. (after M4 part 1) **Method quantifiers** exclude constructors. **Init**: contract balances
   are 0 (paper); a `\CL` note asks whether to allow any nonnegative initial balance.
   **Bet with oracle = null**: the benchmark is discussed in the paper, so it is not changed;
   a `\CL` note in examples.tex records the issue.
5. (after M5) **Senders:** only users send transactions (paper and tool); in unfolded
   contract calls the sender is the calling contract. **Init:** all balances nonnegative
   (paper and tool). **Domains** of `address` and `method` as in decisions 1 and 4, now
   stated in the paper; uint presented in the paper as sugar for `require` statements.
6. (after M5) **Bet:** `require(o != null)` in the main version and in v2, v3 (paper
   listing and files); the previous main version is the new mutant v4; its rows in the
   paper's results table are placeholders until the table is regenerated.
7. (after M5) **block.number:** stays outside the formal model for now; the proposal (block
   number as a component of the transaction) is a `\CL` note in examples.tex.
8. (after M5) **block.number, decided:** the transaction carries the increase of the block
   number (`@ d`, uint, 0 when omitted); applied at the start of the transaction, before
   `initPay`; a revert leaves the state, block number included, unchanged (`\CL` note on
   this); initial block number any value >= 0. Plan for the paper in a `\CL` note.
9. (after M5) **Reals:** implicit int → real conversion (no real → int); balances, values
   and amounts real only with `pragma balance real;` in the file (default int), so files
   stay self-contained and existing benchmarks are unchanged. Tool only; the paper is not
   changed.
10. (after M5) **AMM and lending use cases:** general models (unknown verdicts acceptable)
    and, separately, simplified models; the integer version of each use case as a mutation;
    the two tokens as ledgers embedded in the contract; lending prices set by a designated
    oracle, and, as a version, by anyone (manipulable oracle).
11. (after M5) **Invariant-assisted checking** (DESIGN.md, Sect. 6). The tool should not
    answer "unknown" by itself but go on searching; a time limit is given only in tests.
    Paper: only a `\CL` note for now.
