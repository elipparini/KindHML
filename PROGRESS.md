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
  changes are separate diffs). Ground truth of a property: the `@groundtruth` comment if present,
  otherwise the `_true`/`_false` suffix of its name.
* Changes to input files: `Pricebet` → `Bet` (price-bet*), `Addittivity` → `Additivity`,
  `st.balance` → `balance` (liquidity4, legacy Solvent syntax).
* `signature_error.sol` tests a bug of the old tool (it checked `donate(1)` against the
  signature of `dummy`); the new checker accepts it, as it should.
* Language choices: a contract without constructor gets an empty one; quantified names must
  be unique within a property; `x += e` is sugar for `x = x + e`; `if` without `else` has an
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
  while cvc5 is faster on many valid properties, so the default strategy `auto` runs cvc5 for half
  of the budget and then z3; nested `trans` calls crash Kind 2's normaliser.
* Regressions (64 properties, budget 20 s): 59 match; open: `division` P1 (nonlinear witness),
  `two-donatees` P2, P4, P2b, P3c (true, need an auxiliary invariant; upstream notes say
  Kind 2 returns unknown).
* Changes to regression files: `is_EOA(a) ->` guards in 14 `_true` properties (address domain);
  `liquidity4` P9, P13, P15 relabelled True (vacuous: contract balance is 0 initially and C4
  has no payable procedure; the same holds for all its properties guarded by `balance > 1`).
* Benchmarks (31 properties): all decided with a budget of 120 s; see `results/v1_benchmarks.csv`.
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
  evaluated after the transfer" are detected; unit tests; end-to-end properties).
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
  and `tests/contracts`): 65 passed, 5 expected failures (the open properties of M4), 7 min 40 s.

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
  - benchmarks: 34 properties; all match except `vault_v3` non-inflation (formula, pending).
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
* Vault files: the same two properties for all mutants, with explicit increases (drainability:
  `∃d1, d2 : int`; non-inflation: `∀d1, d2 : int. d1 + d2 < wait_time -> ...`, any
  senders), exactly the formulae now in the paper (`tab-properties.tex`); a negative
  increase only makes the transaction revert, so no guard is needed.
  price-bet_v2 properties unchanged (all steps in one block).
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
* The Lustre output of all 104 existing properties is unchanged (compared before and after).
* Tests: front end (conversions, `%` on reals, real into int, pragma, warning), encoding
  (guard `<> 0.0`, `/`, literals, real balances), counterexample values; the Trans and
  formula differential tests now cover `tests/contracts/reals.sol` and
  `tests/contracts/real_balances.sol` (values: halves; real quantifiers: the integer domain
  and its midpoints). 15 new properties, all matching their ground truth with Kind 2 (20 s
  budget). With integer balances (the file without the pragma), `Split_is_fair` and
  `Small_payment` become invalid, as expected.

## After M5 — AMM and lending use cases, part 1: invariants (decisions 10–11 below)

* Experiments on a constant-product AMM in reals (contracts/amm/amm.sol, 8 properties): with
  Kind 2 on the transition system, 2 properties proved, 6 unknown after 30 s with both solvers.
  With Kind 2's default engines, nonlinear runs exceeded the memory: a run with a 3 GB cap,
  on a machine with 1.7 GB available, caused a global OOM (the editor was killed). Since
  commit 22dd6ff the cap is the smaller of 3 GB and half of MemAvailable.
* Diagnosis: properties hold because of invariants of the reachable states (nonnegative wallets and
  reserves), which Kind 2 does not find through nonlinear transitions. Checked on a free
  state with these invariants as premise, a property is a single SMT query: the swap-pool round
  trip is proved in 1 s, and the inductive step of the invariant in 0.8 s.
* New: `invariant` declarations, Houdini, checks on free states, BMC search for the state
  that refutes a property, portfolio strategy in rounds (DESIGN.md, Sect. 6); the runner
  reports when the memory limit killed a solver. Test contract `tests/contracts/swap_pool.sol`.
* Then: random testing with exact confirmation (`fuzz.py`), hoisting of universal
  quantifiers, invariants required after construction, Houdini per procedure and
  incremental, use cases `contracts/{amm,amm-simple,lending,lending-simple}` (DESIGN.md,
  Sect. 6). The batch of the 182 use-case properties with the final tool was stopped when the
  session ended (its log was in the scratchpad); to be rerun with logs in `runs/`.

## Planned (agreed with the user, 2026-10-06): better search for counterexamples

The search for the state s* that refutes a property on a free state (task 3 of the portfolio)
asks BMC for a state equal to s* in every field, through the whole Trans at every step;
in the runs so far it found 7 counterexamples, fuzzing most of the others. Plan, in this
order (experiments first, on the false lending properties still unknown, whose counterexamples
need about six specific steps; then implementation; then the 182-property batch, logged in
`runs/`):
1. Generalise s*: search only the fields read by the property (possibly the constraints of its
   premise instead of exact values), as IC3 generalises its counterexamples to induction.
2. Guided fuzzing: score reachable states by their distance to the target (s*, or the
   premise of the property) and extend the best traces first (hill climbing or evolutionary).
3. Symbolic search over fixed sequences of procedures: senders and arguments symbolic,
   one SMT query per sequence ("do these transactions reach a state where φ fails?"),
   built with the modality encoding (one procedure unfolded per step); sequences limited
   to the procedures that write the fields of the property, or proposed by the fuzzer.
4. Later, mostly for linear contracts: prove s* unreachable with k-induction or IC3 on
   `s ≠ s*` and add the invariants that Kind 2 prints to the assumed ones (refinement).

## Planned (2026-10-06): soundness gaps, certificates, invariant generation

Soundness gaps (DESIGN.md, Sect. 6):
* Forbid `lastReverted` in invariants (a reverted transaction changes the revert flag, which
  the step of Houdini does not cover), or cover reverted transactions in the step.
* Check the built-in facts once per file (balances nonnegative; fields of an unconstructed
  contract have default values) with the same initial and step checks, instead of assuming
  them.

Certificates (the tool should justify each verdict):
* invalid: the trace (replayable with the reference interpreter) and, at its last state,
  the values of the universally quantified variables that falsify the formula (from the
  model of the hoisted inputs), checkable by evaluation; when falsity at that state needs
  refuting an existential (e.g. "no attack succeeds"), an unsatisfiability proof.
* valid: the invariants C and the proof obligations as SMT-LIB files (initiation;
  consecution per procedure; the free-state query), each with a proof from a
  proof-producing solver (cvc5: Alethe, checkable with Carcara; or Kind 2's `--certif` and
  `--proof` (LFSC), to be tested); for verdicts of Kind 2 on the transition system, its own
  `--certif` certificate (a k-inductive invariant).
* To check: proof production for nonlinear arithmetic (cvc5 leaves trusted steps); the
  certificates are relative to our encoding, which remains trusted (paper's theorem,
  differential tests); a cheaper, weaker alternative is to re-solve each obligation with
  the other solver.

Invariant generation (today Houdini only selects among the invariants written by the user):
* Kind 2 generates invariants internally (template-based INVGEN engines on the terms of the
  program, IC3 lemmas; `--print_invs` exports them), but on the nonlinear use cases they
  exceeded the memory, they work on the quantified property as Kind 2 sees it, and their
  templates (equalities and orderings between pairs of terms) cannot express sums over the
  addresses (AMM Shares, lending Totals) or polynomial relations (lending Exchange_rate).
* Own generator of candidates for Houdini, from the contract: signs of numeric fields and
  map entries; zero entries for non-user addresses; positivity equivalences between fields
  (r0 > 0 ⇔ r1 > 0); sums of map entries against total fields (the addresses are finite);
  bounds by the constants of the contract; relations suggested by paired assignments
  (`m[s] += e; total += e`); possibly the invariants exported by Kind 2 on cheaper runs.
  Candidates first filtered on the reachable states of the fuzzer (as Daikon does), then
  proved by Houdini.
* Evaluation: does it rediscover the invariants written by hand in the use cases, and how
  many properties are then proved without user invariants?

Done (2026-10-07, commit 7772ac4; DESIGN.md, Sect. 6): `invgen.py` (templates, filter on
the fuzzer's states, `minimize` after Houdini), `sum(m)`, counterexample-guided Houdini
(one conjunction query per procedure), invariant phase per file. With the generated
invariants only (`--no_user_invariants`, 60 s per property, `runs/invgen_rules3.log`):
* AMM main: 135 templates, 31 after the fuzzer, all proved in 7.5 s; 8 of 10 properties proved,
  the same as with the invariants written by hand (which are proved as properties in 0.5 s);
  unknown: Sandwich, Arbitrage (existentials over reals).
* Lending main: 249 templates, 67 after the fuzzer, 61 proved in 47 s; 8 of 11 properties
  proved, the same as with the invariants written by hand (proved as properties in 0.6 s);
  unknown: Liquidation_defence, Liquidation_attack (false), Exchange_rate_monotone.
* Lessons: one property per candidate copies the inlined call into every property (71
  lending candidates not decided in 64 s; as one conjunction, 1-6 s per procedure);
  address quantifiers exclude null, so `m[null]` needs its own templates; minimizing before
  Houdini loses candidates implied by false ones; Houdini needs its own phase (inside the
  rounds of each property it did not finish on the lending protocol); runs killed by the
  memory limit must not count as undecided.
* Regressions and test contracts with the generator on (default; 30 s per property,
  `runs/regressions_invgen.log`): 84 of 90 properties match (82 before), no wrong verdict; the 6
  unknown are in the OPEN list of `tests/test_regressions.py`; the invariant phase takes
  0-13 s per file.

## Noted (2026-10-12, not planned yet): a portfolio of encodings for long budgets

Method quantifiers are expanded only while their nested copies are at most a bound
(`--expand method:N`, default 32; DESIGN.md, Sect. 2). Neither choice is better on every
property (30 s per property, 2 participants): with expansion, price-bet `Liquidity` (9.8 s) and
lending-simple `Liquidation_defence_exists` (3.7 s) are proved, and are not without it;
without expansion, two-donatees `P3c_true` is proved (10.3 s), and is not with it, and
lending-simple `Health_non_interference` takes 1.0 s instead of 3.0 s. With a long budget
(hours or days), the tool could try both encodings of the method quantifiers, in rounds
or in parallel, and possibly the other choices of the encoding (`--mode`, the expansion
of addresses).

Also observed: lending-simple `Liquidation_attack_any` (three free calls of the
attacker) is out of reach for now. In `inline` mode its encoding takes about 2 minutes
(24 MB) whatever the bound, because the state after a call of an unknown method, a case
split over all the methods, is substituted into the next modality. In `exists` mode the
encoding is small (178 KB without expansion), but Kind 2 exceeds 2 GB of memory within
30 s, also with the outer call expanded.

## Noted (2026-10-14): 3 and 4 participants

A short test (about 10 minutes, one job at a time, Kind 2 memory capped at 1 GB, 10 s per
property, portfolio strategy). Data in `runs/participants_*`.

- **Regressions** (additivity, args, liquidity4, mapping1, mapping2, owner, states;
  46 properties): all verdicts are correct for n = 2, 3 and 4, and every property is decided by the
  same method (24 by invariants, 20 by reach, 1 by fuzz, 1 by Kind 2). Total time
  70.6 s, 76.3 s and 77.6 s. Only liquidity4 `P12_true` slows down noticeably
  (0.7 s for n = 2, 3.7 s for n = 3 and 4). The invariant phase takes the same time.
- **bank** (4 properties): the three properties proved by invariants stay proved
  (No_frontrun_deposit 1.0 s for n = 2, 1.8 s for n = 4). `Liquidity` is unknown in both
  cases; within 10 s Kind 2 reaches depth 1 for n = 2 and no depth for n = 4.
- **Encoding size** (`--only_lus`): it grows linearly in n when the property has one address
  quantifier (bank `Liquidity`: 10.4, 12.3, 14.3 KB; liquidity4 `P12_true`: 4.6, 5.1,
  5.7 KB), and faster with nested ones (bank `No_frontrun_deposit`: 13.8, 21.1, 30.9 KB),
  as expected from the expansion of address quantifiers over all addresses.

Conclusion: on these properties, more participants do not change the verdicts and cost little
when the property is decided by invariants or by a short counterexample; the cost appears in
the properties left to Kind 2 (slower unrolling) and in properties with nested address quantifiers.
Not tested: properties whose counterexample needs 3 or more users (where n = 2 could miss a
violation), and the harder benchmarks (vault, price-bet, AMM, lending).

## Done (2026-10-14): parameterized mode (prototype, with the user)

Theory and design in DESIGN.md, Sect. 7. Option `--parameterized` (`kindHML.py`,
`run_all.py`); without it, the tool behaves as before (the 46 regression properties below: same
verdicts and methods, 69.7 s against 70.6 s). Code: `cutoff.py` (fragment and count),
`Checks.cutoff`, `Checks.sum_axioms`, ghost sums (`System.ghost_sums`, `encode_trans.py`),
`verify.effective_users`. Tests: `tests/test_cutoff.py` (the count on small formulas, the
cutoffs of bank and additivity, ghost sums against the reference interpreter on every
contract file, the guard of the sum axioms; with Kind 2, `tests/contracts/parameterized/
registry.sol`).

Experiments (10 s per property, one job at a time, Kind 2 memory capped at 1 GB; data in
`runs/parameterized_*` and `runs/normal_*_n100*`). Total time and correct verdicts:

| | n = 2 | n = 3 | n = 4 | n = 100 |
|---|---|---|---|---|
| regressions (46 properties), normal | 70.6 s, 46 | 76.3 s, 46 | 77.6 s, 46 | 457 s, 23 |
| regressions, parameterized | 62.1 s, 45 | 63.5 s, 43 | 64.3 s, 43 | 70.7 s, 43 |
| bank (4 properties), normal | 12.4 s, 3 | | 13.6 s, 3 | not finished (*) |
| bank, parameterized | 12.0 s, 3 | | 12.1 s, 3 | 12.1 s, 3 |

(*) The invariant phase does not finish in 42 s, the first two properties time out, and the
encoding of `No_frontrun_deposit` (two nested address quantifiers) did not finish in 6 min
with 1.5 GB.

- Cutoffs of the regressions: 1 (additivity, args, liquidity4, division, division2), 2
  (mapping1, owner, states, bank), 3 (mapping2, two-donatees, signature_error, bank_v3).
  Outside the fragment: additivity P1_true and P2_false, division P1_true and P2_false,
  division2 P2_false (an address quantifier after `exists` over numbers); they are checked
  with n users.
- The unknown verdicts are expected: args P0_false and owner P5_false (`exists a : address`,
  so a counterexample with c users does not extend; for args also with n = 2, since c = 1),
  owner P2_true (proved by Kind 2 only, for c users; the invariants method would need
  `is_EOA(owner)`).
- bank: the three properties proved with 2 users are proved for every n >= 2. `Liquidity` is
  unknown, as with 2 users; with the declared invariant `sum(funds) <= balance[Bank]`, it is
  proved for every n >= 2 in about 4 s, thanks to the sum axioms (without them: a
  counterexample to induction with `funds[u2] = 3 > balance[Bank] = 1`).
- registry (properties using `sum(registered) == count`): proved for every n >= 2 in 4.9 s for
  n = 2, 3, 4 and 100; with 100 users the normal mode times out on all properties (147 s).
  `At_most_two` (true only for n <= 2) is unknown in parameterized mode, for every n.

Not done yet:
- the larger benchmarks have larger cutoffs: vault 10 (its Houdini steps 5), lending 7
  (steps 5, one property outside), price-bet 5, AMM 4. The cutoff of a file is the largest over
  its properties; Houdini could use the cutoff of the steps, and each property its own (done, see
  "one number of users per check" below);
- counterexamples are searched for with c users only (a BMC of depth d needs up to
  d(1 + p) + w users);
- with c = n, ghost sums are weaker than exact sums: first trying exact sums with n users
  would keep the proofs for exactly n users.

## Done (2026-10-14): parameterized mode on bank, vault, price-bet; one number of users per check

**First batch** (one cutoff per file; 60 s per property, 60 s per invariant phase, Kind 2 at
1.2 GB, 100 users asked for; `runs/local-20261014-1313/parameterized_n100`, 33 min). All
13 verdicts agree with the ground truth, but only bank is decided (13 of 16 properties; vault 0
of 6, price-bet 0 of 12), against 32 of 34 in `results/v1_benchmarks.csv` (2 users,
120 s, 2 October). Causes: the price-bet and vault properties quantify `exists` over addresses,
so 6 counterexamples with 5 users and 1 with 10 do not extend (Lemma 7.5); their proofs in
the normal mode came from Kind 2 on the transition system, which do not transfer; the
vault cutoff 10 (one property) made its encodings slow (`non_inflation`: 172 s and 13.8 MB
with 10 users, 0.2 MB with 2), so its properties took 320-350 s despite the 60 s budget. One
Kind 2 run reported "Error opening input file" (vault.sol); it did not happen again on the
same program; the disk was 99 % full.

**One number of users per check** (DESIGN.md, Sect. 7.5, Prop. 7.7): each step of Houdini
uses the cutoff of its step for the current candidates; the check of a property the cutoff of
its premises; the search for a counterexample to induction the users of that check;
fuzzing and Kind 2 N = max(c_H, c_R). An `args` variable counts only the address
parameters of the procedures of the called contract other than the constructor (vault
`non_inflation`: 8 instead of 10; lending: 6 instead of 7). Experiments, with Kind 2 calls
counted by task and number of users (scratchpad script):
- regressions (46 properties, 10 s per property, 100 users asked for): verdicts unchanged (43
  correct, the same 3 unknown), 86 s; of the free-state property checks, 62 with 1 user, 5
  with 2; reach 21 with 1 user; Houdini 7 with 2 and 5 with 3; the 4 + 1 + 1 calls with 100
  users are the additivity properties outside the fragment;
- bank and bank_v3: the same 7 decided properties, e.g. "for every n >= 2 users; property checked
  with 1 user";
- vault and vault_v2 (60 s per property): Houdini 8 calls with 4 users and 8 with 5;
  `Two_steps_drainability` checked with 3 users (reach with 3, fuzzing and Kind 2 with 5),
  `non_inflation` with 8. The vault_v2 counterexample is found with 5 users in 17 s (75 s
  with 10), and still does not extend; `non_inflation` still takes 224-236 s (encoding with
  8 users). No new verdict on vault.

## Done (2026-10-14): extending counterexamples by symmetry (idle users)

DESIGN.md, Sect. 7.4, Lemma 7.6 (and Prop. 7.7, renumbered from 7.6). A user is idle in a
state if all its map entries have the default value and no address field holds it. A
counterexample with m users extends to every n ≥ m if its final state has at least
need(¬φ) users idle for the same balance (b = 0 if `sum(balance)` matters):
need is the largest number, over the branches of ¬φ, of the address variables up to the
last universal one (`Scanner.idle_needed`; 0 gives Lemma 7.5). Proof by symmetry: users
idle in every state of a branch can be exchanged, and the transactions over named users
leave the others idle.

Implementation (`verify.py`): the final state comes from the fuzzer, from the
counterexample of the reach search (now requested with its values: the counterexample to
induction may leave out values, e.g. balances that the property does not read), or from a
run of BMC after Kind 2 (on the program without lemmas: with them, Kind 2 waits for its
time limit). BMC and the fuzzer give arbitrary initial balances to the users (price-bet_v4
`Liquidity`: 0, 47482, 22317), so the users outside the trace get initial balance 0, and the
property is checked exactly at the new final state. These confirmations get 10 s each
(`CONFIRM_SECONDS`), also after the time limit. A counterexample that does not extend no
longer ends the search: the other tasks go on. Tests: `tests/test_cutoff.py` (the count, the
idle users, the participants of a counterexample; with Kind 2,
`tests/contracts/parameterized/capped_registry.sol`: a counterexample that extends, and one
that must not, for a property true with 3 users).

Results (100 users asked for; data in `runs/local-20261014-1532-idle2` and
`runs/parameterized_idle_reg_n100.*`):
- regressions (10 s per property): 45 of 46 correct (43 before); args P0_false and owner P5_false
  are refuted for every n ≥ 1 and n ≥ 2. The only unknown is owner P2_true, proved by Kind 2
  only;
- price-bet and vault_v2 (60 s per property, 12 min): all 7 false properties are refuted, for every
  n ≥ 5 (n ≥ 4 for price-bet_v3 Frontrunning), as by the normal mode with 2 users (none
  before, with one cutoff per file; 3 before the balances were set to 0). The 7 true properties
  are unknown: their proofs with 2 users come from Kind 2 on the transition system, which do
  not transfer, and the checks on free states lack invariants.

## Done (2026-10-14): reserve templates; Kind 2 with more users (with the user)

- **Reserve templates** (`invgen.py`; DESIGN.md, Sect. 6): `sum(m) == balance[C]` and
  `sum(m) <= balance[C]` for each numeric map m and contract C. On bank (parameterized, 5
  users asked for, 60 s per property), Houdini proves `sum(funds) <= balance[Bank]` and the
  four properties are proved for every n >= 2 in 5.5 s in total (`Liquidity` was unknown).
- **Proofs by Kind 2 with fewer users** (DESIGN.md, Sect. 7.5, Cor. 7.8). A proof by Kind 2
  with m users holds for every n <= m if need(¬φ) = 0 (contrapositive of Lemma 7.5);
  otherwise for m only. It was ignored when m = N < n; now the outcome is unknown, "true up
  to m users" (ground truth `OK-up to m users`), and Kind 2 goes on with m + 1 users, up to
  n. The other searches for counterexamples stop after the first such proof (none they
  find would extend to n). Results (parameterized mode):
  - bank `Liquidity`, 5 users asked for, 60 s, before the reserve templates: "unknown, true
    up to 2 users" in 36 s (before: "unknown" after 64 s; Kind 2 had proved it with 2 users
    in 21 s). With `--no_invgen`, 4 users, 150 s: true up to 2 users; with 3 users, Kind 2
    reaches 5 steps;
  - registry `At_most_two` (`count <= 2`), 3 or 5 users asked for: invalid, "counterexample
    with 3 users, for every n >= 3; true up to 2 users", in 25-27 s (before: unknown). Test:
    `tests/test_cutoff.py::test_kind2_with_more_users`.

- **Status (2026-10-14, interrupted; committed with the open issue below).** `tests/test_cutoff.py`: 74 passed.
  Full suite (`-m "not slow"`, 22 min): 8 failed. Rerun one by one, against HEAD (70d8b1d):
  - `test_trans_kind2[lending*]` (4): the Kind 2 memory limit (1016 MB) killed a process;
    the test uses neither `verify` nor `invgen`, so unrelated to this change (not rerun);
  - `test_regression[calls-Pay_zero_reverts]`: passes on rerun (on both trees);
  - `test_regression[swap_pool-Inv]`, `[swap_pool-Swap_reversibility]`: fail on HEAD too
    (unknown within the budget); with this change, "true up to 3 / 2 steps";
  - `test_invariants.py::test_portfolio_on_the_swap_pool`: status "error" with this change,
    "unknown" on HEAD (expected "valid" in both). Resolved on 2026-10-15, see below.
  Next: rerun the regressions in parameterized mode (100 users) and the use cases (AMM,
  lending: time of the invariant phase with the new templates).

## Done (2026-10-15): the first pass of Houdini (with the user)

- **Cause of the swap_pool failure.** It fails on every commit since 7772ac4 (generated
  invariants); "error" or "unknown" depends on the run (whether Kind 2 reports a bound
  before its time limit), not on the reserve templates. Two causes:
  - a pass of Houdini (`_Invariants.attempt`) started a program only with at least
    min(budget, FIRST_BUDGET) s left. In the first round of `verify` the budget is
    FIRST_BUDGET, so the pass started none; later passes stopped with 4 s left, for steps
    of 0.5 s. When Houdini runs in the rounds of the properties (`verify` without the invariant
    phase, as in the tests), it waited one round, which Kind 2 used without a verdict
    (16 s, then 32 s): Inv had no verdict within 60 s;
  - the test expected the proved invariants without the generated ones, and the message
    "inductive step" without the procedure.
- **Fix.** A program starts when more than 1 s is left, as the checks of `verify`. The test
  compares the declared invariants only; new test `test_first_houdini_pass_runs` (it fails
  without the fix). Swap pool: Inv proved by Houdini in 24 s (before: no verdict in 60 s);
  Swap_reversibility in 1.5 s (before: 20 s). The command line and `run_all.py` run the
  invariant phase first, where only the first pass was lost.
- **Suite** (`-m "not slow"`, 24 min, log `runs/suite-20261015-1321.log`): 382 passed, 3
  failed, 5 xfailed, 3 xpassed. `swap_pool-Inv` and `swap_pool-Swap_reversibility` pass,
  and the four `test_trans_kind2[lending*]`. The 3 failures are on `calls`, while Firefox
  left about 0.9 GB available (Kind 2's limit is half of it). Rerun: `Report_sees_balance_at_call_point`
  and `Pay_zero_reverts` pass; `Buy_mints` is at the edge, with or without the fix (3 of 6
  runs pass with it, 2 of 7 without): Kind 2 proves it (ind2) in its first run of 16 s or
  not, depending on the processes killed by the memory limit.

## Done (2026-10-19): the bound of the sum of all the entries (with the user)

Analysis of `results/n5.csv` (5 users) and `results/parameterized_n100.csv` (100 users,
parameterized), both run on the server.
- Without parameterized mode, the universal properties of the AMM (amm_simple Sandwich,
  No_money_pump, Swap_additivity, ...) are unknown with 5 users: the check on a free state
  expands the address quantifiers into one query (36 nonlinear cases for Sandwich); z3 and
  cvc5 give no answer in 60-90 s, while each case alone is valid in at most 1.4 s, and the
  whole check with 2 users in 2 s. Parameterized mode checks them with 1 or 2 users: valid in
  under 6 s, for every n >= 3.
- With parameterized mode, amm-real and amm-int lost Nonnegative, Shares (inductive in
  n5.csv) and LP_exit: the sum axioms bounded single entries and pairs only, and the step of
  `redeem` for Shares needs 3 users (DESIGN.md, Sect. 7.3).

Changes:
- `Checks.sum_axioms`: the sum of the entries at all the addresses is at most σ_m (it
  replaces the bounds of single entries and of pairs);
- `nonnegative_maps`: also conjuncts of the premises, at the top and under the `forall`;
- `Checks.refuted_after`: the replay keeps the sums of the free state (`State.sum_offsets`,
  `state_from_values(..., free_sums=True)`); before, it could refute a true candidate such as
  `sum(minted) == supply`.
- Tests (`tests/test_cutoff.py`): the axiom, the conjuncts, the replay;
  `tests/contracts/parameterized/shares.sol` with Kind 2 (the test fails with the old axioms).

Results (5 users, parameterized, 120 s per property and per invariant phase;
`runs/axiom_amm`): the 15 properties of amm-real and amm-int lost in parameterized_n100.csv
are valid (Nonnegative and Shares inductive, LP_exit by invariants in under 1 s); the
invariant phase takes 44-71 s per file.

## Done (2026-10-19): the combined mode (default), and every number of users (with the user)

Decided with the user: `--users_mode combined|exact|parameterized`, default `combined`
(`--parameterized` is `--users_mode parameterized`); the number of users also accepts `any`,
a verdict for every n >= 1 (DESIGN.md, Sect. 7.6).
- `verify.py`: the body of `verify` is the generator `_rounds` of a side (one number of
  users), which yields after each round; the drivers `_drive_one`, `_drive_combined`,
  `_drive_any` advance the sides one round each in turn (one Kind 2 job at a time). In
  combined mode the parameterized side only proves (Houdini, the check on a free state);
  the exact side searches for counterexamples and runs Kind 2, with all the time left once
  the other side has ended. `prove_invariants` returns the Houdini of each number of users
  of the mode, in alternating passes. `kind2_target` gives the Lustre of `--only_lus`.
- `kindHML.py`, `run_all.py`: `any`, `--users_mode`; a column `scope` in the CSV;
  `run_experiments.sh` uses `--users_mode exact` (the tables of the paper).
- Tests: `tests/test_users_modes.py` (the drivers with scripted sides), Kind 2 tests in
  `tests/test_cutoff.py` (combined mode and `any` on the registries, `any` without a cutoff).

Results (one job at a time, 1 GB):
- regressions (64 properties, 3 users, 10 s per property; `runs/users_mode_reg_n3_*`): exact
  55 correct, combined 54 (two-donatees `P3b_false`, refuted by Kind 2 in 10.2 s in exact
  mode, is unknown), and 24 of the proofs hold for every n from the cutoff on. A first
  version, whose parameterized side also searched for counterexamples, took the first 7 s
  of owner `P2_true`, and lost it.
- amm_simple and bank (5 users, 120 s per property; `runs/combined_n5_amm_simple_bank`):
  10 of 13 correct, all proofs for every n from the cutoff on (amm_simple Sandwich in 3.9 s,
  Swap_additivity and No_money_pump in 0.7 s; unknown after 600 s in results/n5.csv). The 3
  unknown are the properties with an existential witness (Sandwich_slippage,
  Swap_reversibility, Arbitrage_exists), as in n5.csv.
- `tests/test_regressions.py` (default mode, 2 users, 30 s): 80 passed, 7 xfailed, 1 xpassed,
  2 failed: calls `Buy_mints` and `Report_sees_balance_at_call_point`, valid in about 24 s or
  unknown depending on the run, also in exact mode and at the previous commit 5312cdd (Houdini
  ends at about 29 s in the rounds of the property); added to OPEN.

## Done (2026-10-22): witness premises of the sums; regressions for every n (with the user)

Pool `Someone_deposited` (`total == 0 || exists a . deposit[a] > 0`, with the invariant
`sum(deposit) == total`; `contracts/regression/pool.sol`) holds for every n, but was unknown
for every n: in the check with the cutoff, σ_deposit is free, and the counterexample to
induction has every entry of the system 0 and σ = total = 1 (a depositor outside the system).
- `Checks.witness_axioms`, `witness_maps` (DESIGN.md, Sect. 7.3): the premise "if the entries
  at null and at the contracts do not add up to σ_m, a user has a nonzero entry", for the sums
  of the contracts, of the property and of its premises; one more user per sum.
- `_rounds`, task "invariants": after the checks without them, the checks with the witness
  premises, if their users fit in the cutoff of the side (decided with the user): no cutoff
  changes (the cutoffs of the 328 properties of the benchmarks and regressions are the same
  as at c0e341d). With the premises of all the sums in every check, the cutoffs of 110 of 277
  benchmark properties would grow (lending: from 4–6 to 7–11 users).
- Pool `Someone_deposited`: valid, "n >= 2 by invariants, n < 2 one by one" (1.5 s).
- `tests/test_regressions.py`: every number of users by default (decided with the user),
  `--users N` for N users (`tests/conftest.py`); `OPEN_ANY` (additivity P1_true and features
  Trivial, without a cutoff; owner P2_true, whose proof with the cutoff needs `owner != C`),
  and `LONGER_ANY`, 180 s for 6 properties decided in 45–88 s for every n (the invariant
  phases of the checks with the cutoff and with 1, 2, ... users share the time).

Results (`pytest -m kind2 tests/test_regressions.py`, 30 s): every n, 80 passed, 12 xfailed,
1 xpassed (18 min); `--users 2`, 83 passed, 8 xfailed, 2 xpassed (12 min). The first run for
every n, with 30 s for all: 74 passed, 9 failed, none with a wrong verdict.

## Done (2026-10-22): address templates (with the user)

The proofs with the cutoff of owner `P2_true` and of the price-bet properties failed on
counterexamples to induction with `owner = C`, `oracle = Bet`, or `player = null` after the
join: the templates only gave `a != null`. New templates, chosen with the user (no cap), for an
address field a, an address constant K (null or a contract) and a boolean field g: `a == K`,
`a != K`, `g -> a != K`, `!g -> a != K`; `minimize` drops `g -> a != K` given `a != K`, and both
given `a == K'` (K' ≠ K). They add at most 21 templates per benchmark file (price-bet; vault 9,
lending 3, AMM and bank none); they have no address quantifiers, and the cutoffs of the 328
properties are unchanged.

Results:
- price-bet, every n, 120 s: the 12 properties match (the 6 true ones, "true up to 6-8 users"
  after 600 s in `results/new.csv`, are valid in 0.5-3.7 s, "n >= 5 by invariants"); invariant
  phase 21-34 s per file.
- owner `P2_true` (every n) and two-donatees `P5_true` are valid by invariants in 0.5 s (P5 was
  proved by Kind 2 in 9 s, at the edge of the timeout): both removed from the open lists.
- `pytest -m kind2 tests/test_regressions.py`: every n, 81 passed, 10 xfailed, 2 xpassed
  (17 min); `--users 2`, 83 passed, 8 xfailed, 2 xpassed (11 min).
- Invariant phase, parameterized mode, 900 s: vault 8 s as before (6 proved, 5 before);
  lending-real does not end, as before; lending-int ends in 808 s (it did not end before): at
  the edge of the limit both times, so no conclusion on the cost there.

## Noted (2026-10-23): the cluster runs before and after 2026-10-22 compared (with the user)

Files:
- `results/cluster-20261021-2221.csv`: started on 2026-10-21 at 22:21, so probably at
  7454e3f;
- `results/cluster-20261022-2304.csv`: at 9d91616 (= origin/v1).

Every number of users (the default), 600 s per property. The two files have the same 157
rows: amm-int 12, amm-real 60, amm-simple-int 9, amm-simple-real 36, bank 16,
lending-simple-real 6, price-bet 12, vault 6. lending-int, lending-real and
lending-simple-int are missing from both.

Commits between the runs:
- dd30672: guided fuzzing;
- c0e341d: a Kind 2 run stopped at a limit is unknown;
- 2e69b3e: witness premises;
- 9d91616: address templates;
- efd3104, 75b8cbf: no effect on these rows.

Only the files were compared; nothing was rerun.

Verdicts: no wrong verdict in either run, and no row has a weaker verdict.
- 115 rows are correct in both.
- 8 rows go from "true up to 4–8 users" (600 s) to valid for every n, in 2.5–19 s:
  - price-bet `Winnability` (v1, v4), `Liquidity` (v1, v3), `Frontrunning` (v1, v2);
  - vault and vault_v3 `Two_steps_drainability`.

  The cause is the address templates: vault has no sums, so the witness premises cannot
  apply there.
- 5 rows go from "error" to "unknown, true up to 1–5 users", with the same scope (c0e341d):
  amm_real `Sandwich_slippage`; lending_simple_real `Health_non_interference` and
  `Liquidation_defence_exists`; vault and vault_v2 `Two_steps_drainability_non_inflation`.
- 4 rows are partial in both: `Sandwich_slippage` of amm_real_v2, amm_real_v5,
  amm_simple_real and amm_simple_real_v2, true up to 1 user.
- 25 rows are unknown in both, all AMM: `Arbitrage_exists`, `Deposit_reversibility`,
  `Swap_reversibility`, and `Sandwich`/`Sandwich_slippage` of some versions. Two of them
  went from "error" to "unknown".

Times of the 115 rows correct in both: 1276 s before, 1830 s after. About 500 s of the
difference comes from three refutations by fuzzing:
- amm_real_v4 `Swap_additivity`: 34.7 s (Kind 2), now 116.5 s (fuzz);
- amm_real_v4 `Swap_reversibility`: 40.3 s, now 177.0 s (fuzz);
- lending_simple_real `Liquidation_attack_exists`: 193.7 s (3 users), now 474.2 s (2 users).

price-bet_v4 `Frontrunning` went from 18.6 s (Kind 2) to 3.5 s (reach).

Hypotheses on the slowdowns (not tested):
- the two AMM rows: the witness checks apply there. A static count, with all the candidates
  as premises, gives 3 sums and 4 users, within the cutoff 4. With nonlinear arithmetic
  they may time out in each round and take time from fuzzing and Kind 2. Besides, dd30672
  gives half of the fuzzing time to the search guided by s*.
- the lending row: the witness checks do not apply there (8 users, cutoff 4), so the cause
  is the guided fuzzing or the scheduling.

Possible next steps (not started; the user decides):
1. **Witness checks only when they can help.** Run them only after a counterexample to
   induction s* that violates a witness premise: σ_m ≠ Σ_F m and every shown user has
   entry 0, as in Pool. Otherwise s* satisfies W, and W cannot exclude it. This is sound,
   since checks are only dropped, and it would remove the cost on real counterexamples
   such as the AMM ones. s* is computed now only when the strongest plain check is invalid.
2. **Targeted reruns, to separate the causes.**
   - The three slow rows at 9d91616, with and without the witness checks.
   - The same rows at 75b8cbf and at dd30672.
   - The families missing from the runs, to evaluate the guided fuzzing (the families
     whose false properties were unknown: lending-real, lending-int, amm-int,
     amm-simple-int).
3. **Templates not added yet.**
   - Comparisons between two address fields (`a == b`, `a != b`): offered, not chosen.
   - Conservation invariants with constructor arguments, as on lending-simple-int:
     `sum(w0) + res0 == s0`, where s0 is a constructor argument, and
     `res0 + sum(debt) == sum(c0)`. Both counterexamples to induction printed there violate
     them.
4. **Witness premises.** They could also go in the steps of Houdini, and a sum could get
   more than one witness. No case needs either yet.
5. **Performance with many users.**
   - In parameterized mode, Houdini on lending-real does not end in 900 s, with or without
     the address templates.
   - The encoding time grows fast with the users: vault
     `Two_steps_drainability_non_inflation` takes 0.4 s with 1 user and 41 s with 7.
   - Integer lending is hard for z3: lending-simple-int `Nonnegative` has no verdict with 3
     users at 60 s, while the real version is inductive in 0.01 s.
6. **The 25 + 4 AMM rows without a full verdict.** Not analyzed in these sessions. The true
   ones (`Arbitrage_exists`, `Deposit_reversibility`, `Swap_reversibility`) have
   existential witnesses over numbers.
7. **The scope "nor with the cutoff c"** reads like "with c users" to the user. Proposed
   wording: "nor by invariants for every n (cutoff c)". Not decided.
8. **27 failures of the Kind 2 tests of `tests/test_trans.py`.** They were already there on
   2026-10-21, with the same Lustre programs at the previous commit. Kind 2 reports a parser
   error or no result. Not investigated.

## Done (2026-10-23): a hard limit per task in `tests/run_all.py` (with the user)

The cluster runs of 2026-10-21 and 22 stopped after lending_simple_real
`Liquidation_attack_exists`: the next task, `Liquidation_attack_any`, never ended. The time
limit of `verify` is only checked between the steps of a round, and one step, the encoding of
this property (three nested `exists f, args . <<a : f(args)>>`), does not end (see the next
section). Kind 2 is not involved: its runs stop at their limit.

Each task of `run_all.py` now runs in a forked child, stopped at `--task_timeout` (default
2 x `--timeout` + 300 s): SIGTERM, on which `kind2.run` stops Kind 2, then, after 30 s,
SIGKILL for the child and its Kind 2 runs (`kind2.kill_runs`). A stopped task is "unknown",
with the scope "stopped at the limit of the task". The child sends back the progress of
Houdini (`verify.houdini_progress`, `resume_houdini`), so the next tasks of the file go on
from it, as before; the Houdinis that a task creates (more users) are not sent back.
`--families` now rejects a name that matches no selected file (the cluster command had
`lending-simply-real`, so lending-simple-int never ran).

## Planned (2026-10-23): the encoding of nested modalities (not started; the user decides)

Measurements (lending_simple_real, encoding only, no Kind 2):

| Property | `lustre_for`, 1 user | free-state check (`Checks._property`), 1 / 2 users |
|---|---|---|
| `Liquidation_attack`, `Liquidation_attack_exists` (1 modality) | 0.0 s | 0.0 s / 0.1 s |
| copy of `Liquidation_attack_any` with 1 modality | 0.5 s | 0.4 s / 1.0 s |
| copy with 2 modalities | 2.5 s | 2.4 s / 11.5 s |
| `Liquidation_attack_any` (3 modalities) | > 600 s | > 300 s / not run |

`Liquidation_attack_any` in the other modes: `levels` 22.8 s (1 user), > 60 s (2 users);
`exists` 0.1 s, 0.3 s, 0.6 s (1, 2, 3 users). The profile of the copy with 2 modalities: 43% in
`free_vars`, called by `quantify` on the whole body at every quantifier, and most of the rest
in `Inliner.run`. With 1 user the premise `a != b` is false for every pair, so the property is
trivially true, but the body is encoded before the simplification removes it.

Cause (hypothesis to confirm in step 1): in mode `inline` (the default), the next state of a
modality is a term, substituted without sharing into the nested modalities, so the work grows
multiplicatively with the depth; `quantify` adds a traversal of the body per quantifier.

Steps:
1. **Measure.** The number of nodes of the terms per depth, with and without sharing (by
   identity), and the time of `free_vars`, `Inliner.run` and the equality tests of the
   simplifications, on the three properties above.
2. **Changes that keep the formula.**
   - `free_vars` cached by node identity, or computed once bottom-up (the nodes are frozen
     dataclasses, whose hash traverses the whole tree, so not by hash).
   - An implication whose premise simplifies to false is encoded as true without encoding
     its conclusion (the premise first). This removes the whole cost with 1 user here.
   The Lustre output must stay the same: compare it, character by character, on all the
   benchmark and regression properties, before and after.
3. **Structural change (a hybrid mode).** From a bound on the depth or on the size of the
   term on, a modality gets fresh existential state variables, as in mode `exists`, instead of
   the substituted term. This is equivalent, since Trans is a function (Lemma
   `lem:transition`), and both forms exist already. The cost for Kind 2 of the quantified
   states is not measured: compare the Kind 2 times on the regressions and on the benchmark
   rows with nested modalities (`Sandwich*`, `Two_steps_*`, `Liquidation_*`), and choose the
   bound from these data, not a priori.
4. **A deadline in the encoder** (the third option of 2026-10-23). `verify` passes its deadline
   to the encoders, which stop past it; the round ends without a verdict. The time limit of a
   check then holds without the child processes of `run_all.py` (e.g. for `kindHML.py`).
5. **Validation.** The differential test of the formula encoding (`pytest -m slow`), the
   regressions (`pytest -m kind2 tests/test_regressions.py`), `Liquidation_attack_any` with
   600 s, and the lending families on the cluster.

## Done (2026-10-23): existentials over numbers decided by z3 directly (with the user)

Analysis of `results/cluster-20261022-2304.csv` (34 rows without a full verdict): 29 are AMM
properties with an existential over a number (Swap_reversibility, Deposit_reversibility,
Arbitrage_exists, Sandwich_slippage; 21 true, 8 false), none decided in 600 s, while the same
properties with an explicit witness are proved in seconds. The others: vault
`Two_steps_drainability_non_inflation` x2 (cutoff 8: the check with the cutoff has 9(n+1)^3 cases,
6561), lending `Health_non_interference` (cutoff 6, 456 cases), lending
`Liquidation_defence_exists` (no cutoff: an address existential under a universal), amm_real_v4
`Sandwich` (its counterexample to induction loses the value of x).

Cause (measured on the check of amm_simple_real `Arbitrage_exists` with 1 user; DESIGN.md Sect. 6,
"Existentials over numbers"): nlqsat rejects the query because of divisions and if-then-else terms
under the quantifier, and Kind 2's `check-sat-assuming` keeps z3 away from nlqsat anyway. After
two rewritings under the quantifier, asked once, z3 decides it in 0.02 s.

Changes:
- `src/kindhml/direct.py`: translation of a node property into z3, check that divisions are
  guarded, rewriting into pure real arithmetic, z3 run in the memory scope
  (`kind2.run_command`, factored out of `kind2.run`), models;
- `Checks.property_goals`, `direct_queries`, `concrete_goal`;
- `_rounds`: with `fuzz.has_witness`, a direct attempt first for each premise set, split into
  cases (proved cases kept across rounds); a refuted case gives s* (state variables of the check)
  and the values of the universal variables; the exact checks of the fuzzer and of `normalized`
  go to z3 directly first;
- tests: `tests/test_direct.py`, `tests/contracts/swap_witness.sol`.

An adversarial review (agents) found an unsound case, fixed with a regression test: `check_guards`
compared guards and divisors across quantifiers by de Bruijn index, so `exists v . v != 0 &&
exists w . (w = 0 && 1 / w = 5)` was reported valid. Also fixed: division by the numeral 0, the
exact check of `normalized` through Kind 2 only, an irrational universal value that discarded s*.

Results (every n, 120 s per property, one job at a time, 1 GB; `runs/direct_amm_simple*`,
`runs/direct_amm_real`): 19 of the 21 true rows valid (most in under 5 s), 4 of the 8 false rows
refuted. Still unknown: amm_real `Sandwich_slippage`, amm_real_v3 `Deposit_reversibility`, and the
false `Sandwich_slippage` of amm_simple_real_v3, amm_real_v3, _v4, amm_int. amm_int
`Swap_additivity` (integers, outside the new path): refuted in 88.6 s before and 91.5 s after.

## Done (2026-10-24): the rest of group 1 (with the user)

The 6 rows left (300 s; `runs/group1_open_300`): amm_real `Sandwich_slippage` valid in 169 s and
amm_real_v3 `Sandwich_slippage` refuted in 199 s (time only). For the others, measured with
logs of the rounds (`direct_check`, searches, exact checks):
- amm_real_v3 `Deposit_reversibility` (true): its s* has supply = 0, r0 = 0, r1 = -1 (the linear
  price of v3 makes reserves negative, so the sign templates fail). With `supply == 0 -> (r0 == 0
  && r1 == 0)` declared, Houdini proves it and the property is valid in 0.4 s: new template
  `f == 0 -> g == 0` (`invgen.py`; `minimize` drops it when implied by `g > 0 -> f > 0` and
  `g >= 0`).
- amm_simple_real_v3 `Sandwich_slippage` (false): alone, the fuzz loop with direct exact checks
  finds a counterexample in 12 s (13 checks); in the rounds, a search gave 3 candidates per round,
  about 6 checks in 300 s. A search is now repeated until its time is over.
- amm_real_v4 `Sandwich_slippage` (false): s* found at 77 s, but the guided search got 1-2 s per
  round (one budget for fuzzing, a quarter for it), returned no candidate (the bounded evaluation
  rejected the states near s*), and an undecided exact check took 14 s. Changes: fuzzing and Kind 2
  swap their shares, the guided search proposes the closest states without the filter, an exact
  check by z3 takes at most 5 s, the direct attempt gets the time of the two Kind 2 forms it
  replaces, and its cases rotate.
- amm_int `Sandwich_slippage` (integers): still unknown; outside `direct.py`.

Results (all 29 rows, every n, 300 s; `runs/group1_all_300`): 28 correct (21 valid, 7 refuted in
5-240 s); amm_int `Sandwich_slippage` unknown.

## Done (2026-10-24): group 2, reduction by symmetry of the checks on free states (with the user)

Group 2 of the analysis of `results/cluster-20261022-2304.csv`: vault and vault_v2
`Two_steps_drainability_non_inflation` (cutoff 8) and lending_simple_real
`Health_non_interference` (cutoff 6), no verdict in 600 s. The check with the cutoff of the vault
property has 9 (n + 1)^3 cases (6561 with 8 users); most are the same up to a renaming of the
users.

Change (DESIGN.md, Sect. 7.7): in the property of a check on free states and in the conclusion of
a step of Houdini, a universal address quantifier in positive position (through conjunctions,
conclusions of implications, universal quantifiers and inline modalities) ranges over the
contracts, the users bound around it and one more user; `KINDHML_SYMMETRY=0` turns it off. The
vault check then has 135 cases for every n >= 3 (1.3 s of encoding with 8 users).

Soundness:
- my design first reduced through disjunctions; I found it unsound before implementing it
  ((∀a. m[a] > 0) || (∀b. m[b] <= 0), valid if b is chosen like a): the reduction stops there;
- an audit by an independent agent found that the terms of a modality (a quantified boolean
  argument) were reduced, and gave a false property that the reduced check proved; confirmed
  with a test that failed before the fix; fixed (terms are encoded without the reduction);
- tests: `tests/test_symmetry.py` (patterns, where the reduction stops, two solver tests).

Results (every n, 300 s; `runs/group2_300`): the 3 rows valid, "n >= 8 (or 6) by invariants,
fewer users by the proof with 8 (or 6) users": vault 29.4 s, vault_v2 27.6 s, lending 7.0 s.

All 157 rows of the cluster run, every n, 120 s per property (against 600 s there;
`runs/cluster_rows_120`): 150 correct, against 123. A regression of ff17998 showed up:
amm_int `Deposit_reversibility` (integers), refuted in 34 s before, unknown. Bisected with copies
of the code: the guided search ran without its filter until the first exact check found the
direct path inapplicable. Fixed: the filter is dropped only once a direct check (exact, or on
free states) has applied; refuted in 34.9 s again, and amm_real_v4 and amm_simple_real_v3
`Sandwich_slippage` still refuted (152 s, 57 s at 300 s). Not decided at 120 s, decided in the
cluster run in more time: amm_simple_int `Sandwich_slippage` (178.6 s) and lending_simple_real
`Liquidation_attack_exists` (474 s); rerun with the fix, amm_simple_int `Sandwich_slippage`
refuted in 230.8 s (300 s limit; integers, outside the direct path) and lending_simple_real
`Liquidation_attack_exists` in 132.4 s (600 s limit; by a direct exact check).
lending_simple_real `Liquidation_defence_exists` (no cutoff) true up to 3 users (5 in 600 s).

## Done (2026-10-24): server for the experiments; methods kind2-<ENGINE> (with the user)

- From now on, every run of a solver (tests included) is on the server (SERVER.md, Sect. 7;
  scripts in `tools/server/`, uncommitted with SERVER.md: they contain the server address).
  Self-tests: same verdicts with 1 and 4 shards (34 tasks), regressions in 4 min with 6 shards.
- 54efdf0: a verdict of Kind 2 has the method `kind2-BMC`, `kind2-IND`, ... (its engine).

## Done (2026-10-24): milestone B, the encoding of nested modalities (with the user)

Plan of 2026-10-23 (above). Measured on the server (`experiments/nested/`):
- the next states of the copies `Any1-3` of `Liquidation_attack_any` (tests/contracts/nested/
  any.sol) have, as trees, 4,200 / 375,000 / 31 million nodes (2 users); building them takes
  1-2 s (shared in Python), the traversals and the Lustre text do not end;
- the largest input of a nested modality, over all the properties with nested modalities (2 and
  6 users): 37,000-3.3 million for `Liquidation_attack_any`, at most 14,800 for the others.
Changes (DESIGN.md, Sect. 2, mode inline): a next state that a nested modality whose method is
a variable takes as input gets variables s' (s' = next state) above 5,000 nodes, any other above
10^6; s' is universal (∀s'. s' = t → body), so that it is hoisted in positive position;
`free_vars` memoized by identity; the encoders stop at the time limit of the check
(`EncodingTimeout`).
Results (server, 5 shards, 300 s; runs/server/nested-head, nested3, nested4):
- `Liquidation_attack_any` (9 rows) ends at its time limit (unknown) instead of hanging;
- a first version bound every input of a nested modality above 5,000 nodes, the AMM `Sandwich*`
  inputs included: two refutations close to the limit got slower (at 600 s: amm_real_v4
  `Sandwich` 238 s, 308 s with ∃s', unknown with ∀s'; amm_simple_int `Sandwich_slippage` 234,
  381, 384 s), others faster, the lending rows unchanged (all unknown). Hence the restriction to
  modalities whose method is a variable: no AMM property is bound;
- the Lustre texts of all the other properties (361 checks of the families and the regressions,
  `experiments/nested/lustre_hashes.py`) are identical to those of 54efdf0, so their verdicts
  do not change;
- with the bounds disabled, a check of Any3 did not stop at its limit (636 s for 20 s): the
  inlining of the transitions (`lustre_subst.Inliner.run`) did not check it; it now does;
- tests on the server: all pass but `test_trans.py::test_trans_kind2` (31 cases), which fails at
  54efdf0 too: the server's Kind 2 (v2.3.0-ge8216dd) rejects the map arguments of its check node
  (a parser error), not the tool's programs.

## Done (2026-10-24): milestone C, the universal values of a counterexample to induction

Group 4 of the analysis of cluster-20261022-2304 (amm_real_v4 `Sandwich`): the guided fuzzer
evaluates the property on a fixed domain of numbers, which misses the small amounts of the
counterexample. The values of the universal variables of the counterexample to induction s*
(inputs `q_x_k` of the check, from z3's model or from Kind 2's counterexample:
`verify._input_values`, `_stream_inputs`) are now tried first by the bounded evaluation of the
guided search (`Fuzzer.guided(values=...)`; `reference._of_type` converts them to the type of
the quantifier). Tests: `tests/test_guided_values.py` (a crafted property whose counterexample
needs x = 1/1000). Results (server, 32 rows with nested modalities, 300 s, 5 shards; runs/server/cd3 against
runs/server/nested-head, 54efdf0): amm_real_v4 `Sandwich` refuted by fuzz in 13.5 s (by reach in
234 s before); the other verdicts unchanged, all in agreement with the ground truth.
amm_simple_real_v4 `Sandwich_slippage` took 111 s (57 s before): rerun 3 times each under the
same load, it takes 105 s with B and C, 105 s with B only, 53 s at 54efdf0. Not a regression of
B: the guided search gives a number of candidates per round that depends on the time of the
checks, so the counterexample found, and the round, depend on timing. Under cProfile, 54efdf0
took 211 s (a counterexample of 2 steps) and B 56 s (13 steps); B encodes faster (0.07 s per
call of `FormulaEncoder.prop` against 0.39 s, the memo of `free_vars`).

## Done (2026-10-24): milestone D, candidate witnesses of existentials over methods

Group 3 (lending-simple-* `Liquidation_defence_exists`, no cutoff). DESIGN.md, Sect. 7.8:
`witness.instances` (instances with procedures and terms of the state; only when the modalities
of the method variable are at the state of the existential, and no quantifier captures a
variable of the terms) and a side of `_drive_any` (`verify._witness_rounds`) that checks the
instances with a cutoff and no idle user on a free state, one per Kind 2 run. Measured on
lending-simple-real (`experiments/witness/`): the 64 instances all have cutoff 4 and need no
idle user; in one Kind 2 run, none was decided in 300 s; one at a time, each in 0.5 s (63
refuted, `repay(debt[a])` proved): the property is proved for every n in 30 s after Houdini.
Tests: `tests/test_witness.py` (crafted `tests/contracts/witness/lock.sol`). Results (same run
as C): the 5 rows `Liquidation_defence_exists` of lending-simple-* are valid for every n (31-70
s; unknown at 300 s before), each by the instance repay(debt[a]), in agreement with the ground
truth.

## Done (2026-10-24): E, the full run at b0deb54 (server)

All the families but the regressions (264 tasks), every number of users, 600 s per property, 6
shards on the server: `results/server-20261024-b0deb54.csv` (runs/server/final/e600). 168
valid, 71 invalid, 25 without verdict; no verdict disagrees with the ground truth. Against the
241 common rows of results/cluster-20261022-2304.csv and cluster-20261024-0035-lending.csv: 69
rows gained a verdict (AMM 30: groups 1-2 and C; vault 2: group 2; lending 37, among them the 4
lending-simple-real `Liquidation_defence_exists` rows, by D), none lost one, none changed. The 25 open rows are all
lending: `Liquidation_attack_any` (9), `Liquidation_attack(_exists)` with ground truth true (4),
`Liquidation_defence` on lending-real and lending-int (5), `Exchange_rate_monotone` on
lending-real (4), and Nonnegative, Totals, Health_non_interference on lending-int (3). The invariant
phase of lending-real now ends (lending_real_v3: 84 proved, 20 dropped, 331 s); it did not in the
cluster run of 2026-10-24. Analysis of the open rows: below (2026-10-25).

## Done (2026-10-25): the open rows of E analysed; two bugs fixed (with the user)

Agents, all their runs on the server (scripts and logs in the session scratchpad,
`e-analysis/`). An earlier attempt, with five agents allowed to run pure Python locally, ran the
laptop out of memory (2026-10-24, 22:07): no computation runs locally any more.

- **Houdini: duplicated inputs in the steps (fixed).** `Checks._after` quantified the value and
  the numeric arguments inside the expanded address quantifiers: one input per copy, and
  `refuted_after` read the last copy. On lending_int (5 users) the constructor (not payable) got
  value 20, every replay reverted, the per-candidate step decided nothing in 30 s, the
  undecided rule dropped 151 generated candidates, and the declared Nonnegative and Totals were
  then refuted: 0 proved. 68 step programs of the AMM, lending and vault files had such
  duplicates. Fix: the expanded quantifiers innermost. Checked by an independent agent: no
  change of cutoffs or step counts on the 44 files (110,805 step counts), the replay right for
  every parameter type. On the server, lending-int at 600 s: Nonnegative, Totals (inductive) and
  Health_non_interference (invariants, 15 s) proved; no other verdict changed; the test suite
  passes but `test_trans_kind2` (server's Kind 2). Remaining weakness: the undecided rule can
  still drop every generated candidate when a replay refutes nothing for another reason.
- **Candidate witnesses: int terms for uint parameters (unsound, fixed).** `witness.candidates`
  offered int terms for a uint parameter: a negative value makes the call revert, while the
  arguments of the property range over the naturals, so the instance did not imply the
  property; the tool proved a false crafted property (`tests/contracts/witness/uint.sol`).
  Fix: the same type, or uint for int (uint fields are nonnegative in reachable states). No
  verdict of E was affected (its 5 proofs by instances have real or int parameters and terms).
- **Exchange_rate_monotone (lending-real, 4 rows) is false**, against the ground truth: after
  interest is accrued and repaid, redeeming the last credits resets xr0 to 1 (checked by hand:
  constructor, deposit0(1), borrow(1/2), accrue, repay(11/20), redeem0(1): xr0 from 21/20 to
  1). The user decides the ground truth; `forall a f args . << a : Lending.f(args) >> (sc0 > 0 ->
  xr0 >= old(xr0))` is proved for every n in 2.8 s. Fuzzing with boundary values (a numeric
  argument takes the value it is compared with in the requires, e.g. `sdebt[msg.sender]*idx`)
  refutes v1 and v4 in 76 s at 300 s (not adopted yet).
- **Liquidation_defence (lending-real, 4 rows, true):** the instance repay(sdebt[a] * idx) is
  proved for every n in under 1 s; witness terms from the requires of the procedure (prototype)
  prove the 4 rows (end to end 48 s on lending_real). lending_int (false): a 9-step counterexample
  exists (cvc5 refutes the exact check in 2 s, z3 not in 60 s); no search reaches such states.
- **Why the invariant phase of lending-real now ends: the reduction by symmetry (b230f2c).**
  Measured on the server (lending_real.sol, every n, 1150 s): at cab8313 it ends in 378 s (84
  proved, for every n >= 5); with KINDHML_SYMMETRY=0 it does not end, nor at ff17998 (the parent
  of b230f2c) or 9d91616. The step of liquidate with the cutoff 5 is 3.5-3.8 MB without the
  reduction (undecided after 242 s), 170-330 kB with it (decided by z3 in at most 3.2 s). The
  cluster run of 2026-10-24 was at b89afee or 3c249a7, both before b230f2c.
- **Attack rows (13):** direct.py refuses free states with an address field (`oracle`); a case
  split over its values proves the 4 true Liquidation_attack(_exists) rows in 1-2 s after Houdini
  (tested end to end). The 5 false Liquidation_attack_any rows: the bounded evaluation of three
  nested method existentials times out; candidates from φ with those existentials replaced by
  false refute them when fuzzing runs alone (48-188 s), not yet in the portfolio. The 4 true
  ones need instances of the whole chain (setPrice; liquidate; setPrice), proved on the instance.

## Done (2026-10-25): the proposals for the open rows of E; full run (server)

Implemented, in the order agreed with the user: ground truth of `Exchange_rate_monotone` (false)
and `Exchange_rate_monotone_credits` (181f019); a case split on the enumerated fields of the free
state in direct.py (1865df2); guard terms for the candidate witnesses (6001741); boundary values
of the fuzzer, its weakened evaluation for existentials over methods, and scheduling for large
programs (DESIGN.md, Sect. 6: undecided candidates kept, free-state programs made once, a least
time per MB for Kind 2, KIND2_LARGE).
- Full run at this code (snapshot p7; all families but the regressions, 268 tasks, 600 s, 6
  shards; `results/server-20261025-p7.csv`): 183 valid, 72 invalid, 13 unknown; no verdict
  disagrees with the ground truth. Against E: 14 rows gained a verdict (lending-real
  `Liquidation_defence` 4, `Liquidation_attack(_exists)` 4, `Exchange_rate_monotone` 2 (v1, v3;
  v2 was refuted in 22 s in a separate run, unknown here),
  lending_simple_int `Liquidation_attack_any`, lending-int Nonnegative, Totals,
  Health_non_interference), plus the 4 new `Exchange_rate_monotone_credits` rows (valid).
- 2 rows lost a verdict, both found by fuzzing near the limit in E (amm_int `Sandwich_slippage`
  at 527 s, lending_real_v2 `Health_non_interference` at 422 s). Rerun with 2 shards: HNI
  refuted in 421 s with boundary values, unknown without; Sandwich_slippage unknown with them
  (twice), refuted in 519 s without. One run per setting: not enough to say whether boundary
  values slow Sandwich_slippage.
- Tests on the server: 1340 passed; the 50 failures are all `test_trans_kind2`, as in the
  earlier suite runs (server's Kind 2).
- Still open (13): `Liquidation_attack_any` false (4: lending_real, _v3, lending_simple_real,
  _v3) and true (4); lending_real_v2 and _v4 `Exchange_rate_monotone`; the 2 rows above;
  lending_int `Liquidation_defence`. On lending-real, the invariant
  phase takes about 380 s of the 600 s, and the fuzzer alone needs 140-160 s for a candidate.

## Done (2026-10-25): instances of a chain of existentials over methods (with the user)

`Liquidation_attack_any` (three calls of the attacker) had no proof: the witnesses of Sect. 7.8
fix only the first existential, and only without a cutoff. The user rejected taking the call
sequences from sibling properties (cheating: a user does not know them); the user's idea of
scoring the combinations by fuzzing became `chains.py` and `verify._chain_rounds` (DESIGN.md,
Sect. 7.9): sequences scored by the margin of the conclusion at models of the invariants and the
premise (z3, free states) and at the counterexamples of the instances tried (CEGIS).
- E1 (BMC for a reachable premise state, for the false rows): depth 5 in 31-36 s on
  lending-simple, none in 120 s on lending-real; no faster than the fuzzer, not pursued.
- E2 (prototype, `runs/scratch-20261025/chain/`): the 4 true rows proved at the first or
  second instance, 11-34 s after the invariants; in the order of the source, none in 300 s on
  lending_simple_real_v2 (402 of 6859 instances). Crafted first: `tests/contracts/chain/`.
- A soundness review by a separate agent (read-only): no false proof for type-checked
  properties, but the names of the new existentials could capture or clash (contrived
  identifiers); fixed with fresh names, and the robustness findings fixed (the weakened
  property no longer blocks the instances, undecided instances are checked again, states from
  Kind 2 counterexamples, bounds, exceptions). `tests/test_chains.py`: 7 tests.
- In the tool (600 s, 8 shards): lending_simple_real_v4 78 s, _v2 95 s, lending_real_v4 177 s;
  lending_real_v2 unknown (its instance comes after the 600 s: a question of scheduling, left
  for later, as the final runs will have a longer limit). lending_simple_int still refuted.
- Lending regression (before the review fixes, which change only the chain side; 107 of 117
  rows at the time of the commit): no verdict lost or wrong; gained 3 `Liquidation_attack_any`
  rows and `Exchange_rate_monotone` v2 and v4 (fuzzing, which varies between runs).

## Noted (2026-10-25, with the user): for later

- A full run with `--no_user_invariants` (only generated invariant candidates), next to the run
  with the declared ones (`results/server-20261025-p7.csv`), to show how much the declared
  invariants of the spec files contribute.
- Improvements use only the contract and the property under check: never instances or hints
  from other properties of the spec (the proposal "chain instances from sibling properties" for
  `Liquidation_attack_any` was rejected). The declared invariants of the spec files, templates
  designed from the use cases, and constants measured on the rows are accepted.

## Noted (2026-10-14, with the user): invariant generation; the numbers of users for Kind 2

- **Invariant generation from the literature.** The generator is a fixed list of templates
  (Sect. 6). To study (references from memory, to check): template-based generation with
  Farkas' lemma (Colón, Sankaranarayanan, Sipma, CAV 2003); learning from examples and
  counterexamples (ICE, Garg et al., CAV 2014); dynamic detection (Daikon), and its uses
  for smart contracts (InvCon, Trace2Inv, SmartInv); for parameterized systems, invariants
  computed on a small instance and generalized to quantified ones (invisible invariants,
  Pnueli, Ruah, Zuck, TACAS 2001; I4, Ma et al., SOSP 2019; IC3PO, Goel and Sakallah,
  2021; DistAI, Yao et al., OSDI 2021). The last group fits the parameterized mode: Kind 2's
  invariants with N users (`--print_invs`) could be generalized over the users and proved
  for every n by Houdini with a cutoff.
- **A smarter choice of the numbers of users for Kind 2.** Kind 2 now tries N, N + 1, ...,
  n in turn. If need(¬φ) = 0, the numbers of users for which φ holds form an initial
  segment {1, ..., T} (Cor. 7.8 and Lemma 7.5): one proof with m users gives every n <= m,
  and one counterexample with m users every n >= m. So T can be bracketed by jumps (e.g.
  N, N + 1, N + 2, then n directly, or doubling) and then found by bisection, or several
  numbers of users can be tried by parallel jobs. Kind 2's cost grows with the number of
  users (the encoding grows linearly or faster, Sect. "3 and 4 participants"), which a
  strategy must weigh. If need(¬φ) > 0, there is no such monotonicity, and each number of
  users needs its own run.

## Planned (later, agreed 2026-10-14): k-induction with a cutoff depending on k

Goal: proofs on the transition system that hold for every n ≥ c, which Kind 2's proofs
with c users do not give (its IC3 and invariant generation produce invariants about the
users u1, ..., uc).

Main steps: a k-induction proof consists of two formulas; each is a check on free states,
like the steps of Houdini; read in first-order logic (DESIGN.md, Sect. 7.2), its cutoff
grows linearly in k; both are checked with that many users, so the proof holds for every
larger number (Thm. 7.3).

- **The two formulas** (T one transaction, with the guard on construction of the properties):
  Base_k: Init(s_0) ∧ T(s_0, t_0, s_1) ∧ ... ∧ T(s_{k-1}, t_{k-1}, s_k) ⇒ φ(s_0) ∧ ... ∧ φ(s_k);
  Step_k: T(s_0, t_0, s_1) ∧ ... ∧ T(s_{k-1}, t_{k-1}, s_k) ∧ φ(s_0) ∧ ... ∧ φ(s_{k-1}) ⇒ φ(s_k),
  with s_0 free. If both are valid with n users, φ holds in every reachable state of S_n.
  The proved invariants C may be added as premises at every state of Step_k (then the
  claim is for n ≥ max(c_H, c_k), Prop. 7.7).
- **The cutoff.** In ¬Step_k, the address constants are the a_F address fields of s_0; for
  each transaction, its sender and the address parameters of the procedure it calls (the
  witness fixes the procedure, so p is the largest number of address parameters of a
  procedure, constructors included, since the transition system can call them); the w
  address universals of φ(s_k); the address existentials e of each premise φ(s_i) (and of
  the invariants C, if added). So c_k = max(1, a_F + k(1 + p) + w + k·e), and Base_k needs
  at most as many (Init fixes the address fields to null). φ must satisfy (F3) in both
  polarities, since it is a premise and a conclusion. Bank: a_F = 0, p = 0, w = 1, e = 0,
  so c_k = k + 1.
- **Requirements.** Only plain k-induction: no IC3, no invariant generation (their
  invariants name the users); path compression (states pairwise distinct), if enabled,
  adds address existentials (a differing entry for each pair of states) and must be
  disabled or counted. Sums as ghost variables (Lemma 7.4); in Base_k, the initial sum of
  the balances becomes a free value (sound, weaker), while the sums of the fields are 0.
- **Implementation.** Build Base_k and Step_k as free checks, as the steps of Houdini
  (`invariants.py`), for k = 1, 2, ... with c_k users, rather than rely on Kind 2's
  internal k-induction: then the checked formula is the one whose cutoff is computed, and
  no auxiliary invariant enters. A counterexample of Base_k is a counterexample of φ with
  c_k users (Lemma 7.5 or the symmetry extension above decides whether it extends); a
  counterexample of Step_k only says that k is too small.
- **Cost and open question.** c_k grows with k, so it helps only for small k; plain
  k-induction without auxiliary invariants is much weaker than what Kind 2 ran for the
  baseline proofs. First experiment: Kind 2 with BMC and k-induction only, with 2 users, on
  the properties proved in `results/v1_benchmarks.csv` (about 10 properties, at most 10 minutes),
  recording the depth k of each proof.

## Decisions taken after M1 (with the user)

1. **Domain of `address` quantifiers:** all addresses except `null` (users and contracts).
   A new predicate `is_EOA(e)` holds iff `e` is a user address (not `null`, not a contract).
   Properties whose ground truth assumes users only (e.g. `mapping1` `P1_true`) get an explicit
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
