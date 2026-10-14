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
  many rules are then proved without user invariants?

Done (2026-10-07, commit 7772ac4; DESIGN.md, Sect. 6): `invgen.py` (templates, filter on
the fuzzer's states, `minimize` after Houdini), `sum(m)`, counterexample-guided Houdini
(one conjunction query per procedure), invariant phase per file. With the generated
invariants only (`--no_user_invariants`, 60 s per rule, `runs/invgen_rules3.log`):
* AMM main: 135 templates, 31 after the fuzzer, all proved in 7.5 s; 8 of 10 rules proved,
  the same as with the invariants written by hand (which are proved as rules in 0.5 s);
  unknown: Sandwich, Arbitrage (existentials over reals).
* Lending main: 249 templates, 67 after the fuzzer, 61 proved in 47 s; 8 of 11 rules
  proved, the same as with the invariants written by hand (proved as rules in 0.6 s);
  unknown: Liquidation_defence, Liquidation_attack (false), Exchange_rate_monotone.
* Lessons: one property per candidate copies the inlined call into every property (71
  lending candidates not decided in 64 s; as one conjunction, 1-6 s per procedure);
  address quantifiers exclude null, so `m[null]` needs its own templates; minimizing before
  Houdini loses candidates implied by false ones; Houdini needs its own phase (inside the
  rounds of each rule it did not finish on the lending protocol); runs killed by the
  memory limit must not count as undecided.
* Regressions and test contracts with the generator on (default; 30 s per rule,
  `runs/regressions_invgen.log`): 84 of 90 rules match (82 before), no wrong verdict; the 6
  unknown are in the OPEN list of `tests/test_regressions.py`; the invariant phase takes
  0-13 s per file.

## Noted (2026-10-12, not planned yet): a portfolio of encodings for long budgets

Method quantifiers are expanded only while their nested copies are at most a bound
(`--expand method:N`, default 32; DESIGN.md, Sect. 2). Neither choice is better on every
rule (30 s per rule, 2 participants): with expansion, price-bet `Liquidity` (9.8 s) and
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
rule, portfolio strategy). Data in `runs/participants_*`.

- **Regressions** (additivity, args, liquidity4, mapping1, mapping2, owner, states;
  46 rules): all verdicts are correct for n = 2, 3 and 4, and every rule is decided by the
  same method (24 by invariants, 20 by reach, 1 by fuzz, 1 by Kind 2). Total time
  70.6 s, 76.3 s and 77.6 s. Only liquidity4 `P12_true` slows down noticeably
  (0.7 s for n = 2, 3.7 s for n = 3 and 4). The invariant phase takes the same time.
- **bank** (4 rules): the three rules proved by invariants stay proved (No_frontrun_deposit
  1.0 s for n = 2, 1.8 s for n = 4). `Liquidity` is unknown in both cases; within 10 s
  Kind 2 reaches depth 1 for n = 2 and no depth for n = 4.
- **Encoding size** (`--only_lus`): it grows linearly in n when the rule has one address
  quantifier (bank `Liquidity`: 10.4, 12.3, 14.3 KB; liquidity4 `P12_true`: 4.6, 5.1,
  5.7 KB), and faster with nested ones (bank `No_frontrun_deposit`: 13.8, 21.1, 30.9 KB),
  as expected from the expansion of address quantifiers over all addresses.

Conclusion: on these rules, more participants do not change the verdicts and cost little
when the rule is decided by invariants or by a short counterexample; the cost appears in
the rules left to Kind 2 (slower unrolling) and in rules with nested address quantifiers.
Not tested: rules whose counterexample needs 3 or more users (where n = 2 could miss a
violation), and the harder benchmarks (vault, price-bet, AMM, lending).

## Done (2026-10-14): parameterized mode (prototype, with the user)

Theory and design in DESIGN.md, Sect. 7. Option `--parameterized` (`kindHML.py`,
`run_all.py`); without it, the tool behaves as before (the 46 regression rules below: same
verdicts and methods, 69.7 s against 70.6 s). Code: `cutoff.py` (fragment and count),
`Checks.cutoff`, `Checks.sum_axioms`, ghost sums (`System.ghost_sums`, `encode_trans.py`),
`verify.effective_users`. Tests: `tests/test_cutoff.py` (the count on small formulas, the
cutoffs of bank and additivity, ghost sums against the reference interpreter on every
contract file, the guard of the sum axioms; with Kind 2, `tests/contracts/parameterized/
registry.sol`).

Experiments (10 s per rule, one job at a time, Kind 2 memory capped at 1 GB; data in
`runs/parameterized_*` and `runs/normal_*_n100*`). Total time and correct verdicts:

| | n = 2 | n = 3 | n = 4 | n = 100 |
|---|---|---|---|---|
| regressions (46 rules), normal | 70.6 s, 46 | 76.3 s, 46 | 77.6 s, 46 | 457 s, 23 |
| regressions, parameterized | 62.1 s, 45 | 63.5 s, 43 | 64.3 s, 43 | 70.7 s, 43 |
| bank (4 rules), normal | 12.4 s, 3 | | 13.6 s, 3 | not finished (*) |
| bank, parameterized | 12.0 s, 3 | | 12.1 s, 3 | 12.1 s, 3 |

(*) The invariant phase does not finish in 42 s, the first two rules time out, and the
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
- bank: the three rules proved with 2 users are proved for every n >= 2. `Liquidity` is
  unknown, as with 2 users; with the declared invariant `sum(funds) <= balance[Bank]`, it is
  proved for every n >= 2 in about 4 s, thanks to the sum axioms (without them: a
  counterexample to induction with `funds[u2] = 3 > balance[Bank] = 1`).
- registry (rules using `sum(registered) == count`): proved for every n >= 2 in 4.9 s for
  n = 2, 3, 4 and 100; with 100 users the normal mode times out on all rules (147 s).
  `At_most_two` (true only for n <= 2) is unknown in parameterized mode, for every n.

Not done yet:
- the larger benchmarks have larger cutoffs: vault 10 (its Houdini steps 5), lending 7
  (steps 5, one rule outside), price-bet 5, AMM 4. The cutoff of a file is the largest over
  its rules; Houdini could use the cutoff of the steps, and each rule its own (done, see
  "one number of users per check" below);
- counterexamples are searched for with c users only (a BMC of depth d needs up to
  d(1 + p) + w users);
- with c = n, ghost sums are weaker than exact sums: first trying exact sums with n users
  would keep the proofs for exactly n users.

## Done (2026-10-14): parameterized mode on bank, vault, price-bet; one number of users per check

**First batch** (one cutoff per file; 60 s per rule, 60 s per invariant phase, Kind 2 at
1.2 GB, 100 users asked for; `runs/local-20261014-1313/parameterized_n100`, 33 min). All
13 verdicts agree with the ground truth, but only bank is decided (13 of 16 rules; vault 0
of 6, price-bet 0 of 12), against 32 of 34 in `results/v1_benchmarks.csv` (2 users,
120 s, 2 October). Causes: the price-bet and vault rules quantify `exists` over addresses,
so 6 counterexamples with 5 users and 1 with 10 do not extend (Lemma 7.5); their proofs in
the normal mode came from Kind 2 on the transition system, which do not transfer; the
vault cutoff 10 (one rule) made its encodings slow (`non_inflation`: 172 s and 13.8 MB
with 10 users, 0.2 MB with 2), so its rules took 320-350 s despite the 60 s budget. One
Kind 2 run reported "Error opening input file" (vault.sol); it did not happen again on the
same program; the disk was 99 % full.

**One number of users per check** (DESIGN.md, Sect. 7.5, Prop. 7.7): each step of Houdini
uses the cutoff of its step for the current candidates; the check of a rule the cutoff of
its premises; the search for a counterexample to induction the users of that check;
fuzzing and Kind 2 N = max(c_H, c_R). An `args` variable counts only the address
parameters of the procedures of the called contract other than the constructor (vault
`non_inflation`: 8 instead of 10; lending: 6 instead of 7). Experiments, with Kind 2 calls
counted by task and number of users (scratchpad script):
- regressions (46 rules, 10 s per rule, 100 users asked for): verdicts unchanged (43
  correct, the same 3 unknown), 86 s; of the free-state rule checks, 62 with 1 user, 5
  with 2; reach 21 with 1 user; Houdini 7 with 2 and 5 with 3; the 4 + 1 + 1 calls with 100
  users are the additivity rules outside the fragment;
- bank and bank_v3: the same 7 decided rules, e.g. "for every n >= 2 users; rule checked
  with 1 user";
- vault and vault_v2 (60 s per rule): Houdini 8 calls with 4 users and 8 with 5;
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
rule is checked exactly at the new final state. These confirmations get 10 s each
(`CONFIRM_SECONDS`), also after the time limit. A counterexample that does not extend no
longer ends the search: the other tasks go on. Tests: `tests/test_cutoff.py` (the count, the
idle users, the participants of a counterexample; with Kind 2,
`tests/contracts/parameterized/capped_registry.sol`: a counterexample that extends, and one
that must not, for a rule true with 3 users).

Results (100 users asked for; data in `runs/local-20261014-1532-idle2` and
`runs/parameterized_idle_reg_n100.*`):
- regressions (10 s per rule): 45 of 46 correct (43 before); args P0_false and owner P5_false
  are refuted for every n ≥ 1 and n ≥ 2. The only unknown is owner P2_true, proved by Kind 2
  only;
- price-bet and vault_v2 (60 s per rule, 12 min): all 7 false rules are refuted, for every
  n ≥ 5 (n ≥ 4 for price-bet_v3 Frontrunning), as by the normal mode with 2 users (none
  before, with one cutoff per file; 3 before the balances were set to 0). The 7 true rules
  are unknown: their proofs with 2 users come from Kind 2 on the transition system, which do
  not transfer, and the checks on free states lack invariants.

## Done (2026-10-14): reserve templates; Kind 2 with more users (with the user)

- **Reserve templates** (`invgen.py`; DESIGN.md, Sect. 6): `sum(m) == balance[C]` and
  `sum(m) <= balance[C]` for each numeric map m and contract C. On bank (parameterized, 5
  users asked for, 60 s per rule), Houdini proves `sum(funds) <= balance[Bank]` and the
  four rules are proved for every n >= 2 in 5.5 s in total (`Liquidity` was unknown).
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
    "unknown" on HEAD (expected "valid" in both). **To investigate first**: possibly the
    reserve templates (more candidates on swap_pool), or an error of Kind 2.
  Next: investigate the error above; rerun the regressions in parameterized mode (100 users)
  and the use cases (AMM, lending: time of the invariant phase with the new templates).

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

- **The two formulas** (T one transaction, with the guard on construction of the rules):
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
  the rules proved in `results/v1_benchmarks.csv` (about 10 rules, at most 10 minutes),
  recording the depth k of each proof.

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
