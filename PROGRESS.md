# KindHML v1 — Progress log

Branch `v1` (worktree `~/Desktop/gitlab/KindHML-v1`). The old tool stays on `main`
(`~/Desktop/gitlab/KindHML`) for differential testing. Work stops after each milestone.

## Milestones

- [x] **M1** Worktree, design note (`DESIGN.md`), Kind 2 experiments.
- [x] **M2** Grammar, AST, type checker; parse tests on all benchmarks and regressions.
- [x] **M3** Desugaring, `Trans` encoding, Lustre printer; unit tests; reference evaluator.
- [ ] **M4** Formula encoding, full pipeline, regressions imported; all ground truths checked.
- [ ] **M5** Contract-to-contract calls; README; `run_experiments.sh`; `\CL` notes in the paper.

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

## Decisions taken after M1 (with the user)

1. **Domain of `address` quantifiers:** all addresses except `null` (users and contracts).
   A new predicate `is_EOA(e)` holds iff `e` is a user address (not `null`, not a contract).
   Rules whose ground truth assumes users only (e.g. `mapping1` `P1_true`) get an explicit
   `is_EOA(a) ->` guard; every such change of a benchmark is listed in M4.
2. **Unconstructed states:** `φ` is checked in the reachable states where every contract is
   constructed (the property is `(∧_C constructed_C) → Φ(φ)`).
3. **Contract names in modalities:** an unknown name is a type error; `Pricebet` (price-bet)
   and `Addittivity` (regression additivity) are corrected in the files.
