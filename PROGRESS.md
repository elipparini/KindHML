# KindHML v1 — Progress log

Branch `v1` (worktree `~/Desktop/gitlab/KindHML-v1`). The old tool stays on `main`
(`~/Desktop/gitlab/KindHML`) for differential testing. Work stops after each milestone.

## Milestones

- [x] **M1** Worktree, design note (`DESIGN.md`), Kind 2 experiments.
- [ ] **M2** Grammar, AST, type checker; parse tests on all benchmarks and regressions.
- [ ] **M3** Desugaring, `Trans` encoding, Lustre printer; unit tests; reference evaluator.
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

## Open questions for the user

1. **Domain of `address` quantifiers.** In the paper `∀x:address` ranges over all addresses,
   including contracts (and `null`). Many ground truths (e.g. `mapping1` `P1_true`:
   `∀a. ∃h. ⟨a : Mapping1.h()⟩ m[a] = old(m[a]) + 1`) are true only if `a` ranges over user
   addresses, because transactions from a contract (A5) or from `null` revert. The old tool
   excludes the contract and `a0` for `forall`, but not for `exists`.
   Proposal: quantifiers over `address` range over user addresses; `null` and contract
   addresses are available only as constants (`null`, `this`, contract names).
2. **Unconstructed states.** The paper checks `φ` in all reachable states, including the initial
   one where no contract is constructed. The ground truths assume the old tool's guard
   `not constructed ∨ φ` (e.g. `mapping1` `P1_true` is false in the initial state).
   Proposal: check `φ` in the reachable states where all contracts are constructed.
3. `price-bet*.sol` rules refer to `Pricebet` while the contract is `Bet`;
   `regression_new/additivity.sol` refers to `Addittivity`. The old tool ignores the name.
   Proposal: fix the benchmarks and make the name mismatch an error.
