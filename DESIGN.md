# KindHML v1 — Design

This note maps the definitions of the paper (`main.tex`, Section "Encoding in first-order logic",
file `encoding-fol.tex`; Appendix `appendix-correctness.tex`) to the modules of the tool, and lists
every point where the tool departs from the paper.

## 1. Pipeline

```
source .sol --(ANTLR: grammar/KindHML.g4)--> parse tree --(builder)--> AST
   --(typecheck)--> typed AST --(desugar)--> core contract + core formula
   --(encode_trans)--> Init, Trans_f, Trans_C, Trans      (Lustre functions)
   --(encode_formula)--> Phi(phi)                          (Lustre property)
   --(lustre printer)--> .lus --(kind2 -json)--> verdict
```

| Module | Paper counterpart |
|---|---|
| `grammar/KindHML.g4`, `builder.py`, `ast.py` | Fig. `fig:contracts:syntax`, logic syntax (Section "logic") |
| `typecheck.py` | typing judgement Γ,n ⊢ e : T of the logic; assumptions A3, A6, A7 |
| `desugar.py` | `initPay`; `require(¬constructed_C)`/`require(constructed_C)`; `def(s)` guards (A3, App. `app:correctness:transition`); unfolding of contract calls (A4) |
| `encode_trans.py` | `Init`; levels and `S^i(s)` (Table `tab:statement-to-fol`); `Trans_f`, `Trans_C`, `Trans`, `Revert` |
| `encode_formula.py` | modal tree and `Φ^{V,E}` |
| `lustre.py` | "direct transcription" into Lustre (not detailed in the paper) |
| `kind2.py` | invariant check of `Φ(φ)` w.r.t. `(Init, Trans)` (Theorem `thm:soundness`) |
| `reference.py` | the operational semantics (Figs. `fig:semanticsExpr`, `fig:semanticsSt`, transactions, flagged states), used only for testing |

## 2. Lustre shape of the encoding

Experiments with Kind 2 v2.3.0 (see `PROGRESS.md`, Milestone 1) fix the following shape.

* `type address = enum { null, <C1>, ..., u1, ..., un }` (contract addresses and `n` user addresses).
* `type proc = enum { <C>_<f>, ... }`.
* Maps `address => τ` are records with one field per address (Kind 2 cannot inline functions
  over arrays inside quantified properties). `balance` is such a map.
* `St` is a record with one field per state variable of `StateVars` (`balance`, `constructed_C`,
  the contract fields, `revert`, optionally `block_num`).
* `Tx` is a record with one field per transition variable of `TransVars` (`sender`, `cx`, `fx`,
  `value`, one field `f_x` per parameter of each procedure, optionally `blocks`, the
  increase of the block number).
* For each procedure `f`, a Lustre `function trans_<C>_<f>(s: St; t: Tx) returns (r: St)`
  whose local variables `l1, ..., lm` are the levels `StateVars^1..StateVars^m`; its equations are
  exactly `S^0(s0; s)`, and `r` is the ITE of `Trans_f`.
  Kind 2 inlines these functions, which performs the substitution yielding `χ_v`.
* `function trans(s: St; t: Tx) returns (r: St)` is the switch of `Trans` / `Trans_C`.
* The main node has inputs `t: Tx` and the initial user balances, and a state stream
  `s = init -> pre trans(s, t)`; `Init` constrains the initial balances by an `assert`.
* The property is `--%PROPERTY "<Rule>" (∧_C s.constructed_C) => Φ(φ)`.

### Contract calls

A call `D.g(e1, ..., ek) $ e` in a procedure of C is unfolded (Sect. `sec:encoding:contract`):
the desugaring replaces it by `Unfold(C, D, g, ē, e, body)`, where `body` is initPay (a
transfer of `e` tokens from C to D if `g` is payable, `require(e == 0)` otherwise), the
guard `require(constructed_D)`, the uint guards, and the body of `g`, itself desugared
(nested calls are unfolded recursively; a cyclic call graph is rejected, A4).
"Evaluated at the call point" is implemented without extra variables: at level i, the
encoder computes the terms of ē and e at level i, and encodes `body` from level i in a
*frame* where `msg.sender` is D's caller C, `msg.value` is the term of e, and each parameter
of g is the term of its actual parameter. So an argument such as `balance` denotes the
balance before the transfer of `e`. The division guard of a call covers ē and e
(Appendix `app:correctness:transition`). The guard on the sender, `require(is_EOA(sender))`,
belongs to the transaction (`desugar.procedure`), not to the body (`desugar.callee`): in
an unfolded call, the sender is the calling contract.

### Lemmas

Kind 2's invariant generator does not work on quantified properties, so rules whose proof
needs an auxiliary invariant fail. The tool adds to every Lustre program the
quantifier-free property `_lemma_balances_nonnegative` (true in every system: Init makes
balances nonnegative and transfers require 0 <= amount <= balance); Kind 2 proves it and uses
it in the induction for the rule (e.g. `tests/contracts/calls.sol` Buy_mints: unknown after
60 s without it, valid in 6 s with it). `KINDHML_LEMMAS=0` disables it.

### Encoding of formulas (`encode_formula.py`)

The modal tree of the paper is built during the recursion: a node `V` is a state term (the
copy `SVars^V`) with a pointer to its parent, and `old(e)` at `V` is encoded at the parent.
For the edge `E` labelled `⟨e_s : C.e_f(ē) $ e_v @ e_Δ⟩`, the transition variables are the
record literal `Tx { sender = Φ(e_s); cx = C; fx = Φ(e_f); value = Φ(e_v); <EqParams>;
blocks = Φ(e_Δ) }` (`e_Δ` is 0 when omitted); the parameters of other procedures get an
arbitrary value (Trans does not depend on them). The only transition variables that remain
existentially quantified are the parameters of `h()` (a `method` variable without argument,
extension).

The child state `SVars^{V'}` is obtained in one of four ways (`--mode`):

* `inline` (default): the term χ(SVars^V, TVars^E), computed by substituting the levels
  (`S^i`) in Python (`lustre_subst.py`), with constant folding. This is the substitution of
  χ_v described at the end of Sect. `sec:encoding:contract`; it is equivalent to the paper's
  ∃SVars^{V'} since Trans is a function (Lemma `lem:transition`).
* `levels`: the paper's literal form: ∃ over fresh scalar copies of the levels SVars^1..m and
  of SVars^{V'}, constrained by the equations of Trans written on these scalars. This is also
  what the old tool did. Performance is similar to `inline`.
* `exists`: ∃SVars^{V'}. SVars^{V'} = trans(SVars^V, TVars^E), calling the Lustre function.
* `subst`: SVars^{V'} := trans(SVars^V, TVars^E). Kind 2 hits an internal assertion
  (`lustreAstNormalizer.ml`) on nested calls inside quantifiers.

Quantifiers over the finite types `address` and `method` are expanded into finite
conjunctions/disjunctions (A1; `--expand`). This matters: with symbolic senders, the revert
conditions of the transaction guard on the sender (`is_EOA(sender)`) occur under the inner
quantifiers, and the solvers fail to find witnesses of outer existentials (e.g. regression
`additivity` P1: unknown after 30 s without expansion, valid in 0.2 s with it).
Quantifiers over records break Kind 2's BMC and k-induction, so an `args` variable is expanded
into one scalar per element of `ParamVars`, as in the paper; unused scalars are dropped.

### Running Kind 2

One Kind 2 job at a time. Kind 2 starts its solvers in other process groups, and solvers it
leaves behind are reparented when it exits; so each run is a named `systemd-run --user`
scope (a cgroup, which also caps memory at 3 GB), stopped at the end of the run. Without
systemd, the runner records the descendants of Kind 2 while it runs and kills them.

The runner reads Kind 2's plain-text output, with `--print_cex false`. In JSON mode Kind 2
always builds the counterexample (the values of every stream of every function instance),
and it cannot be interrupted while doing so. On `tests/contracts/calls.sol`
Relay_never_reverts (three contracts), BMC finds the counterexample 7 s after the start,
but the JSON answer is printed at 25 s; with a budget of 20 s the verdict was lost. JSON
output is used only with `--cex`.

### Solvers

With cvc5, on many rules that have a counterexample, Kind 2's inductive step crashes
(`Ltree.fold : quantified term`) and Kind 2 then stops BMC as well, so that only IC3 may
still find the counterexample (the old tool filtered this error out). With z3, BMC finds
counterexamples; on many valid rules cvc5 is faster. `--solver auto` (default) runs
cvc5 for at most half of the budget and then, if it gives no verdict, z3 for the rest
(benchmarks with a budget of 120 s: 3 min 51 s in total, against about 16 min for z3 first).

## 3. Assumptions of the paper (A1–A7) and how they are enforced

* A1 (finite addresses/methods): `n_participants` user addresses from the command line.
* A2 (maps indexed by addresses): type checker.
* A3 (guarded divisions in formulas): type checker (warning or error), def-guards in contracts.
* A4 (acyclic calls): desugaring rejects cycles.
* A5 (transaction guards): `desugar.py` adds them explicitly.
* A6 (no `sender`/`value` in formulas): type checker.
* A7 (each `args` variable in exactly one modality): type checker.

## 4. Choices of the tool and deviations from the paper

Choices first recorded as `\CL` notes and now stated in the paper (after M5, with the user):

1. **uint** (Sect. `sec:contracts`). A field or parameter of type `uint` is an integer. An
   assignment of a negative value to a `uint` field reverts; a negative actual value for a
   `uint` parameter reverts. Quantified `uint` variables, and the components of `args`
   variables for `uint` parameters, range over the naturals.
2. **Senders** (Sect. `sec:encoding:contract`, A5(iv)). A transaction is sent by a user:
   it starts with `require(is_EOA(sender))`, i.e. the sender is neither `null` nor a
   contract. Unfolded contract calls have no such guard (see Contract calls).
2b. **Init.** Every address, contracts included, has a nonnegative initial balance.
2c. **Domains** (Sect. `sec:logic:syntax`). Address quantifiers range over all addresses
   except `null`; method quantifiers over the procedures other than the constructors (a
   constructor can still be named explicitly in a modality). The predicate `is_EOA(e)`
   (tool only, not in the paper) holds iff `e` is neither `null` nor a contract address.

Deviations, still recorded as `\CL` notes in the paper where relevant:

3. **block.number** (decided with the user; a `\CL` note gives the plan for the paper).
   State variable `block_num` (initially any value ≥ 0) and transition variable
   `Tx.blocks`, the *increase* of the block number. A transaction starts with
   `require(Tx.blocks >= 0); block_num := block_num + Tx.blocks`, before `initPay`; as for
   any state variable, a revert restores the old value (also of `block_num`). In a modality
   the increase is `@ e` (a uint; 0 when omitted), so formulae quantify it explicitly,
   e.g. `∃d : int` for drainability and `∀d : int` for non-inflation, as in the paper's
   Vault formulae (a negative `d` only makes the transaction revert). Earlier versions
   quantified the block existentially in every modality, which makes universal properties
   vacuous (examples.tex, `\CL` analysis note).
4. **`h()` with a method variable.** Allowed; the parameters are existentially quantified
   (this is what the literal `∃TVars^E` of the paper gives when `EqParams` is empty).
4b. **Division** is Euclidean (SMT-LIB `div`/`mod`); the paper does not fix the rounding.
   In contracts, expressions are strict: a division by zero anywhere in a statement's direct
   expressions reverts, also under `&&`/`||` (this is `def^i(s)`).
6. **Unconstructed states.** The checked property is `(∧_C constructed_C) → Φ(φ)`, i.e. `φ` is
   required only in reachable states where all contracts are constructed.
