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
* Numbers are Lustre `int`, or `real` for the type `real` (Sect. 5).
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
7. **Reals** (extension, not in the paper). See Sect. 5.
8. **Invariants and checks on free states** (extension, not in the paper). See Sect. 6.

## 6. Invariants and the portfolio strategy (`invariants.py`, `verify.verify`)

Kind 2 checks `Φ(φ)` on the reachable states of `(Init, Trans)`, by BMC and k-induction
through `Trans`. This fails when `Trans` is nonlinear and `φ` holds only because of facts
about the reachable states: on a constant-product swap pool in reals, even the concrete
round trip `swap0(10); swap1(out)` from reserves (100, 100) stays unknown, because Kind 2
must establish, through the nonlinear swaps, that wallets and reserves are nonnegative.

**Invariants.** A file may declare `invariant I { ψ }`, with ψ a formula without
modalities, required, like a rule, in the reachable states where all contracts are
constructed. The candidates are the declared invariants and the generated ones (below).
Built-in facts, true in every system, are assumed without checks: balances are
nonnegative; the fields of an unconstructed contract have their default values (only the
procedures of a contract assign its fields, and all but the constructor require it to be
constructed). The largest inductive subset C is found by Houdini (Flanagan, Leino 2001):
* initiation is trivial (no contract is constructed in the initial states);
* the step, for each procedure f (constructors included), is one query on free values,
  without the transition system: `C(s) ⇒ Φ(∀a, x̄, v. ⟨a : C.f(x̄) $ v⟩ (constructed → ∧C))(s)`,
  encoded like a modality so that only f is unfolded (with the whole `Trans` and `t.fx`
  fixed, each query took about 10 s);
* if it is refuted, its counterexample gives a free state satisfying C and the arguments of
  the call; the reference interpreter runs the call from that state (for every sender),
  and the candidates false afterwards are not inductive; if none is identified, or the
  query is not decided, the step of f is checked with one property per candidate
  (slower: the inlined call is copied into every property; on the lending protocol, 71
  candidates were not decided in 64 s that way, while each conjunction takes 1-6 s);
* the candidates refuted in a pass are dropped together, and the steps are checked again;
  generated candidates still undecided after 16 s are dropped too (declared ones wait).

Houdini runs once per file, before its rules, as a phase with its own time limit
(`prove_invariants`; in `run_all.py` and the CLI, `--invariants_timeout`, by default 3 times
the time limit of a rule; its time is printed); if it does not finish, the rules go on with
it in their rounds. A run killed by the memory limit says nothing about the candidates: the
pass stops and a later one tries again (under memory pressure, all the AMM candidates were
once dropped as undecided). Within the rounds of
each rule, Houdini shared the time with the other tasks and restarted from small budgets:
on the lending protocol it did not finish within 11 rules of 60 s, while alone it takes
about 110 s.

The rules assume the proved invariants minus the generated ones implied by other proved
ones (`invgen.minimize`, syntactic: `f >= 0` by `f > 0`, an implication by the equivalence,
`sum(m) <= f` by `sum(m) == f`, ...): fewer, stronger premises are faster for the solvers.
Minimizing before Houdini would lose candidates: `res0 > 0 -> sc0 > 0` is implied by
`(res0 > 0) == (sc0 > 0)`, which survives the fuzzer but is false (all the reserves can be
borrowed).

**Invariant generation** (`invgen.py`). Houdini only selects among candidates, so the tool
generates them from templates over the fields of the contracts: signs (`f >= 0`, `f > 0`,
`∀u. m[u] >= 0`), bounds by the constants of the contracts, positivity relations
(`(f > 0) == (g > 0)`, `f > 0 -> g > 0`), holders (`∀u. !is_EOA(u) -> m[u] == 0`,
`m[null] == 0`; address quantifiers exclude null, so `m[null]` needs its own templates, or
`sum(m) == f` does not bound the entries of a free state), totals (`sum(m) == f`,
`sum(m) <= f`, `∀u. m[u] <= f`), definitions (`G -> f == e` and `G && d != 0 -> f * d == e'`
for the assignments `f = e` and `f = e' / d` under the conditions G of the enclosing ifs),
and `a != null` for address fields. `sum(m)` is a new built-in (also for users): the sum of
m over all addresses, finite (A1). The candidates are written as source text and
type-checked like declared invariants; those false in a reachable state of the fuzzer (2 s
of random transactions) are discarded first (as Daikon does). Kind 2's own generators do
not replace this: they relate pairs of terms of the Lustre program (no sums over the
addresses, no polynomial relations), and on the nonlinear use cases they exceeded the
memory. Results (generated candidates only, the declared invariants ignored): AMM, 123
templates, 31 after the fuzzer, all proved in 10 s; lending, 248 templates, 71 after the
fuzzer, 61 proved in 111 s; in both, the proved ones include every invariant written by
hand for the use case (e.g. `sum(minted) == supply`, and the exchange rate
`sc0 > 0 -> xr0 * sc0 == res0 + ssdebt * idx`).

**Checking a rule on a free state.** `C'(s) ⇒ ((∧ constructed) → Φ(φ))(s)` for an arbitrary
state s, where C' is a subset of C. If it holds, φ holds in every reachable state (all of them
satisfy C): the proof is sound, for any C'. The solvers are sensitive to the form of the
query, so the tool tries several forms in turn:
* premises: first the invariants that share state variables with φ, then their transitive
  closure (in the AMM, the invariant on the liquidity shares, connected to the swaps only
  through `supply`, turned a 1 s proof of Swap_reversibility into a timeout; the balance
  lemma over int, in a query over nonlinear reals, keeps z3 from using nlsat);
* the property as a whole, then split into cases, its conjuncts through implications, one
  property each (AMM Slippage: unknown after 60 s as a whole, 54 cases proved in 3 s; the
  swap-pool round trip: proved in 1 s as a whole, its 2 cases unknown together in 20 s).
The invariants are a premise of the property, not Lustre assertions (with assertions, z3
did not prove the swap-pool round trip in 30 s; as a premise, in 1 s). The universal
quantifiers in positive position become inputs of the node (`hoist`): a property is valid
iff it holds for all inputs, and the solver then gets no quantifier (Kind 2 passes them to
it, which keeps z3 from using nlsat: a swap round trip at a concrete state was unknown after
20 s with `∀x`, refuted in 0.5 s with x an input). Files over reals should use
`pragma balance real`, so that the queries are over reals only.

If the check fails, its counterexample s* satisfies C' and violates φ, but may be
unreachable (a counterexample to induction). A BMC search for s* in `(Init, Trans)` then
either finds a trace to s*, which is a counterexample of φ, or not; s* is shown to the
user when the time limit expires, as a hint for stronger invariants. Unreachability of s*
cannot be decided in general.

**Random testing** (`fuzz.py`). Kind 2 rarely finds counterexamples through nonlinear
transitions (on the integer AMM, BMC reaches depth 1 in 60 s, and a counterexample needs a
constructor, a deposit and a swap). Random transactions, run by the reference interpreter
(reverted ones left out), give reachable states; the rule is evaluated there with bounded
quantifiers (and a sample of the arguments of all procedures). A state where it fails is a
candidate, which Kind 2 checks exactly (the formula at that concrete state, `concrete_check`);
a confirmed candidate is a counterexample, reported with its transactions. For a rule with
an existential quantifier over numbers in positive position, the bounded evaluation almost
always misses the witness, so new random states are checked exactly instead. The random
values are chosen half of the time among the numbers of the current state (or their half
or quarter), and the sender, with probability 0.2, among the users stored in address
fields (an owner, an oracle): otherwise the procedures restricted to them almost never
succeed (on the lending protocol, `accrue` was not called, and false candidate invariants
such as `xr0 == 1` survived the filter).

**Portfolio** (default; `--strategy kind2` gives the previous behaviour). The tool does not
give up: it runs rounds of the tasks below, one Kind 2 job at a time, each with the round's
budget (4 s, doubled at each round), until a task gives a verdict or the time limit expires
(time limit 0: no limit). Task 5 gets 4 budgets per round. With a time limit, on contracts
with linear arithmetic it gets all the time left (a Kind 2 run restarts from scratch, and on
the regressions the other tasks succeed in seconds or not at all); on nonlinear contracts (a
product of two variables, a division by a variable) the rounds go on.
1. Houdini on the invariants (once per file; shared by its rules).
2. The rule on a free state under the proved invariants, in the forms above (z3 with 3/4 of
   the budget, then cvc5: z3 decides nonlinear real queries with nlsat, and Kind 2 cannot
   read cvc5's models of such queries).
3. The BMC search for s*, once 2 has found it.
4. Random testing, with exact confirmation.
5. Kind 2 on the transition system (as before; with BMC and k-induction only, after the
   memory limit of a run killed a solver: the invariant generators and IC3 run in parallel
   and each has its own solver, which exceeds the memory on nonlinear problems).

Verdicts say how they were found: `inductive` (an invariant proved by Houdini),
`invariants` (task 2), `reach` (task 3), `fuzz` (task 4), `kind2` (task 5).

On the regressions and test contracts (30 s per rule), 82 rules out of 89 match; 28 are
decided by free-state checks (0.4–2.6 s each). Two rules at the edge of the time limit with
Kind 2 alone (about 27 s) are now unknown: `two-donatees` P5 and `calls`
Report_sees_balance_after_transfer.

## 5. Real variables

Fields, mapping values, parameters and quantified variables may have type `real`. With
`pragma balance real;` at the start of a file, `balance`, `msg.value`, transfer amounts and
the values of calls and modalities are real too (`Program.balance_type`); the block number
and its increase stay int. The encoding is the paper's, over real instead of integer terms.

Kind 2 (v2.3.0) differs from the integer case in the following points, each checked by an
experiment.

* **No mixing.** Lustre does not convert between int and real: `x + 1` with `x : real` is a
  type error, and literals must be written `1.0`. The type checker therefore inserts
  `ToReal` (printed `real(e)`) wherever an int is used as a real, turns int literals into
  real ones, and marks the arithmetic on reals (`BinOp.real`). There is no conversion from
  real to int (Kind 2's `int(x)` is the floor, e.g. `int(-1.5) = -2`).
* **Division.** `/` on reals is the division of reals, `div` (Euclidean) on ints; `%` is not
  defined on reals. As for `div`, `x / 0.0` is an unspecified value in SMT-LIB (Kind 2
  finds `1.0/0.0 ≠ 2.0/0.0`), so the guards def^i(s) also cover real divisions, with the
  zero `0.0`. `r = n / 2` with `n : int` is the integer division, converted; the type
  checker warns about it.
* **Solvers.** On quantified real properties the solvers are complementary: z3 does not
  prove `∃x : real. x > r ∧ x < r + 1` (true up to 0 steps), which cvc5 proves; cvc5 does
  not prove some properties that z3 proves (`Ltree.fold` in the inductive step, as for
  ints). The default strategy (cvc5, then z3) covers both (e.g. `real_balances.sol`
  Small_payment is proved by z3 after cvc5's half of the budget). Nonlinear real
  arithmetic works with k-induction; cvc5's IC3 fails on it, as on nonlinear integers.
* **Counterexamples.** In JSON, Kind 2 writes a real as `{"num": n, "den": d}`; the
  formatter prints `n/d`.
