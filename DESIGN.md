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
* The Kind 2 property is `--%PROPERTY "<Property>" (∧_C s.constructed_C) => Φ(φ)`.

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

Kind 2's invariant generator does not work on quantified properties, so properties whose proof
needs an auxiliary invariant fail. The tool adds to every Lustre program the
quantifier-free property `_lemma_balances_nonnegative` (true in every system: Init makes
balances nonnegative and transfers require 0 <= amount <= balance); Kind 2 proves it and uses
it in the induction for the property (e.g. `tests/contracts/calls.sol` Buy_mints: unknown after
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
Nested method quantifiers multiply the copies, each with the transitions of its
modalities: three free calls of the 10 methods of lending-simple give 1000 copies, whose
encoding did not finish in 5 minutes. So a method quantifier is expanded only if the
product of the numbers of methods of the expanded method quantifiers around it, and of
its own, is at most a bound (`--expand method:N`, default 32: every benchmark property so far
has at most 11 copies; two free calls of lending-simple, 100 copies, took 22 s to encode
instead of 3 s). The outer quantifiers are expanded first; the others stay quantified.
Neither choice is better on every property (30 s per property): with expansion, price-bet
`Liquidity` and lending-simple `Liquidation_defence_exists` are proved and are not without
it; without expansion, two-donatees `P3c_true` is proved and is not with it.
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

With cvc5, on many properties that have a counterexample, Kind 2's inductive step crashes
(`Ltree.fold : quantified term`) and Kind 2 then stops BMC as well, so that only IC3 may
still find the counterexample (the old tool filtered this error out). With z3, BMC finds
counterexamples; on many valid properties cvc5 is faster. `--solver auto` (default) runs
cvc5 for at most half of the budget and then, if it gives no verdict, z3 for the rest
(benchmarks with a budget of 120 s: 3 min 51 s in total, against about 16 min for z3 first).

## 3. Assumptions of the paper (A1–A7) and how they are enforced

* A1 (finite addresses/methods): `n_participants` user addresses from the command line
  (with `--parameterized`, possibly fewer; Sect. 7).
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
9. **Parameterized mode** (extension, not in the paper): checks with the cutoff on the
   number of users, and sums as state variables. See Sect. 7.

## 6. Invariants and the portfolio strategy (`invariants.py`, `verify.verify`)

Kind 2 checks `Φ(φ)` on the reachable states of `(Init, Trans)`, by BMC and k-induction
through `Trans`. This fails when `Trans` is nonlinear and `φ` holds only because of facts
about the reachable states: on a constant-product swap pool in reals, even the concrete
round trip `swap0(10); swap1(out)` from reserves (100, 100) stays unknown, because Kind 2
must establish, through the nonlinear swaps, that wallets and reserves are nonnegative.

**Invariants.** A file may declare `invariant I { ψ }`, with ψ a formula without
modalities, required, like a property, in the reachable states where all contracts are
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

Houdini runs once per file, before its properties, as a phase with its own time limit
(`prove_invariants`; in `run_all.py` and the CLI, `--invariants_timeout`, by default 3 times
the time limit of a property; its time is printed); if it does not finish, the properties go on with
it in their rounds. A run killed by the memory limit says nothing about the candidates: the
pass stops and a later one tries again (under memory pressure, all the AMM candidates were
once dropped as undecided). Within the rounds of
each property, Houdini shared the time with the other tasks and restarted from small budgets:
on the lending protocol it did not finish within 11 properties of 60 s, while alone it takes
about 110 s.

The properties assume the proved invariants minus the generated ones implied by other proved
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
`sum(m) <= f`, `∀u. m[u] <= f`), reserves (`sum(m) == balance[C]`, `sum(m) <= balance[C]`
for each contract C: what the users can claim is held by C), definitions (`G -> f == e` and `G && d != 0 -> f * d == e'`
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

**Checking a property on a free state.** `C'(s) ⇒ ((∧ constructed) → Φ(φ))(s)` for an arbitrary
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
(reverted ones left out), give reachable states; the property is evaluated there with bounded
quantifiers (and a sample of the arguments of all procedures). A state where it fails is a
candidate, which Kind 2 checks exactly (the formula at that concrete state, `concrete_check`);
a confirmed candidate is a counterexample, reported with its transactions. For a property with
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
1. Houdini on the invariants (once per file; shared by its properties).
2. The property on a free state under the proved invariants, in the forms above (z3 with 3/4 of
   the budget, then cvc5: z3 decides nonlinear real queries with nlsat, and Kind 2 cannot
   read cvc5's models of such queries).
3. The BMC search for s*, once 2 has found it.
4. Random testing, with exact confirmation.
5. Kind 2 on the transition system (as before; with BMC and k-induction only, after the
   memory limit of a run killed a solver: the invariant generators and IC3 run in parallel
   and each has its own solver, which exceeds the memory on nonlinear problems).

Verdicts say how they were found: `inductive` (an invariant proved by Houdini),
`invariants` (task 2), `reach` (task 3), `fuzz` (task 4), `kind2` (task 5).

On the regressions and test contracts (30 s per property), 82 properties out of 89 match; 28 are
decided by free-state checks (0.4–2.6 s each). Two properties at the edge of the time limit with
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

## 7. Parameterized mode: cutoffs on the number of users (`cutoff.py`, `--parameterized`)

A verdict obtained with n users says nothing, in general, about other numbers of users.
This section shows that no cutoff exists for the problem as a whole (Prop. 7.1), and that
each check on free values of Sect. 6 has a cutoff, computed syntactically, when it lies in a
fragment (Thm. 7.3). Sums over the addresses are outside the fragment; they are replaced by
state variables, which keeps the checks sound (Lemma 7.4). Counterexamples found with few
users extend to more users under a syntactic condition (Lemma 7.5). The parameterized mode
uses these results (Sect. 7.5).

**Setting.** For n ≥ 1, S_n is the system with the addresses A_n = F ∪ U_n, where
F = {null, C_1, ..., C_m} (null and the contracts) and U_n = {u1, ..., un}. Addresses are
compared only with `==` and `!=` (type checker), and neither contracts nor properties can name a
user. The only constructs that range over all addresses are the quantifiers of formulas and
`sum(m)`.

### 7.1 No cutoff for the reachable states

**Proposition 7.1.** No computable function c(P, φ) has the following property: for every
contract P and property φ, if φ holds in the reachable states of S_n for every n ≤ c(P, φ), then
φ holds in the reachable states of S_n for every n.

*Proof.* Let M be a deterministic two-counter machine. The contract P_M has integer fields
pc, r1, r2, steps, T, count, a boolean field halted and a map registered. Its procedure
`step()` runs one instruction of M unless halted, increments steps, and sets halted and
T := steps when M halts; `register()` requires `!registered[msg.sender]`, sets it, and
increments count. Let φ = `!(halted && count >= T)`. In the reachable states of S_n, count
takes exactly the values 0, ..., n; so φ fails in S_n iff M halts, after T steps, and T ≤ n. If c were computable,
M would halt iff T ≤ c(P_M, φ), which is decidable by running M for c(P_M, φ) steps. This
contradicts the undecidability of the halting problem for two-counter machines. ∎

The obstacle is an integer field that counts users; the formula has no quantifier. The
file `tests/contracts/parameterized/registry.sol` shows it on a small scale: `count <= 2` is
proved with 2 users (from the invariant `sum(registered) == count`), and refuted with 3.

### 7.2 Checks as first-order formulas

A check of Sect. 6 (a step of Houdini, or a property on a free state) is a verification
condition χ = P ⇒ Q: P the premises, Q a property or the candidates after a call. We read χ in
many-sorted first-order logic with a sort Addr, whose constants are null and the contracts;
a map is a function symbol from Addr to numbers or booleans, a field is a constant, and the
free state and the transaction are free symbols. χ is *valid with n users* if it holds in
every structure whose Addr part is A_n. The Lustre program of the check with n users
expresses exactly this; in particular the expansion of address quantifiers over A_n is
exact. This is an assumption on the encoder, like the correctness of the whole encoding.

χ is in the *fragment* if
* (F1) no map has address values;
* (F2) `sum` does not occur;
* (F3) in ¬χ, no address existential lies in the scope of a universal quantifier, unless the
  latter ranges over a finite domain independent of n (methods, booleans).

Let k(χ) be the number of address fields, plus the number of address existentials of ¬χ,
where an existential under a universal over a finite domain D counts |D| times, and the
existentials of the two sides of a disjunction of ¬χ count only for the larger side (their
witnesses can be shared). `Scanner.skolems` computes it in one pass over the formulas.

**Lemma 7.2 (substructure).** Let χ be in the fragment and k = k(χ). If χ is not valid with
n users, then it is not valid with n' users, for every n' with max(1, k) ≤ n' ≤ n.

*Proof.* Let M be a structure with n users in which ¬χ holds. By (F3), Skolemization turns
¬χ into a universal sentence ∀ȳ ψ, with ψ quantifier-free, at most k address constants (the
address fields and the Skolem constants of the address existentials), and Skolem functions
with values in the other sorts. Let D consist of F, the values of these constants (at most
k users), and further users of M up to n' users in total. By (F1), every function symbol
with values in Addr is a constant, whose value is in D. So the restriction M' of M to D
(the other sorts unchanged) is a substructure of M, and M' ⊨ ∀ȳ ψ, since universal
sentences hold in substructures. M' keeps null and the contracts, and `is_EOA` holds exactly
outside F; so M' is a structure with n' users in which ¬χ holds. ∎

**Theorem 7.3 (cutoff).** Let χ be in the fragment, and c ≥ max(1, k(χ)). If χ is valid
with c users, then it is valid with every n ≥ c users.

*Proof.* Lemma 7.2 with n' = c, by contraposition. ∎

Validity with c users does not imply validity with fewer users. The parameterized mode only
makes claims for n ≥ c.

### 7.3 Sums as state variables

**Lemma 7.4.** Let χ# be χ in which each `sum(m)` is a state variable σ_m (`ghost_sums`):
free in the free state; σ_m := σ_m − m[k] + v at each assignment `m[k] = v` (a transfer
keeps σ_balance); 0 for an unconstructed contract; the sum of the initial balances in the
initial states. For each map m whose entries are all nonnegative by the premises
(`forall u. m[u] >= 0` and `m[null] >= 0`, or the balance lemma), the premises of χ# also
contain m[a] ≤ σ_m and m[a] + m[b] ≤ σ_m for all a ≠ b (`Checks.sum_axioms`, with the guard
on construction of the candidates). If χ# is valid with n users, then χ is valid with n
users.

*Proof.* An instance of χ with n users is an instance of χ# with σ_m := Σ_a m[a]. The
updates keep σ_m equal to the sum of the entries, at every level of a call (by induction on
the levels; a revert restores both). The added premises hold when the entries are
nonnegative, which the premises of the instance give. ∎

χ# satisfies (F2), and the added premises are universal, so they do not change k. They
matter: with the invariant `sum(funds) <= balance[Bank]` (declared, or generated as a
reserve, Sect. 6), bank `Liquidity` is proved for every n ≥ 2; without them, nothing relates σ_funds to the entries, and the
counterexample to induction has `funds[u2] = 3 > balance[Bank] = 1`.

### 7.4 Counterexamples

**Lemma 7.5 (added users).** Suppose that a trace of S_c reaches a state where all contracts
are constructed and φ is false, and that no address variable of φ is universal in ¬φ
(address quantifiers, and the address parameters of `args` variables and of `h()`;
`Scanner.dual`). Then φ is false in a reachable state of S_n for every n ≥ c.

*Proof.* Consider the trace of S_n with the same transactions, in which u_{c+1}, ..., u_n
have initial balance 0 and send nothing. Each transaction reads and writes map entries only
at addresses of A_c, so each state of the new trace extends the corresponding state of the
old one with default values at the new users, and every sum is unchanged. Put ¬φ in negation
normal form: its address quantifiers are existential. By induction on ¬φ, a subformula true
in a state of S_c is true in its extension (for a modality, the transition from the
extension is the extension of the transition). ∎

For a property such as `exists a : address . ...` (price-bet `Winnability`), the new users
must also fail, and Lemma 7.5 does not apply. They fail if the trace leaves enough users
in the same situation. In a state s, a user u is *idle for* a balance b if every map entry
at u has its default value, `balance[u] = b`, and no address field of s holds u. For a
formula χ in negation normal form, need(χ) is the largest number, over the branches of χ,
of the address variables bound on the branch up to and including the last universal one
(0 if there is none); the address parameters of `args` variables and of `h()` count as
address variables. `Scanner.idle_needed(φ)` computes need(¬φ), which is 0 in the case of
Lemma 7.5.

**Lemma 7.6 (idle users).** Suppose that a trace of S_m reaches a state s where all
contracts are constructed and φ is false, and that s has at least need(¬φ) users idle for
the same balance b, with b = 0 if `sum(balance)` occurs in the contracts or in φ. Then φ is
false in a reachable state of S_n for every n ≥ m.

*Proof.* As in Lemma 7.5, the trace of S_n in which u_{m+1}, ..., u_n have initial balance
b and send nothing reaches a state s⁺ that extends s, and every new user is idle for b in
it; the sums are unchanged (the new entries are 0, and b = 0 if `sum(balance)` matters).
Two facts are used.

(a) Symmetry. Let π be a permutation of the users. The transition function commutes with
π (contracts and properties name no user, and compare addresses only with `==` and `!=`), so a
formula holds in a sequence of states (a state and its ancestors, which `old` reads) under
an assignment ν iff it holds in their images under π ∘ ν. If π exchanges two users that are
idle for b in every state of the sequence, and fixes the values of ν, then it maps each
state to itself; so the formula holds under ν iff it holds under π ∘ ν.

(b) Untouched users. A transaction whose sender and arguments are terms over the values of
ν, the constants and the fields reads and writes map entries and balances only at such
addresses, and assigns to the address fields only such addresses. So a user that is idle
and not a value of ν remains idle in the next state; so do the new users.

Let J be the users of s idle for b. By induction on a formula ψ in negation normal form (a
modality is self-dual, since the transition function is deterministic; ¬Φ(φ) has such a
form): if ψ holds, under an assignment ν into A_m, in a sequence of states of S_m that
starts at s and follows transactions over the values of ν, and at least need(ψ) users of J
are not values of ν, then ψ holds in the extended sequence under ν. Atoms take the same
values in both (their terms denote addresses of A_m; the sums are equal). The connectives,
the quantifiers over numbers, methods and booleans, and the modalities (by (b)) follow by
induction. For ∃x. ψ', the witness in A_m serves: it removes at most one user of J, and
need(∃x. ψ') = need(ψ') + 1 when need(ψ') > 0. For ∀x. ψ', a value in A_m is handled by
induction; for a new user a, take a user a' of J that is not a value of ν (there is one,
since need(∀x. ψ') ≥ 1): by (a), with π exchanging a and a', ψ' holds in the extended
sequence under ν[x ↦ a] iff it holds under ν[x ↦ a'], which follows by induction. Applied to
¬Φ(φ) at s, with ν empty, this gives ¬Φ(φ) at s⁺. ∎

BMC and the fuzzer give arbitrary initial balances to the users, so the idle users of a
counterexample often have different balances (price-bet_v4 `Liquidity`: 0, 47482 and
22317). The users outside the trace (neither a sender, nor a called address, nor an
argument of its transactions; the address fields, which start at null, only receive such
users) are neither read nor written by its transactions, unless the contracts use
`sum(balance)`. Setting their initial balances to 0 therefore gives a trace of S_m whose
final state is the old one with their balances 0. The tool checks exactly that φ is false
there (`concrete_check`), and then applies Lemma 7.6 with b = 0.

### 7.5 The parameterized mode

Each check uses its own number of users, the least one for which Thm. 7.3 applies to it.
Checks with different numbers of users combine as follows.

**Proposition 7.7.** Let C be the final set of Houdini, and suppose that the step of each
procedure f for C is valid with k_f ≥ max(1, k(χ#_f)) users. Let the check of a property φ on a
free state, with premises C' ⊆ C, be valid with u ≥ max(1, k(χ#_φ)) users. Then φ holds in
the reachable states of S_n for every n ≥ max(c_H, u), where c_H = max_f k_f.

*Proof.* Let n ≥ max(c_H, u). By Thm. 7.3 and Lemma 7.4, each step is valid with n users,
so C is inductive in S_n; it holds in the initial states (no contract is constructed), so
it holds in every reachable state. The check of φ is valid with n users for the same
reasons; so every reachable state, which satisfies C', satisfies φ. ∎

A proof on the transition system with N users (Kind 2) transfers to fewer users only.

**Corollary 7.8.** Suppose that need(¬φ) = 0, and that φ holds in the reachable states of
S_N where all contracts are constructed. Then the same holds in S_m for every m with
1 ≤ m ≤ N.

*Proof.* A reachable state of S_m where all contracts are constructed and φ is false gives
one in S_N, by Lemma 7.5 with c = m and n = N. ∎

With `--parameterized` (strategy portfolio), for n users asked for:
* `Checks.cutoff` bounds the counts from above, with all the templates of the invariant
  generator and the declared invariants as candidates: Houdini and the choice of premises
  only remove candidates, which does not increase k (premises add their counts, and the
  candidates after a call count for the largest one). A property is checked in parameterized
  mode if the steps and the property are in the fragment and N = max(c_H, c_R) ≤ n, with these
  bounds c_H (steps) and c_R (property); otherwise it is checked as without the option. The
  verdict says which;
* each step of Houdini uses the cutoff of the step for the current candidates
  (`Checks.step_count`); when Houdini ends, the invariants hold for every n' ≥ c_H, the
  largest of the cutoffs of the final steps (`_Invariants.users`);
* the check of the property uses the cutoff of its premises (`Checks.property_count`), possibly
  fewer users than Houdini; a proof (`inductive` or `invariants`) holds for every
  n' ≥ max(c_H, u) (Prop. 7.7), and the verdict gives both numbers;
* the searches for counterexamples are sound with any number of users; the search for the
  counterexample to induction uses the users of the check that produced it, fuzzing and
  Kind 2 use N users. A counterexample with m users holds for every n' ≥ m if Lemma 7.5 or
  Lemma 7.6 applies (`idle_users` counts the idle users of its final state: the fuzzer's
  state, the counterexample of the search, requested with its values, or that of a run of
  BMC after Kind 2, without the lemmas, so that Kind 2 stops at the counterexample), after
  setting to 0 the balances of the users outside the trace if needed. These confirmations
  get CONFIRM_SECONDS (10 s) each, also after the time limit of the property. Otherwise the
  counterexample holds for m users only; if m < n, the other searches go on, and the
  outcome is unknown if none decides;
* a proof by Kind 2 on the transition system with m users holds for m users (its
  invariants, IC3 and k-induction are about m users), and for every n' ≤ m if
  need(¬φ) = 0 (Cor. 7.8). Kind 2 starts with N users; after a proof with m < n users, it
  goes on with m + 1 users, up to n. Meanwhile the outcome is unknown, "true up to m users"
  (ground truth `OK-up to m users`), like "true up to k steps" for BMC; if need(¬φ) > 0,
  "true for N to m users". The scope gives what the run with m + 1 users reached ("true up
  to k steps", or "no verdict"). A proof with n users gives the verdict valid; a
  counterexample with m + 1 users is handled as above (it extends to n if Lemma 7.5 or
  7.6 applies). After the first proof, the other searches for counterexamples stop: one
  with m' ≤ m users that extends to every n' ≥ m' would extend to m. The check of the property
  on a free state goes on while it is open (it may prove φ for every n' ≥ max(c_H, u)).

For the step of procedure f, k(χ#) is the number of address fields, plus 1 for the sender,
plus the address parameters of f, plus the largest number of address universals of a
candidate (1 for the templates of Sect. 6), plus the address existentials of the declared
invariants (as premises). For a property, it is the number of address fields, plus the address
universals of the property, plus the latter term. An `args` variable counts the address
parameters of the procedures of the called contract other than the constructor (a method
variable does not denote a constructor, and the other parameters do not affect the call).
On bank, c_H = 2, and the properties need 1 or 2 users; on vault, the steps need 4 or 5 users
and the properties 3 and 8.

*Limits.* (1) Counterexamples are searched for with few users; one that needs more users
is not found (registry `At_most_two` is unknown for every n). A BMC of depth d would need up
to d(1 + p) + w users (p address parameters, w witnesses). (2) Properties such as additivity
P1_true, `forall c1 c2 . exists c3 v12 v3 . forall addr ...`, are outside (F3). (3) With
c = n, ghost sums are weaker than exact sums with n users, so a proof for exactly n users
can be lost (registry `At_most_two` with n = 2).

*Results* (10 s per property; PROGRESS.md, 2026-10-14). On the 46 properties of seven regression
files, the time is 62–71 s for n = 2, 3, 4 and 100 (normal mode: 71–78 s for n = 2, 3, 4,
and 457 s with 23 properties decided for n = 100); 43 verdicts are correct for n ≥ 3, and three
are unknown as expected (two counterexamples outside Lemma 7.5, one proof by Kind 2). On
bank, the three properties proved with 2 users are proved for every n ≥ 2 in 15–16 s, for any n
asked for; the normal mode with 100 users does not finish. With one number of users per
task, the verdicts on the regressions are unchanged, and most of their checks use 1 user;
on vault_v2, the counterexample of `Two_steps_drainability` is found with 5 users in 17 s
(75 s with 10 users, the former cutoff of the file).
