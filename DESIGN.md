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
  A large next state gets fresh state variables s' with s' = next state (2026-10-24): the
  terms of nested modalities share subterms in Python, but the Lustre text, and every traversal
  as a tree, does not. With a method variable that is not expanded, the next state is an ite over
  all the procedures, and each such modality multiplies the size of the term by 70-80 (copies of
  lending-simple-real `Liquidation_attack_any`, 2 users: 4,200, 375,000 and 31 million nodes; its
  encoding did not end, and hung the cluster runs). A next state that a nested modality whose
  method is a variable takes as input is bound if it has more than `INLINE_BOUND` = 5,000 nodes,
  any other if it has more than `LAST_BOUND` = 10^6. Measured on all the properties with nested
  modalities (2 and 6 users): the inputs of `Liquidation_attack_any` have 37,000-3.3 million
  nodes, all the others at most 14,800 (AMM `Sandwich*` 2,900-7,300, lending
  `Liquidation_defence*` 4,200-14,800); a bound of 20,000 still left an input of 11,800 nodes
  before a method variable (150 s, 10 million nodes), 5,000 gives 12 s and 0.8 million. A first
  version bound every input of a nested modality above 5,000 nodes: the AMM `Sandwich*`
  properties (methods given) were bound too, and two refutations close to the time limit got
  slower (amm_real_v4 `Sandwich`: 238 s, then 308 s with ∃s', unknown at 600 s with ∀s'). Without
  parameters to quantify, s' is universal (∀s'. s' = t → ψ, equivalent to ∃s'. s' = t ∧ ψ since
  s' is determined): in positive position it becomes an input of the check, and the query has
  no quantifier. `free_vars` is memoized by node identity. The encoders stop at the time limit
  of the check (`lustre_subst.DEADLINE`, checked by `FormulaEncoder.phi` and `Inliner.run`,
  `EncodingTimeout`): the check is then unknown.
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
modalities: three free calls of the 10 methods of lending-simple-real give 1000 copies, whose
encoding did not finish in 5 minutes. So a method quantifier is expanded only if the
product of the numbers of methods of the expanded method quantifiers around it, and of
its own, is at most a bound (`--expand method:N`, default 32: every benchmark property so far
has at most 11 copies; two free calls of lending-simple-real, 100 copies, took 22 s to encode
instead of 3 s). The outer quantifiers are expanded first; the others stay quantified.
Neither choice is better on every property (30 s per property): with expansion, price-bet
`Liquidity` and lending-simple-real `Liquidation_defence_exists` are proved and are not without
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
(`(f > 0) == (g > 0)`, `f > 0 -> g > 0`, and `f == 0 -> g == 0` for fields without a sign,
e.g. the reserves of amm_real_v3: `supply == 0 -> r0 == 0`), holders (`∀u. !is_EOA(u) -> m[u] == 0`,
`m[null] == 0`; address quantifiers exclude null, so `m[null]` needs its own templates, or
`sum(m) == f` does not bound the entries of a free state), totals (`sum(m) == f`,
`sum(m) <= f`, `∀u. m[u] <= f`), reserves (`sum(m) == balance[C]`, `sum(m) <= balance[C]`
for each contract C: what the users can claim is held by C), definitions (`G -> f == e` and `G && d != 0 -> f * d == e'`
for the assignments `f = e` and `f = e' / d` under the conditions G of the enclosing ifs),
and, for an address field a, an address constant K (null or a contract) and a boolean field
g, `a == K`, `a != K`, `g -> a != K` and `!g -> a != K` (regression owner `P2_true`, for every
n, needs `owner != C`; price-bet `Winnability` needs `player_has_joined -> player != null`).
`sum(m)` is a new built-in (also for users): the sum of
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

**Existentials over numbers** (`direct.py`, 2026-10-23). A property with an existential over a
real in positive position (`fuzz.has_witness`; e.g. AMM `Swap_reversibility`, `exists y` the
amount that undoes a swap) was never decided through Kind 2: 29 of the 34 rows without a
verdict in `results/cluster-20261022-2304.csv`, while the same properties with an explicit
witness were proved in seconds. Two causes, both measured on the check of amm_simple_real
`Arbitrage_exists` with 1 user (Kind 2: unknown after 15 s):
* z3 has a complete procedure for quantified nonlinear real arithmetic (nlqsat), but it rejects
  the query ("not NRA"): the encoding puts divisions (`ite(b != 0, a / b, old)`) and if-then-else
  terms of number type under the quantifier, and z3's own rewritings (purify-arith,
  blast-term-ite) do not act under binders;
* Kind 2 asks with `check-sat-assuming`, so z3 uses its incremental solver (quantifier
  instantiation), never nlqsat. The rewritten query, asked this way, still timed out (20 s);
  z3's fallback parameters (`combined_solver.*`) do not apply with assumptions, and with
  push/pop only two of four queries were decided.

So for such properties the check on a free state and the exact check of the fuzzer at a
concrete state also go to z3 directly: the formula of the node property (`Checks.property_goals`
or `concrete_goal`, universal quantifiers hoisted as for Kind 2) is translated into a z3 term
(records become their fields, Lustre functions are inlined), rewritten under each quantifier —
a division a / b becomes a fresh variable d with `b != 0 -> b * d = a`, an if-then-else term
ite(c, x, y) a fresh variable v with `(c -> v = x) && (!c -> v = y)`, both bound at the innermost
quantifier around them (free constants outside) — and its negation is checked once, with
`(check-sat-using (then simplify nlqsat))`, by the z3 binary in the memory scope of the Kind 2
runs. Each fresh variable is determined by its definition (d when b != 0), so the rewriting is an
equivalence if every division is guarded: wherever a / b occurs, a context makes its value
irrelevant when b = 0 (`direct.check_guards`: the condition of an implication or of the branch of an
if-then-else, another conjunct, a disjunct b = 0, implying b != 0). Divisions of contract code are
guarded by def^i; a division written in a property may not be (the type checker only warns), and
then, as with integers, addresses or methods that are not constants, the check is outside the
fragment and goes to Kind 2 as before. Otherwise an unguarded `exists v . x / (y + v) > 0` would
become valid (d free when b = 0).

In the rounds (`_rounds`, task "proof"), for such a property the direct check comes first, for each
premise set, split into cases (as a whole, the AMM checks with the cutoff timed out; split, each
case takes at most 0.5 s); the cases share the budget, and those proved are kept for the next
rounds. The Kind 2 attempts follow. A model of a refuted case gives s* (only the state variables
that occur in the check: the property does not depend on the others, so a reachable state that
agrees with s* on them is a counterexample; no s* if a value is irrational) and the values of the
universal variables, printed with s*. The exact check of the fuzzer also goes to z3 directly, so
that a reachable state where no witness exists is a counterexample.

Scheduling, for these properties (2026-10-24; each change measured on the rows still open):
* the direct attempt of a premise set replaces its two Kind 2 forms, and gets their time (3
  budgets): through Kind 2 none of these checks was decided, and with 1 budget shared by 16 cases
  the refuted case of amm_real_v4 `Sandwich_slippage` was found or not depending on the time of
  the cases before it; the cases also start one later at each round;
* fuzzing gets the share of Kind 2 on the transition system (4 budgets), and Kind 2 1 budget;
* a search of the fuzzer is repeated until its time is over (it gives a few candidates per
  call: amm_simple_real_v3 `Sandwich_slippage` needed 13 exact checks, about 6 in 300 s before);
* the guided search proposes the closest state of each trace without the bounded evaluation as a
  filter (near the s* of amm_real_v4 `Sandwich_slippage`, the filter kept one state in 12 s);
* an exact check by z3 takes at most 5 s, and is not followed by Kind 2 (on amm_real_v4, an
  undecided one took the whole fuzzing budget of a round).

Results on the 29 rows with an existential over a number left unknown by the cluster run (every
n, against 600 s there): with 120 s per property and before these scheduling changes, 19 of the
21 true ones valid and 4 of the 8 false ones refuted; with 300 s and the changes (and the
template `f == 0 -> g == 0`, for amm_real_v3 `Deposit_reversibility`), 28 of 29: all the true
ones valid (most in under 5 s, amm_real `Sandwich_slippage` in 20 s), and the false ones refuted
in 5-240 s, except amm_int `Sandwich_slippage` (integers, outside `direct.py`).

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
A counterexample to induction s* guides the search (`Fuzzer.guided`): after the constructors,
at each step, of 20 random transactions that do not revert, the one whose state is closest to
s* is taken (with probability 0.2 a random one). The distance is the sum of the differences of
the numbers of s*, plus a constant for each other value that differs. The property is
evaluated as above, only at the states closer to s* than the earlier ones of their trace (the
evaluation takes most of the time). For a property with a witness, the candidate of a trace is
its closest state to s* where the bounded evaluation is false. s* is often unreachable, so the
BMC search for s* (task 3) fails, but reachable states near s* often violate the property. On
lending-simple-int (2 users), the counterexamples to induction of Liquidation_attack and
Liquidation_attack_exists violate the conservation of T0, and 1 random state in 64,776 has
a borrower and an attacker as in the premise of these attacks. The guided search finds a counterexample of
Liquidation_attack within 1 s (20 seeds out of 20; 2.2 s when the property is evaluated at
every state), and one of Liquidation_attack_exists within 8 s for 10 seeds out of 20.

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
4. Random testing, with exact confirmation: first guided by s*, once 2 has found it, then
   unguided.
5. Kind 2 on the transition system (as before; with BMC and k-induction only, after the
   memory limit of a run killed a solver: the invariant generators and IC3 run in parallel
   and each has its own solver, which exceeds the memory on nonlinear problems).

Verdicts say how they were found: `inductive` (an invariant proved by Houdini),
`invariants` (task 2), `reach` (task 3), `fuzz` (task 4), `kind2-<ENGINE>` (task 5, with the
engine of Kind 2 that found the verdict, in Kind 2's abbreviation: `kind2-BMC`, `kind2-IND`,
`kind2-IND2`, `kind2-IC3IA`, `kind2-IC3QE`; `kind2` if Kind 2 does not name it).

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

## 7. Parameterized mode: cutoffs on the number of users (`cutoff.py`, `--users_mode`)

A verdict obtained with n users says nothing, in general, about other numbers of users.
This section shows that no cutoff exists for the problem as a whole (Prop. 7.1), and that
each check on free values of Sect. 6 has a cutoff, computed syntactically, when it lies in a
fragment (Thm. 7.3). Sums over the addresses are outside the fragment; they are replaced by
state variables, which keeps the checks sound (Lemma 7.4). Counterexamples found with few
users extend to more users under a syntactic condition (Lemma 7.5). The parameterized mode
uses these results (Sect. 7.5); the combined mode, the default, runs it together with the
checks with n users, and the tool can also check a property for every number of users
(Sect. 7.6).

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
(`forall u. m[u] >= 0` and `m[null] >= 0`, also as conjuncts of the premises, or the balance
lemma), the premises of χ# also contain the set E_m of the universal formulas
∀ a_1 … a_k distinct. m[a_1] + … + m[a_k] ≤ σ_m, for k ≥ 1 (`Checks.sum_axioms`, with the
guard on construction of the candidates). With d addresses and nonnegative entries, E_m is
equivalent to the single formula Σ_a m[a] ≤ σ_m over the d addresses, which the tool emits.
If χ# is valid with n users, then χ is valid with n users.

*Proof.* An instance of χ with n users is an instance of χ# with σ_m := Σ_a m[a]. The
updates keep σ_m equal to the sum of the entries, at every level of a call (by induction on
the levels; a revert restores both). The added premises hold when the entries are
nonnegative, which the premises of the instance give: a sum of entries at distinct addresses
is at most the sum of all of them. ∎

χ# satisfies (F2), and the added premises are universal, so they hold in every substructure
and do not change k. They matter:
* with the invariant `sum(funds) <= balance[Bank]` (declared, or generated as a reserve,
  Sect. 6), bank `Liquidity` is proved for every n ≥ 2; without them, nothing relates σ_funds
  to the entries, and the counterexample to induction has `funds[u2] = 3 > balance[Bank] = 1`;
* the bounds of single entries and of pairs of entries (k ≤ 2, the first version) are too
  weak: the step of `redeem` of the AMM shares (`tests/contracts/parameterized/shares.sol`,
  amm-real `Shares`, `forall u v . u != v -> minted[u] + minted[v] <= supply`) needs 3 users,
  and with k ≤ 2 its counterexample to induction has `minted[u] = 2` for three users and
  σ_minted = supply = 4. On amm-real and amm-int (5 users), Houdini then dropped the declared
  invariants Nonnegative and Shares, and LP_exit was unknown.

When Houdini replays the counterexample of a step with the reference interpreter
(`Checks.refuted_after`), a sum of the free state is σ_m, not the sum of the visible entries:
the interpreter keeps the difference (`State.sum_offsets`), which a call does not change. Before
this, the replay could refute a true candidate such as `sum(minted) == supply`.

**Witness premises.** Let F = {null, C_1, ..., C_m}, and, for a map m with a state variable
σ_m, let W_m be σ_m ≠ Σ_{a ∈ F} m[a] → ∃u ∉ F. m[u] ≠ 0: if the entries at null and at the
contracts do not add up to σ_m, a user has a nonzero entry (`Checks.witness_axioms`).
* Lemma 7.4 also holds when the premises of χ# contain W_m: in the instance with
  σ_m := Σ_a m[a], if every user has entry 0, then σ_m is the sum of the entries at F.
* In ¬χ#, W_m reads σ_m = Σ_F m ∨ ∃u. (u ∉ F ∧ m[u] ≠ 0): one address existential, under
  no universal. So χ# stays in the fragment, and k grows by 1 for each W_m.
* If sum(m) occurs neither in the contracts, nor in the property, nor in the premises, W_m
  adds nothing: in a counterexample of the check without it, σ_m can be replaced by the sum
  of the entries at the addresses of the check, which satisfies W_m and E_m and changes
  nothing else (`Checks.witness_maps`).

They matter: in `contracts/regression/pool.sol`, `Someone_deposited`
(`total == 0 || exists a . deposit[a] > 0`, with the invariant `sum(deposit) == total`) holds
for every n. Without W_deposit, its check has the counterexample to induction where every
entry of the system is 0 and σ_deposit = total = 1: the depositor is a user outside the
system. Since each W_m adds a user, the tool assumes them only in the checks of the
properties, and only within the cutoff (Sect. 7.5). With the W_m of all the sums in every
check of a property, the cutoffs of 110 of the 277 benchmark properties with a cutoff would
grow (lending: from 4–6 to 7–11 users).

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
  verdict says which. The counts are computed for every property of the file, the lemmas
  and the invariants included, since any of them can be checked by name; a property without
  a count has no cutoff. With `--no_user_invariants`, the declared invariants are properties,
  not candidates: they are still in the program of the encoder, so their sums have state
  variables;
* each step of Houdini uses the cutoff of the step for the current candidates
  (`Checks.step_count`); when Houdini ends, the invariants hold for every n' ≥ c_H, the
  largest of the cutoffs of the final steps (`_Invariants.users`);
* the check of the property uses the cutoff of its premises (`Checks.property_count`), possibly
  fewer users than Houdini; a proof (`inductive` or `invariants`) holds for every
  n' ≥ max(c_H, u) (Prop. 7.7), and the verdict gives both numbers. After the checks without
  them, the check is also tried with the witness premises of its sums (Sect. 7.3), if its
  cutoff u, one more user for each of them, is at most N: so max(c_H, u) ≤ N still holds, and
  no cutoff changes;
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
can be lost (registry `At_most_two` with n = 2). (4) The witness premises are assumed only
within the cutoff, and not in the steps of Houdini.

*Results* (10 s per property; PROGRESS.md, 2026-10-14). On the 46 properties of seven regression
files, the time is 62–71 s for n = 2, 3, 4 and 100 (normal mode: 71–78 s for n = 2, 3, 4,
and 457 s with 23 properties decided for n = 100); 43 verdicts are correct for n ≥ 3, and three
are unknown as expected (two counterexamples outside Lemma 7.5, one proof by Kind 2). On
bank, the three properties proved with 2 users are proved for every n ≥ 2 in 15–16 s, for any n
asked for; the normal mode with 100 users does not finish. With one number of users per
task, the verdicts on the regressions are unchanged, and most of their checks use 1 user;
on vault_v2, the counterexample of `Two_steps_drainability` is found with 5 users in 17 s
(75 s with 10 users, the former cutoff of the file).

### 7.6 The combined mode, and every number of users

The parameterized mode decides fewer properties than the exact checks with n users in three
cases (limits above): ghost sums are weaker than exact sums, a proof by Kind 2 with N users
says nothing about n > N users, and a counterexample with N users may not extend to n.
The users mode (`--users_mode`, `verify.users_mode_of`) chooses the numbers of users:
`exact` (n users), `parameterized` (Sect. 7.5) or `combined` (the default).

A *side* is the check of a property with one number of users m (`_Side`, `_rounds`): the
tasks of Sect. 6, in rounds with doubling budgets, with ghost sums and the cutoffs of
Sect. 7.5 on the parameterized side. A side has a *goal*, the users its verdict is about
(n, or none for every n ≥ 1). On the parameterized side, a counterexample that does not
extend to the goal gives an unknown outcome, as in Sect. 7.5. The sides of a check advance
one round each in turn, in a fixed order, so Kind 2 runs one job at a time; each side has
its own budgets, so no time is split by a constant.

**Combined mode, n users** (`_drive_combined`). If the property has a cutoff N ≤ n, the
parameterized side P (N users) and the exact side E (n users), in this order; otherwise E
only. The first valid or invalid outcome is the verdict. P only proves: Houdini and the
check on a free state (tasks 1 and 2); it ends when that check is refuted under its
strongest premises. E searches for counterexamples with n users, and runs Kind 2 on the
transition system: on P, a proof by Kind 2 with N < n users would not decide n, and a
counterexample with N users decides n only if it extends. Kind 2 of E gets all the time
left (the rule of Sect. 6) only once P has ended. On the regressions (3 users, 10 s per
property), P with all the tasks took the first 7 s of owner `P2_true` (the search for its
counterexample to induction, and fuzzing), and E did not reach Kind 2, which proves it in
8 s in exact mode.

**Proposition 7.9.** Every verdict of the combined mode holds for n users.

*Proof.* A verdict of E is one with n users. A proof of P holds for every n' ≥ max(c_H, u)
(Prop. 7.7), and max(c_H, u) ≤ N ≤ n, since the cutoffs of the checks are bounded by those
of `Checks.cutoff`. A counterexample of P is a verdict only if it extends to every n' ≥ m
for its number of users m ≤ N ≤ n (Lemmas 7.5, 7.6). ∎

**Every number of users** (`n_participants` = `any`, `_drive_any`): the claim is that φ holds
in S_n for every n ≥ 1. With a cutoff c of the property, the sides are P (c users, no goal)
and the exact sides E_m for m = 1, ..., c − 1; without one, E_1. When P has not proved φ and
all the exact sides have ended before the deadline, the exact side with one more user
starts (best effort: a counterexample may need more users than the cutoff, e.g. registry
`At_most_two`). Kind 2 gets all the time left only on a side alone.

**Lemma 7.10.** If φ fails in S_m for some m ≥ 1, it does not hold for every n ≥ 1.
*Proof.* Immediate. ∎

So any counterexample is a verdict, also one of P that does not extend.

**Lemma 7.11.** If φ holds in S_n for every n ≥ L, and in S_m for every m < L, it holds for
every n ≥ 1. *Proof.* Immediate. ∎

P gives the first premise with L = max(c_H, u) (Prop. 7.7); L ≤ c, since the counts of
`Checks.cutoff` bound those of the checks (Sect. 7.5). The exact sides E_1, ..., E_{L−1} give
the second. If need(¬φ) = 0, Cor. 7.8 applies to every proof with M users, whatever its
method, since each one is about the reachable states of S_M: a proof on E_M (by Kind 2, or
by invariants) covers every m ≤ M, and so does the proof of P, with M = L. Then the proof of P
alone gives every n ≥ 1. Once P has proved φ for every n ≥ L, the exact sides E_m with
m ≥ L stop: they cannot change the verdict. Otherwise the outcome is unknown, with what is
proved: "true up to k users" (E_1, ..., E_k), "for m users" (proofs after the first gap),
"for every n ≥ L users" (P). If a side ended with an error (of Kind 2), the outcome is that
error, as with n users. A run of Kind 2 stopped at its time or memory limit before reporting
on the property (e.g. at the time limit while parsing the program of many users, where Kind 2
reports its timeout as an error) gives no verdict, not an error. In exact mode with `any`,
only the exact sides run.

The *scope* of an outcome (`Outcome.scope`) says what the run established, not what was
asked:
* n users, a verdict without the cutoff: "only for n users (cutoff c > n)" for a proof (or
  "(no cutoff: ...)"), "counterexample with n users"; without a verdict, the reason alone;
* n users, the cutoff c ≤ n: "for every n ≥ L users" for a proof of P (with "; property
  checked with u users" if u ≠ L); "only for n users" or "counterexample with n users" for
  a verdict of E; "no verdict with n users, nor with the cutoff c" without a verdict;
* parameterized mode: as above, and "counterexample with m users, for every n ≥ m (...)"
  for a counterexample of P that extends (Lemmas 7.5, 7.6);
* every n: "n ≥ L by invariants, n < L one by one", or "n < L by the proof(s) with M
  users, which hold(s) for fewer users" (Cor. 7.8); "counterexample with m users"; without a
  verdict, "true ...; no verdict with m users, ..., nor with the cutoff c".

### 7.7 Reduction by symmetry of the checks on free states (2026-10-24)

The checks on free states expand the address quantifiers into conjunctions over the addresses,
so a property with k universal address variables has about (n + |contracts|)^k cases with n
users: vault `Two_steps_drainability_non_inflation` (a, b, c, two method variables) has
9 (n + 1)^3 cases, 6561 with its cutoff of 8 users (2.1 MB of Lustre and 21 s of encoding with
5 users); lending `Health_non_interference` 456 cases with its cutoff 6. Most cases are the
same up to a renaming of the users.

Claim. Let G = ∀s. P(s) → Φ(s) be a check on a free state s, where P (the invariants, the
built-in facts, the sum and witness premises) names no user, i.e. P(π s) ⟺ P(s) for every
permutation π of the users (π acts on the keys of the maps, on the address values of the fields,
and leaves null, the contracts and the ghost sums unchanged). Let ∀a. ψ(a) be an address
quantifier of Φ in positive position: reached from the top of Φ only through conjunctions, the
conclusions of implications, universal quantifiers, and modalities whose next state is a term
(`inline`, no existential parameter), and let B be the users bound by such quantifiers around
it. Then G is valid iff it is valid with ∀a. ψ(a) replaced by the conjunction over the
contracts, the users of B, and one user not in B.
Argument. (1) The universal quantifiers in positive position can be moved to the front:
A → ∀a.ψ ⟺ ∀a.(A → ψ) and (∀a.ψ) ∧ χ ⟺ ∀a.(ψ ∧ χ) (a not free in A, χ), and
⟨t⟩∀a.ψ ⟺ ∀a.⟨t⟩ψ because the transition is a function that does not depend on a. So
G ⟺ ∀ā. ∀s. P(s) → Ψ(s, ā), with ā these variables. (2) For a permutation π of the users,
∀s. P(s) → Ψ(s, ā) ⟺ ∀s. P(s) → Ψ(s, π ā): substitute π s for s; P is invariant, and
Ψ(π s, π ā) ⟺ Ψ(s, ā) since Ψ names no user other than those of ā (its other address
quantifiers, not reduced, range over all the addresses, a set invariant under π; the
transitions commute with π, Sect. 7.4). (3) So G needs one tuple ā per orbit, i.e. per pattern
of equalities of its components with the users. A conjunction splits the check
(∀s. P → (ψ1 ∧ ψ2) is the conjunction of the checks of ψ1 and ψ2), so only the variables on one
path matter together; choosing each of them among the contracts, the users of the variables
before it on the path, and the next user gives one representative of each orbit.
The reduction stops at a disjunction: in (∀a.A) ∨ (∀b.B), the variables a and b must be chosen
together, and choosing b like a misses b = u2 when a = u1 (`tests/test_symmetry.py`, Either).
It also stops at negations, premises, existentials, the terms of a modality (sender, value and
arguments: a quantified boolean argument is a term, and its reduced value would be weaker; an
audit found a false property proved that way, `tests/test_symmetry.py`), and constructs other
than the above; it is
used for the property of a check on free states and for the conclusion of a step of Houdini,
never for a check at a concrete state (not invariant under π) or for Kind 2 on the transition
system (where it would weaken the induction hypothesis). `KINDHML_SYMMETRY=0` turns it off.

The number of users of the check, and so the cutoffs (Sect. 7.2-7.5), do not change: the free
state still has n users; only the cases of the conclusion are fewer. With the reduction, the vault
check has 135 cases for every n >= 3 (1.3 s of encoding with 8 users).

