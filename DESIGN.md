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
  `value`, one field `f_x` per parameter of each procedure, optionally `block_num`).
* For each procedure `f`, a Lustre `function trans_<C>_<f>(s: St; t: Tx) returns (r: St)`
  whose local variables `l1, ..., lm` are the levels `StateVars^1..StateVars^m`; its equations are
  exactly `S^0(s0; s)`, and `r` is the ITE of `Trans_f`.
  Kind 2 inlines these functions, which performs the substitution yielding `χ_v`.
* `function trans(s: St; t: Tx) returns (r: St)` is the switch of `Trans` / `Trans_C`.
* The main node has inputs `t: Tx` and the initial user balances, and a state stream
  `s = init -> pre trans(s, t)`; `Init` constrains the initial balances by an `assert`.
* The property is `--%PROPERTY "<Rule>" Φ(φ)`, where `Φ(φ)` is an expression over `s`.

### Encoding of formulas

The modal tree of the paper is built explicitly. A node `V` is represented by a Lustre term of
type `St`: the root is `s`, and the child reached through the edge `E` labelled
`⟨e_s : C.e_f(ē) $ e_v⟩` is `trans(term(V), tx(E))`, where `tx(E)` is the record literal
`Tx { sender = Φ(e_s); cx = C; fx = Φ(e_f); value = Φ(e_v); <EqParams>; others = 0 }`.

This replaces the literal `∃SVars^{V'} ∃TVars^E` of the paper by substitution. It is equivalent:
`Trans` is a function of `(SVars, TVars)` (Lemma `lem:transition`), and all transition variables
that affect `Trans` are fixed by the equalities of the modality, except those listed below, which
remain existentially quantified (as scalar variables):

* the parameters of a procedure called through a `method` variable without an `args` argument,
  written `h()` (extension, see §4);
* the block number of the transaction, if the contract uses `block.number` (extension, see §4).

Quantification over records breaks the BMC and k-induction engines of Kind 2, so an `args`
variable is expanded into one scalar variable per element of `ParamVars` (as in the paper).
`old(e)` at node `V` is encoded at the parent of `V`.

## 3. Assumptions of the paper (A1–A7) and how they are enforced

* A1 (finite addresses/methods): `n_participants` user addresses from the command line.
* A2 (maps indexed by addresses): type checker.
* A3 (guarded divisions in formulas): type checker (warning or error), def-guards in contracts.
* A4 (acyclic calls): desugaring rejects cycles.
* A5 (transaction guards): `desugar.py` adds them explicitly.
* A6 (no `sender`/`value` in formulas): type checker.
* A7 (each `args` variable in exactly one modality): type checker.

## 4. Deviations from the paper

Each item is also recorded as a `\CL{...}` note in the paper.

1. **uint.** A field or parameter of type `uint` is an integer. An assignment of a negative value
   to a `uint` field reverts; a negative actual value for a `uint` parameter reverts. Quantified
   `uint` variables, and the components of `args` variables for `uint` parameters, range over
   the naturals.
2. **null sender.** Transactions whose sender is `null` revert (extra premise of A5).
3. **block.number.** State variable `block_num` (initially 0) and transition variable
   `Tx.block_num`. A transaction sets `block_num = Tx.block_num` before `initPay`; as for any
   state variable, a revert restores the old value. The environment only produces
   `Tx.block_num ≥ block_num`, and in a modality the value is existentially quantified over
   `≥ block_num`.
4. **`h()` with a method variable.** Allowed; the parameters are existentially quantified
   (this is what the literal `∃TVars^E` of the paper gives when `EqParams` is empty).
5. Open questions (to be decided): domain of `address` quantifiers; guard on unconstructed
   states. See `PROGRESS.md`.
