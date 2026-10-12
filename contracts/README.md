# Benchmarks

A verification task is a pair (contract, property). The benchmarks are grouped in
*families*: a base contract, its variants (mutations), and the properties they share. The
directory `regression/` is not a family: each of its files holds a contract and its rules,
with the ground truth in `// @groundtruth: True|False` comments.

## Layout of a family

```
amm-real/
  amm_real.sol       base contract (no rules)
  amm_real_v2.sol .. variants; the first comment describes the mutation
  spec.hml           the properties shared by all the contracts (rules and invariants)
  amm_real_v2.hml    optional: rules for amm_real_v2.sol only
  lemmas.hml         optional: helper invariants (not tasks)
  groundtruth.csv    the expected verdict of each task
```

The rules of a contract `C.sol` are those of `spec.hml`, in order; the rules of `C.hml`, if
present, replace the rules of the same name and add the others. A contract file of a family
holds no rules.

`lemmas.hml` holds invariants that only help the proofs. They are not tasks and have no
ground truth. With the default strategy, the tool proves them, together with the invariants
of the spec, and assumes those proved when it checks the rules. The option `--no_lemmas`
leaves them out, and `--no_user_invariants` leaves out all declared invariants as candidates
(the invariants of the spec are still verified, as tasks).

`groundtruth.csv` has one row per task, with the columns:

- `contract`: the contract file, e.g. `amm_real_v2.sol`;
- `property`: the name of the rule or invariant;
- `expected`: `true`, `false` or `unknown`;
- `note`: optional, usually why the property fails or holds in this contract.

For an invariant, `true` means that it holds in every reachable state (where all contracts
are constructed), not that it is inductive.

The test `test_family_groundtruth_covers_the_tasks` checks that the rows are exactly the
tasks of the family.

## Families

| family | contracts | notes |
|---|---|---|
| `amm-real`, `amm-simple` | constant-product AMM, with and without liquidity tokens | real amounts |
| `amm-int`, `amm-simple-int` | the same, with integer amounts | divisions round down |
| `lending`, `lending-simple` | lending protocol | real amounts |
| `lending-int` | `lending` with integer amounts | fixed point |
| `bank`, `vault`, `price-bet` | small contracts | |

A variant whose properties must be stated differently (e.g. with other types, as the
integer versions) is the base of a new family, not a variant.
