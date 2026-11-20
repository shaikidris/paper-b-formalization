# Paper B Lean formalization handoff

Use the [dashboard](DASHBOARD.md) and [task ledger](TASKS.md) for current status.
The statement ledger is pinned to [v1.2](https://doi.org/10.5281/zenodo.24339761).
Use [published v1.3](https://doi.org/10.5281/zenodo.24350515) for the current
resource targets.

## Certified structural results

- [Lemma 2.1](evidence/paper-21-siblings-certified/fidelity.md) certifies the
  finite flat sibling quotients. It carries the physical tail and records
  which quotient receives each retained original arc occurrence.
- [Lemma 2.2](evidence/paper-22-last-exit-certified/fidelity.md) certifies
  the complete last-exit case split, including the two nonempty physical
  exit sets and the original-tree LCA test for a third block.
- [Lemma 3.1](evidence/paper-31-forest-certified/fidelity.md) certifies the
  proper-loss forest, its inclusive ancestry test, and its real parent edges.
- [Theorem 4.1](evidence/paper-41-transfer-certified/fidelity.md) certifies
  the exact union identity for both exit-tail sets before compression.
  Figure 1 checks that each of the two contribution terms is necessary.

The [oracle contract](release-core/PaperB/OracleContract.lean) and
[word machine lifecycle](release-core/PaperB/RamLifecycle.lean) fix the
quantifiers and resource observations. The structural proofs and source
normalization already build on the pinned Lean toolchain.

## Next checkpoints

- EX0, EX1 and EX3 are verified. The original DAG build produces the
  static reader with exact inclusive dominance, child lookup, and LCA.
- EX2.4 now runs the complete executable ordered sweep, builds the exact
  per-quotient DFS membership index and proves operation counts over its
  real trace. The retained query reader projects only six arrays.
  Prove that the counted calls pay for the packed word operations, account
  for dictionary construction and DFS, and discharge peak workspace on
  the same builder.
- EX4 joins the verified chronological fresh-event index to the indexed
  first-install schedule and the actual incoming-arc exit fold. Install
  the composed jump maps, then bind the all-case original-vertex query
  to the retained physical columns.
- EX5 has verified fixed RAM workers for static LCA and binary search,
  fixed-code relocation, a dense quotient slot layout and exact
  occurrence ownership. Materialize the actual local quotient rows,
  assemble one sealed build/query program and prove its full resource
  bounds. Apply the accepted oracle to the guarded listed-target transfer
  in EX5.5 and EX6.2.

Run from the repository root with Elan and Python 3 available.

```sh
python3 -B paper-b-formalization/plan.py validate
python3 -B paper-b-formalization/test_plan.py
(cd paper-b-formalization/release-core && lake build)
(cd paper-b-formalization/release-core && lake env lean ../evidence/paper-41-transfer-certified/Audit.lean)
```

Record the exact declaration, build, statement audit and axioms before
marking a result certified. The repository is private. Private Lean source
and ledgers use the approved non-sharing route.
