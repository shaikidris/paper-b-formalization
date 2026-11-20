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

- **EX2.4.** The [fast ordered reader](release-core/PaperB/ForestFastOrderedReader.lean)
  composes the fixed-bank dictionary sort and grouped static-tree layout.
  Its query proves exact proper loss, and the six retained columns have
  linear size. The raw incoming rows preserve labelled occurrences. The
  epoch-array pass visits each supplied predecessor occurrence once and
  removes duplicate predecessors only for forest tests. Finish their
  shared preparation and prove the complete preprocessing and peak-space
  bounds for that executable reader.
- **EX4.2–EX4.4.** An actual fresh event’s positive parent occurs earlier.
  The packed writer checks exact occupied records, including the artificial
  root and top-level identity records, and charges 18 word writes per job.
  Derive the chronological jobs and base values from the actual first
  labels and incoming rows. Connect the resulting records and intervals
  to the all-case original-vertex query.
- **EX5.1–EX5.4.** The dense runtime quotient preserves labelled adjacency,
  the root and topological rank. A shared stable grouping emits at most two
  local order entries per original vertex. The fixed RAM workers for LCA
  and search have checked costs, and the scalar search now returns from a
  relocated instruction slot. Instantiate the local orders and compose one
  fixed sealed builder and query. The oracle contract requires bounds and
  correctness for that same build and every later query.
- **EX5.5 and EX6.2.** Instantiate the checked listed-target and guarded
  detection reductions with the sealed oracle from EX5.4.

EX0, EX1 and EX3 are verified. Current counts and individual proof evidence
are in the [dashboard](DASHBOARD.md) and [task ledger](TASKS.md).

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
