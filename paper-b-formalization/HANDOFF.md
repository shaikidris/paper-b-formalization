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

- **EX2.4.** The [packed builder](release-core/PaperB/ForestBuildPackedWords.lean)
  retains at most 19 words per quotient vertex and agrees with the prepared
  reader. [Known-node membership](release-core/PaperB/ForestPackedMembership.lean)
  uses four word probes. The [fixed dictionary run](release-core/PaperB/ForestPackedLookupRun.lean)
  has logarithmic fuel and feeds the checked query continuation. The
  [construction certificate](release-core/PaperB/ForestCheckpointCertificate.lean)
  accounts for selected operations and live storage on the actual reader.
  EX2.4 still requires a complete work and peak-space bound for that same
  construction, including the packed serialization pass.
- **EX4.2–EX4.4.** The [depth-aware sweep](release-core/PaperB/ExitDirectDepthInv.lean)
  preserves the initialized depth column through packed writes.
  [Fresh-slot correctness](release-core/PaperB/ExitClosedOverlay.lean)
  extends the decoded live records while preserving prior paths.
  Instantiate the invariant on the chronological quotient forest, including
  root and top-level seeds, and bind the certified reads to
  [all original-vertex cases](release-core/PaperB/AllOrigOracleCases.lean).
- **EX5.1–EX5.4.** [Physical row accounting](release-core/PaperB/PhysicalArcRowMass.lean)
  preserves arc multiplicity across the shared emitter. The [fixed pair search](release-core/PaperB/RamPairHitRow.lean)
  halts within logarithmic fuel and returns the exact hit row, and the
  [child search](release-core/PaperB/RamChildRow.lean) binds the scalar worker
  to physical child intervals. Complete all sealed columns, link the fixed
  query and builder, and prove the [oracle contract](release-core/PaperB/OracleContract.lean)
  for the same build and every later query.
- **EX5.5 and EX6.2.** Instantiate the checked listed-target and guarded
  detection reductions with the sealed oracle from EX5.4.

EX0, EX1 and EX3 are verified. The [dashboard](DASHBOARD.md) and
[task ledger](TASKS.md) record coverage and link each verified checkpoint.
Eligible public or self-contained Lean tasks run through Personal Generic.
Private source, unpublished proof work, and the private ledger stay in the
local checkout during this Generic run. Checkpoint receipts record the API
project and reported usage for new Generic calls.

Run from the repository root with Elan and Python 3 available.

```sh
python3 -B paper-b-formalization/plan.py validate
python3 -B paper-b-formalization/test_plan.py
(cd paper-b-formalization/release-core && lake build)
(cd paper-b-formalization/release-core && lake env lean ../evidence/paper-41-transfer-certified/Audit.lean)
```

Record the exact declaration, build, statement audit and axioms before
marking a result certified. The repository is private.
