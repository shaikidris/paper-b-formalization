# Paper B Lean formalization handoff

Use the [dashboard](DASHBOARD.md) and [task ledger](TASKS.md) for current status.
The statement ledger is pinned to [v1.2](https://doi.org/10.5281/zenodo.24339761).
Use [published v1.3](https://doi.org/10.5281/zenodo.24350515) for the current
resource targets.

## Certified structural results

- [Lemma 2.1](evidence/paper-21-siblings-certified/fidelity.md) certifies the
  finite flat sibling quotients. It carries the physical tail and records
  which quotient receives each retained original arc occurrence.
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

- EX1 finishes the combined last-exit case split and the costed ordinary
  dominator and static tree builders. The unique dominator ancestry and
  lowest common ancestor semantics are verified.
- EX2 finishes the executable growing forest sweep and the reuse of
  deterministically sorted keys. The retained DFS array values, word
  accesses for jump primitives, and predecessor stamp pass already build.
- EX4 stores and advances the two exit maps and vertex bases in topological
  order. The exact set theorem supplies correctness of the map constants.
- EX5 connects the actual index builder and queries to one charged word
  machine execution. EX6 reduces healthy-zero guarded outputs to the
  listed-target interface.

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
