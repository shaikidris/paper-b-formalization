# Paper B Lean formalization handoff

Begin with [the dashboard](DASHBOARD.md), [the task ledger](TASKS.md), and [the v1.3 implementation targets](../evidence/paper-b-log-shave-20261118/formalization-v1.3.md). The statement ledger is pinned to [v1.2](https://doi.org/10.5281/zenodo.24339761). Use [published v1.3](https://doi.org/10.5281/zenodo.24350515) for current resource targets.

## Checked baseline

- [Forest.lean](release-core/PaperB/Forest.lean) proves the semantic proper-loss forest on a flat quotient with a supplied injective topological rank.
- [Jumps.lean](release-core/PaperB/Jumps.lean) proves the depth-target search and logarithmic move count. Its array-backed refinement counts word accesses under a preallocated layout.
- [ForestBuild.lean](release-core/PaperB/ForestBuild.lean) proves conditional charging. Constructor execution and its space bounds remain open.
- [PrefixProbe.lean](evidence/public-lean-prefix-probe/PrefixProbe.lean) implements the numeric prefix search and proves the probe count is bounded by fuel. The cutoff theorem and the width-to-fuel proof remain open.

## Next EX2.4 checkpoint

Finish elaborating the interval candidate against the pinned toolchain. The candidate replay below gives the same assembled file as the two verified list and membership patches. Ten compiler errors remain in the tree and bucket-count proofs. After the replay builds, prove that a known real pair is an inclusive ancestor of a vertex label exactly when its preorder interval contains that label. Keep this correctness statement separate from the time and space proof for the executable index.

Run from the repository root with Elan and Python 3 available.

```sh
python3 -B paper-b-formalization/plan.py validate
python3 -B paper-b-formalization/test_plan.py
(cd paper-b-formalization/release-core && lake build)
```

Replay the interval candidate in a scratch directory. This elaboration currently fails at the documented open goals.

```sh
repo="$PWD"
scratch="$(mktemp -d)"
evidence="$repo/paper-b-formalization/evidence/public-lean-interval-assembly"
cp "$evidence/ForestIntervals.base.lean.txt" "$scratch/ForestIntervals.lean"
(cd "$scratch" && git apply --unidiff-zero "$evidence/ForestIntervals.patch")
(cd paper-b-formalization/release-core && lake env lean "$scratch/ForestIntervals.lean")
```

Save each patch against its base and report the Lean build, theorem types, and axiom audit. Update tasks.json and run plan.py render after a checked checkpoint. The complete EX2.4 contract also needs the actual executable constructor, dictionary and index operations, and the corresponding time and space bounds.

This repository is private. For API work on a sharing-enabled project, use the published paper and self-contained public exercises. Repository access and private ledger or proof payloads belong on an approved non-sharing route.
