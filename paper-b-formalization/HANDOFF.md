# Paper B Lean formalization handoff

Begin with [the dashboard](DASHBOARD.md), [the task ledger](TASKS.md), and [the v1.3 implementation targets](../evidence/paper-b-log-shave-20261118/formalization-v1.3.md). The statement ledger is pinned to [v1.2](https://doi.org/10.5281/zenodo.24339761). Use [published v1.3](https://doi.org/10.5281/zenodo.24350515) for current resource targets.

## Checked baseline

- [Forest.lean](release-core/PaperB/Forest.lean) proves the semantic proper-loss forest on a flat quotient with a supplied injective topological rank.
- [Jumps.lean](release-core/PaperB/Jumps.lean) proves the depth-target search and logarithmic move count. Its array-backed refinement counts word accesses under a preallocated layout.
- [ForestIntervals.lean](release-core/PaperB/ForestIntervals.lean) proves inclusive ancestor membership using half-open intervals in the computed DFS preorder. The real-pair corollary gives exact proper-loss membership for quotient vertex labels. [Lean replay and audit](evidence/ex24-ancestry-interval/verification.json)
- [ForestBuild.lean](release-core/PaperB/ForestBuild.lean) proves conditional charging. Constructor execution and its space bounds remain open.
- [PrefixProbe.lean](evidence/public-lean-prefix-probe/PrefixProbe.lean) implements the numeric prefix search and proves the probe count is bounded by fuel. The cutoff theorem and the width-to-fuel proof remain open.

## Next checkpoints

- EX0 is verified. The [oracle contract](release-core/PaperB/OracleContract.lean) fixes the quantifiers and the [word-machine lifecycle](release-core/PaperB/RamLifecycle.lean) defines the four resource observations from a sealed build and later query. The actual graph encoding, bytecode and asymptotic budgets belong to the implementation milestones.
- EX1.1 has exact reachability marks for a supplied order and verified indegree preprocessing. Finish the Kahn queue invariant and prove the emitted order is topological, then construct and charge compact ID tables.
- EX1.3 has original DAG sibling blocks, the path correspondence and abstract flatness. Finish the finite labelled adjacency representation, rank and occurrence bounds.
- EX2.4 has exact logarithmic predecessor cutoff and an array-backed query for a correct layout. Finish the executable depth-indexed sweep, deterministic pair dictionary and layout construction, then connect the machine cost proof.

Run from the repository root with Elan and Python 3 available.

```sh
python3 -B paper-b-formalization/plan.py validate
python3 -B paper-b-formalization/test_plan.py
(cd paper-b-formalization/release-core && lake build)
(cd paper-b-formalization/release-core && lake env lean ../evidence/ex03-ram-lifecycle/Audit.lean)
```

Save each patch against its base and report the Lean build, theorem types, and axiom audit. Update `tasks.json` and run `plan.py render` after each checked checkpoint.

This repository is private. For API work on a sharing-enabled project, use the published paper and self-contained public exercises. Repository access and private ledger or proof payloads belong on an approved non-sharing route.
