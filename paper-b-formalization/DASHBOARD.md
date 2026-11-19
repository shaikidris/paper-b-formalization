# Paper B planning dashboard

Snapshot generated from the editable JSON ledgers. This dashboard tracks work and proof scope; it is not a build or mathematical certificate.

- Published edition inventory: 10 items, including 9 proof-bearing statements and Question 6.2.
- Work inventory: 27 packages in 7 milestones.
- Completed planning audits: 1.
- Certified main theorems: **1/2**. Certified numbered results: **3/9**.
- Assigned workers: 0; execution: LEAN_IMPLEMENTATION_IN_PROGRESS.
- Oracle milestone: Theorem 1.1, with one index built before the failures and target are named, including preprocessing, peak and retained words, query correctness and cost.
- First main proof milestone: Theorem 4.1, equality of both exit-tail sets under nested cuts before any LCA compression.

## Completed and remaining

- Completed work packages **12/27**. Planning audits **1** and verified proof packages **11**.
- Remaining work packages **15**. 6 in progress, 9 planned.
- Milestones 3 in progress, 2 planned, 2 verified.
- [EX2.2 unattended batch](unattended/README.md) has its own declaration-by-declaration status.

## In progress

- [EX1.4](TASKS.md#ex14) — At the ordinary-tree LCA of two incomparable failures, both failures lie strictly below it in distinct actual sibling blocks. Bundle these facts with the branch lemmas over all original targets.
- [EX1.5](TASKS.md#ex15) — Lean verifies the actual dominator construction step using the previously checked predecessor-fold semantics. The concrete JumpOps backend and end-to-end scan remain.
- [EX1.6](TASKS.md#ex16) — The static heavy-path LCA kernel uses only supplied correct head, depth, parent and subtree-size tables. The proof checks exactness and logarithmic light-edge crossings. Construct and verify the actual head table and static child interval lookup.
- [EX2.4](TASKS.md#ex24) — Balanced merging builds a deterministic sorted distinct candidate-key array with exact member semantics and a logarithmic comparison-depth bound. Disjoint bounded slot spans support a two-bank layout. Refine the list recursion to the bounded two-bank execution and integrate the candidate node pointer array.
- [EX4.1](TASKS.md#ex41) — The min/max preorder summary decodes to the exact ordinary-tree LCA of each finite physical-tail set. Joining intervals refines empty-aware LCA join, and the composable two-coordinate maps preserve this decoding. Instantiate the interval contract on the actual ordinary-tree index and account stored word records.
- [EX4.2](TASKS.md#ex42) — Each physical exit-tail set is exactly the union of entering-arc contributions: direct exits from the endpoint and all valid earlier proper-loss predecessor tails. Build the executable map and base sweep over these labelled occurrences and its prefix invariant.

## Ready to start

- EX6.1 — Prove the guarded-path and shrinking-witness equivalence.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

