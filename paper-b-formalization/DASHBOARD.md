# Paper B planning dashboard

Snapshot generated from the editable JSON ledgers. This dashboard tracks work and proof scope; it is not a build or mathematical certificate.

- Published edition inventory: 10 items, including 9 proof-bearing statements and Question 6.2.
- Work inventory: 27 packages in 7 milestones.
- Completed planning audits: 1.
- Certified main theorems: **0/2**. Certified numbered results: **2/9**.
- Assigned workers: 0; execution: LEAN_IMPLEMENTATION_IN_PROGRESS.
- Oracle milestone: Theorem 1.1, with one index built before the failures and target are named, including preprocessing, peak and retained words, query correctness and cost.
- First main proof milestone: Theorem 4.1, equality of both exit-tail sets under nested cuts before any LCA compression.

## Completed and remaining

- Completed work packages **10/27**. Planning audits **1** and verified proof packages **9**.
- Remaining work packages **17**. 8 in progress, 9 planned.
- Milestones 4 in progress, 2 planned, 1 verified.
- [EX2.2 unattended batch](unattended/README.md) has its own declaration-by-declaration status.

## In progress

- [EX1.4](TASKS.md#ex14) — At the ordinary-tree LCA of two incomparable failures, both failures lie strictly below it in distinct actual sibling blocks. Bundle these facts with the branch lemmas over all original targets.
- [EX1.5](TASKS.md#ex15) — Executable LCA folding over nonempty reachable predecessor slots computes the greatest common ancestor and charges each predecessor occurrence once. The word version refines the semantic fold with aggregated probe and record charges. Run the fold on each topologically processed vertex; prove that the prefix tree matches original dominance and accounts for all charged operations.
- [EX1.6](TASKS.md#ex16) — The static heavy-path LCA kernel uses only supplied correct head, depth, parent and subtree-size tables. The proof checks exactness and logarithmic light-edge crossings. Construct and verify the actual head table and static child interval lookup.
- [EX2.4](TASKS.md#ex24) — Balanced merging builds a deterministic sorted distinct candidate-key array with exact member semantics and a logarithmic comparison-depth bound. Disjoint bounded slot spans support a two-bank layout. Refine the list recursion to the bounded two-bank execution and integrate the candidate node pointer array.
- [EX3.2](TASKS.md#ex32) — Lean checks the inherited term and converse on each real edge of the constructed forest. No overlap hypothesis is needed. The original-graph to labelled-quotient bridge remains open.
- [EX3.3](TASKS.md#ex33) — Lean now instantiates exit transfer on the actual Fin-labelled sibling quotient built from original DAG arcs. It carries the exact physical tail. Figure 1 replays. Whole task and paper-statement acceptance await EX1.3 and EX2 evidence and the dependent task checklist.
- [EX4.1](TASKS.md#ex41) — Lean verifies two-coordinate map composition and interval joins. Computed rank summaries compose over concatenation, and their endpoint test is equivalent to all listed tail ranks lying in the half-open subtree interval, with an explicit empty case. Integration with stored exit tails and bounded word accounting remain open.
- [EX4.2](TASKS.md#ex42) — The exact first seed of a real parent is earlier than its child seed. Every fresh endpoint and each map on the relevant ancestor path is available before the new pair seed. Instantiate this interface on the constructed proper-loss forest and finish predecessor source reads.

## Ready to start

- EX6.1 — Prove the guarded-path and shrinking-witness equivalence.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

