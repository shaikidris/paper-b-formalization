# Paper B planning dashboard

Snapshot generated from the editable JSON ledgers. This dashboard tracks work and proof scope; it is not a build or mathematical certificate.

- Published edition inventory: 10 items, including 9 proof-bearing statements and Question 6.2.
- Work inventory: 27 packages in 7 milestones.
- Completed planning audits: 1.
- Certified main theorems: **0/2**. Certified numbered results: **0/9**.
- Assigned workers: 0; execution: LEAN_IMPLEMENTATION_IN_PROGRESS.
- Oracle milestone: Theorem 1.1, with one index built before the failures and target are named, including preprocessing, peak and retained words, query correctness and cost.
- First main proof milestone: Theorem 4.1, equality of both exit-tail sets under nested cuts before any LCA compression.

## Completed and remaining

- Completed work packages **1/27**. Planning audits **1** and verified proof packages **0**.
- Remaining work packages **26**. 5 in progress, 21 planned.
- Milestones 2 in progress, 5 planned.
- [EX2.2 unattended batch](unattended/README.md) has its own declaration-by-declaration status.

## In progress

- [EX0.2](TASKS.md#ex02) — Lean proves exit transfer for nested cuts in a flat acyclic quotient. The constructed forest still needs to supply distinctness and nesting. The costed oracle signature remains open.
- [EX2.1](TASKS.md#ex21) — Lean identifies the two endpoints as exactly the distinct predecessors of an earliest proper loss. The characterization now feeds the topological sweep. Statement-level certification is pending.
- [EX2.2](TASKS.md#ex22) — Lean verified the bundled semantic Lemma 3.1 on a flat quotient with a supplied injective topological rank. The construction has exactly the canonical effective keys, a single artificial root, exact inclusive ancestor labels, nesting, fresh endpoint order and at most one real node per vertex in the count. Paper-level certification awaits the dependent input representation and statement audit.
- [EX2.3](TASKS.md#ex23) — Lean verified the growing-tree invariant, unique depth-target traversal, the logarithmic move bound, and the array-backed jump implementation under a preallocated word layout. A leaf insertion uses 14 word accesses. The traversal and ancestry test have explicit logarithmic word-read bounds. The full EX0.3 package and end-to-end statement audit remain open.
- [EX2.4](TASKS.md#ex24) — Lean checks the computed DFS preorder interval equivalence for inclusive ancestry, its specialization to real cut-pair nodes and quotient labels, and its equivalence to exact proper loss. The proof covers self-membership and exclusion at the right endpoint. All ten original candidate errors are resolved. Conditional charging and the separate numeric prefix-probe count also build. The cutoff and logarithmic-fuel proofs, executable constructor, deterministic dictionary, array-backed constant-time query and end-to-end time and space bounds remain open.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

