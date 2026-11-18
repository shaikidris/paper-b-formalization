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
- [EX2.2](TASKS.md#ex22) — Lean verified the local sweep transition and the global sweepChain_spec for every vertex of a flat ranked quotient. The global result gives canonical, nested, duplicate-free labels with exact proper-loss membership. The shared parent forest and linear node bound remain open. The semantic sweep carries no executable resource claim.
- [EX2.3](TASKS.md#ex23) — Lean verified the record-prefix persistence theorem and the skew-push block-sum and ordering invariants from the Carbon checkpoint. The complete growing-tree validity and traversal code requires further Lean repairs. Logarithmic traversal and the physical word-operation bounds remain open.
- [EX2.4](TASKS.md#ex24) — The native Carbon Medium swarm started a dedicated constructor and accounting worker. The executable constructor and resource proof are pending.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

