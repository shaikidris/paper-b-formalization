# Paper B planning dashboard

Snapshot generated from the editable JSON ledgers. This dashboard tracks work and proof scope; it is not a build or mathematical certificate.

- Published edition inventory: 10 items, including 9 proof-bearing statements and Question 6.2.
- Work inventory: 27 packages in 7 milestones.
- Completed planning audits: 1.
- Certified main theorems: **0/2**. Certified numbered results: **0/9**.
- Assigned workers: 1; execution: LEAN_IMPLEMENTATION_IN_PROGRESS.
- Oracle milestone: Theorem 1.1, with one index built before the failures and target are named, including preprocessing, peak and retained words, query correctness and cost.
- First main proof milestone: Theorem 4.1, equality of both exit-tail sets under nested cuts before any LCA compression.

## In progress

- [EX0.2](TASKS.md#ex02) — Lean proves exit transfer for nested cuts in a flat acyclic quotient. The constructed forest still needs to supply distinctness and nesting. The costed oracle signature remains open.
- [EX2.1](TASKS.md#ex21) — Lean identifies the two endpoints as exactly the distinct predecessors of an earliest proper loss. The characterization now feeds the topological sweep. Statement-level certification is pending.
- [EX2.2](TASKS.md#ex22) — Carbon's first two checkpoints build. They prove the predecessor-loss equivalence and global loss nesting. It is now working on the case where an entering predecessor is outside the cut.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

