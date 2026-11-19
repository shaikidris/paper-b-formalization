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

- Completed work packages **14/27**. Planning audits **1** and verified proof packages **13**.
- Remaining work packages **13**. 8 in progress, 5 planned.
- Milestones 5 in progress, 2 verified.
- [EX2.2 unattended batch](unattended/README.md) has its own declaration-by-declaration status.

## In progress

- [EX1.4](TASKS.md#ex14) — At the ordinary-tree LCA of two incomparable failures, both failures lie strictly below it in distinct actual sibling blocks. Bundle these facts with the branch lemmas over all original targets.
- [EX1.5](TASKS.md#ex15) — The executable dominator step uses the actual packed jump-region implementation. Lean verifies correct prefix ancestry, the fresh leaf ancestor law and array-backed folding and insertion. Build the initialized word region and run the concrete step over the full Kahn order.
- [EX1.6](TASKS.md#ex16) — The executable head-table sweep writes exactly one head per vertex in preorder and produces a valid array-backed static heavy-path LCA lookup from correct parent and size arrays. Instantiate the ordinary-tree layout, add the child interval lookup and charge all packed array construction phases.
- [EX2.4](TASKS.md#ex24) — The executable per-head prefix search and raw predecessor tests refine the semantic forest sweep step. The charged upper bound includes every depth call and the worst number of replayed predecessor probes. Instantiate the supplied node selectors on the jump arrays and implement the complete topological sweep.
- [EX4.2](TASKS.md#ex42) — A topological array driver installs a real pair map before its first base, preserves prior maps on repeated seeds and proves availability for actual fresh sources and earlier labelled predecessors. Instantiate the callbacks on the exact exit summary operations and charge the total graph scan and map traversals.
- [EX4.3](TASKS.md#ex43) — Lean composes and evaluates stored map records on the actual skew jump trace. The logged move, record probes and map operations have the required logarithmic traversal bound. Exact full record installation remains open.
- [EX5.1](TASKS.md#ex51) — The linear array bucket pass groups actual occurrences by owner or target, preserving order and repeats. All row initialization, reads, prepends, final reversals and references are explicitly counted. Instantiate the grouping on the concrete graph normalization and the finite sibling arc emitter, then lower the executions.
- [EX5.5](TASKS.md#ex55) — The listed-target transfer verifies the v1.3 mixed quadratic-log build plus linear-log per-target time, ordered output, and explicit-space bounds under the exact oracle contract. The whole-oracle instantiation remains open.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

