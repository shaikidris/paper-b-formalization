# Paper B planning dashboard

Snapshot generated from the editable JSON ledgers. This dashboard tracks work and proof scope; it is not a build or mathematical certificate.

- Published edition inventory: 10 items, including 9 proof-bearing statements and Question 6.2.
- Work inventory: 27 packages in 7 milestones.
- Completed planning audits: 1.
- Certified main theorems: **1/2**. Certified numbered results: **4/9**.
- Assigned workers: 0; execution: LEAN_IMPLEMENTATION_IN_PROGRESS.
- Oracle milestone: Theorem 1.1, with one index built before the failures and target are named, including preprocessing, peak and retained words, query correctness and cost.
- First main proof milestone: Theorem 4.1, equality of both exit-tail sets under nested cuts before any LCA compression.

## Completed and remaining

- Completed work packages **15/27**. Planning audits **1** and verified proof packages **14**.
- Remaining work packages **12**. 9 in progress, 3 planned.
- Milestones 5 in progress, 2 verified.
- [EX2.2 unattended batch](unattended/README.md) has its own declaration-by-declaration status.

## In progress

- [EX1.5](TASKS.md#ex15) — The allocated packed jump region starts with exactly the root record and word-size header. The initialization and leaf storage fit within explicit linear word bounds. Use the actual initialized region with the full topological scan.
- [EX1.6](TASKS.md#ex16) — A binary search over sorted half-open child intervals returns exactly the child containing the queried preorder rank. Entry and exclusive stop endpoints, root and absence cases are checked. Wire the child ranges recorded by the actual ordinary tree and charge their construction.
- [EX2.4](TASKS.md#ex24) — The executable per-head prefix search and raw predecessor tests refine the semantic forest sweep step. The charged upper bound includes every depth call and the worst number of replayed predecessor probes. Instantiate the supplied node selectors on the jump arrays and implement the complete topological sweep.
- [EX4.2](TASKS.md#ex42) — A topological array driver installs a real pair map before its first base, preserves prior maps on repeated seeds and proves availability for actual fresh sources and earlier labelled predecessors. Instantiate the callbacks on the exact exit summary operations and charge the total graph scan and map traversals.
- [EX4.3](TASKS.md#ex43) — Lean composes and evaluates stored map records on the actual skew jump trace. The logged move, record probes and map operations have the required logarithmic traversal bound. Exact full record installation remains open.
- [EX4.4](TASKS.md#ex44) — Source and target failure, initially unreachable targets, and comparable failures are handled by exact early decisions. Comparable failures require only their higher dominator, in both orders and for duplicates. Integrate with the retained index and incomparable-pair branch.
- [EX5.1](TASKS.md#ex51) — The linear array bucket pass groups actual occurrences by owner or target, preserving order and repeats. All row initialization, reads, prepends, final reversals and references are explicitly counted. Instantiate the grouping on the concrete graph normalization and the finite sibling arc emitter, then lower the executions.
- [EX5.2](TASKS.md#ex52) — Dense offset tables certify disjoint fixed-word fields, a linear live arena and a linear sealed prefix under concrete graph count bounds. Width depends on a fixed layout allowance. Instantiate all block widths, bind the uniform worst-case capacities and connect actual programs to these regions.
- [EX5.5](TASKS.md#ex55) — The listed-target transfer verifies the v1.3 mixed quadratic-log build plus linear-log per-target time, ordered output, and explicit-space bounds under the exact oracle contract. The whole-oracle instantiation remains open.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

