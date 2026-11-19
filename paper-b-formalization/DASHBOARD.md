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
- [EX1.6](TASKS.md#ex16) — The executable static layout constructs exact inclusive subtree interval tests, sizes from exclusive stops, valid heavy children and head arrays, and cached child interval records from packed parent/depth arrays. Prove ordering and total charges for the actual ordinary-tree buckets and wire the bounded child lookup.
- [EX2.4](TASKS.md#ex24) — The executable per-head step writes one label, allocates at most one new pair node and uses the exact key lookup to reuse existing nodes without changing their stored parent. It preserves grounded packed jump memory and charges at most 18 logical writes. Close the Ready embedding induction over all processed heads and compose the graph input preparation and memory charges.
- [EX4.2](TASKS.md#ex42) — A topological array driver installs a real pair map before its first base, preserves prior maps on repeated seeds and proves availability for actual fresh sources and earlier labelled predecessors. Instantiate the callbacks on the exact exit summary operations and charge the total graph scan and map traversals.
- [EX4.3](TASKS.md#ex43) — Lean composes and evaluates stored map records on the actual skew jump trace. The logged move, record probes and map operations have the required logarithmic traversal bound. Exact full record installation remains open.
- [EX4.4](TASKS.md#ex44) — Executable post-build routing and answer evaluation use only typed retained-index primitive reads. Finite control budgets distinguish constant and logarithmic operations and preserve orientation. Prove all leaf meanings using the exact original-DAG cases and instantiate query primitives on the sealed packed index.
- [EX5.1](TASKS.md#ex51) — One standard right shift computes an unsigned half in the fixed word machine. Lean verifies the exact register, preserved fields and one-instruction trace. Use this in the fixed binary search and packed query lowering.
- [EX5.2](TASKS.md#ex52) — The arena and sealed prefix are reserved solely from declared input counts with the exact oracle contract bit width. Dense offsets, headers, retained words and legal query address ranges are bounded uniformly. Choose constant final block widths and instantiate the same built/queried machine programs in this layout.
- [EX5.5](TASKS.md#ex55) — The listed-target transfer verifies the v1.3 mixed quadratic-log build plus linear-log per-target time, ordered output, and explicit-space bounds under the exact oracle contract. The whole-oracle instantiation remains open.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

