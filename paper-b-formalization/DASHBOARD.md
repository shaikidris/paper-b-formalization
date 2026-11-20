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

- Completed work packages **17/27**. Planning audits **1** and verified proof packages **16**.
- Remaining work packages **10**. 9 in progress, 1 planned.
- Milestones 4 in progress, 3 verified.
- [EX2.2 unattended batch](unattended/README.md) has its own declaration-by-declaration status.

## In progress

- [EX2.4](TASKS.md#ex24) — The actual retained forest has checked constant-time known-node reads and logarithmic key lookup work.
- [EX4.2](TASKS.md#ex42) — The chronological sweep now has an exact prefix-occupancy model, with single fresh insertion and earlier/staged read bridges.
- [EX4.3](TASKS.md#ex43) — The fused prior-base callback now executes without building a reference route, with exact evaluation and word-read bounds under its occupancy invariant.
- [EX4.4](TASKS.md#ex44) — One runtime adapter supplies actual original-ID, dominance, LCA and child readers; full LCA and dominance correctness now hold on the original graph.
- [EX5.1](TASKS.md#ex51) — The actual Kahn order/inverse and original ID reader now give exact checked increasing and covering local arrays directly.
- [EX5.2](TASKS.md#ex52) — The canonical exit-map jump records now have an exact 18-word encoding and checked offset read. The same sealed arena and fixed code integration remain open.
- [EX5.3](TASKS.md#ex53) — Concrete setup instructions exist for all three calls. The exact first setup trace and no-wrap predecessor are Lean checked.
- [EX5.5](TASKS.md#ex55) — The listed-target transfer verifies the v1.3 mixed quadratic-log build plus linear-log per-target time, ordered output, and explicit-space bounds under the exact oracle contract. The whole-oracle instantiation remains open.
- [EX6.2](TASKS.md#ex62) — Under the exact single-target oracle contract, Lean checks the whole guarded application from shared deletion and grouped rows to the first actual detecting witness and complete negative answer. Full sealed oracle instantiation remains open.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

