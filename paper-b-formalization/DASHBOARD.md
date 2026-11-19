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

- Completed work packages **16/27**. Planning audits **1** and verified proof packages **15**.
- Remaining work packages **11**. 9 in progress, 2 planned.
- Milestones 5 in progress, 2 verified.
- [EX2.2 unattended batch](unattended/README.md) has its own declaration-by-declaration status.

## In progress

- [EX1.6](TASKS.md#ex16) — The actual jump words produce valid static-tree columns, and Lean proves that static parent ancestry gives original DAG dominance on reachable vertices. Final constructor and packed reader composition remains in progress.
- [EX2.4](TASKS.md#ex24) — The root embedding and both exact installation branches are checked. Lean recovers canonical parent and depth on allocation, canonical node identity on reuse, and absence of the new key from all old occupied slots.
- [EX4.2](TASKS.md#ex42) — Lean checks the executable array schedule with one visit per vertex, at most one map installation and exact agreement with reference map/base semantics. The actual first-allocation schedule and physical reader bindings remain in progress.
- [EX4.3](TASKS.md#ex43) — The actual exit-map traversal fuses jump selection and composition in a fixed-register tail loop, agrees with the ghost trace and uses one packed record probe and composition per step. Exact record installation remains in progress.
- [EX4.4](TASKS.md#ex44) — All branches for two reachable incomparable failures are verified under the exact static, key, membership and physical-span readers. Both exit orientations are checked. Actual packed read bindings and other original inputs remain in progress.
- [EX5.1](TASKS.md#ex51) — The word-machine midpoint is now a checked three-instruction executable block with exact arithmetic and register preservation. The charged binary-search and whole build remain open.
- [EX5.2](TASKS.md#ex52) — The arena and sealed prefix are reserved solely from declared input counts with the exact oracle contract bit width. Dense offsets, headers, retained words and legal query address ranges are bounded uniformly. Choose constant final block widths and instantiate the same built/queried machine programs in this layout.
- [EX5.5](TASKS.md#ex55) — The listed-target transfer verifies the v1.3 mixed quadratic-log build plus linear-log per-target time, ordered output, and explicit-space bounds under the exact oracle contract. The whole-oracle instantiation remains open.
- [EX6.2](TASKS.md#ex62) — Lean checks the linear grouping of supplied residual guard and terminal incidences on the existing decoder model. The per-label query has at most two distinct failures, all terminal occurrences, and exact residual semantics. Shared residual graph and whole-oracle instantiation remain open.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

