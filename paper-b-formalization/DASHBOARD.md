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

- [EX2.4](TASKS.md#ex24) — The full successful-step invariant now checks for the actual packed callbacks. It constructs the new canonical embedding and preserves all old labels and physical slots. Totality and full increasing-order induction remain in progress.
- [EX4.2](TASKS.md#ex42) — The physical model now uses original DFS entry rank for exit extrema and a separate topological rank for quotient order. This distinguishes the two physical computations required for exact interval testing.
- [EX4.3](TASKS.md#ex43) — The actual exit-map traversal fuses jump selection and composition in a fixed-register tail loop, agrees with the ghost trace and uses one packed record probe and composition per step. Exact record installation remains in progress.
- [EX4.4](TASKS.md#ex44) — The exact span conversion recovers both actual witnesses using the retained inverse DFS entry and held-ID columns. Reader instantiation and machine execution remain in progress.
- [EX5.1](TASKS.md#ex51) — The word-machine midpoint is now a checked three-instruction executable block with exact arithmetic and register preservation. The charged binary-search and whole build remain open.
- [EX5.2](TASKS.md#ex52) — The arena and sealed prefix are reserved solely from declared input counts with the exact oracle contract bit width. Dense offsets, headers, retained words and legal query address ranges are bounded uniformly. Choose constant final block widths and instantiate the same built/queried machine programs in this layout.
- [EX5.3](TASKS.md#ex53) — The fixed RAM LCA worker is proved exact with ten registers, immutable head/parent/depth columns and 14k+19 executed instructions for k jumps. The complete sealed query remains in progress.
- [EX5.5](TASKS.md#ex55) — The listed-target transfer verifies the v1.3 mixed quadratic-log build plus linear-log per-target time, ordered output, and explicit-space bounds under the exact oracle contract. The whole-oracle instantiation remains open.
- [EX6.2](TASKS.md#ex62) — Shared baseline guard deletion now has a checked executable graph builder, exact linear scan counts and all-case path transfer. Next connect the checked rows and eventual single-index batch construction to actual detecting-set output.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

