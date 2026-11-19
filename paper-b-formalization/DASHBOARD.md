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

- Completed work packages **2/27**. Planning audits **1** and verified proof packages **1**.
- Remaining work packages **25**. 12 in progress, 13 planned.
- Milestones 2 in progress, 5 planned.
- [EX2.2 unattended batch](unattended/README.md) has its own declaration-by-declaration status.

## In progress

- [EX0.3](TASKS.md#ex03) — Lean verifies finite-word arithmetic, comparison, the lowbit primitive composition and a logarithmic address bound that counts every arc occurrence. The heap primitives and observation aggregation build. Actual program execution, live-layout and allocation bounds, and build/query trace integration remain open.
- [EX1.1](TASKS.md#ex11) — Lean verifies the induced graph on initially reachable original IDs preserves surviving path semantics for every failure predicate and exactly preserves the order and multiplicity of each retained outgoing list. Failed endpoints and initially unreachable targets are covered. The executable topological enumeration and charged ID compaction remain open.
- [EX1.2](TASKS.md#ex12) — Lean verifies the ordinary dominator tree semantically on every acyclic input, with ancestral equivalence on all reachable vertices. The proof refines any topological rank to an injective one and verifies strict descent for the parent. EX1.2’s tracker closure awaits EX1.1; the executable predecessor-LCA constructor remains under EX1.5.
- [EX1.3](TASKS.md#ex13) — Lean verifies the unique entry point of an arc into a dominator subtree and preservation of within-subtree paths from the root. Labelled quotient construction, flatness, projection, lifting, and occurrence counts remain open.
- [EX2.1](TASKS.md#ex21) — Lean identifies the two endpoints as exactly the distinct predecessors of an earliest proper loss. The characterization now feeds the topological sweep. Statement-level certification is pending.
- [EX2.2](TASKS.md#ex22) — Lean verified the bundled semantic Lemma 3.1 on a flat quotient with a supplied injective topological rank. The construction has exactly the canonical effective keys, a single artificial root, exact inclusive ancestor labels, nesting, fresh endpoint order and at most one real node per vertex in the count. Paper-level certification awaits the dependent input representation and statement audit.
- [EX2.3](TASKS.md#ex23) — Lean verified the growing-tree invariant, unique depth-target traversal, the logarithmic move bound, and the array-backed jump implementation under a preallocated word layout. A leaf insertion uses 14 word accesses. The traversal and ancestry test have explicit logarithmic word-read bounds. The full EX0.3 package and end-to-end statement audit remain open.
- [EX2.4](TASKS.md#ex24) — Lean verifies exact logarithmic prefix probing and its specialization to predecessor losses along a supplied nested cut chain. A separate array query decides proper loss on a correct interval layout. The executable depth-indexed predecessor test, forest sweep, deterministic pair dictionary, interval layout construction, and Word-RAM time and space remain open.
- [EX3.1](TASKS.md#ex31) — Lean checks the fresh-endpoint term on every real edge of the constructed forest of a supplied flat labelled quotient. The original-graph to labelled-quotient bridge remains open.
- [EX3.2](TASKS.md#ex32) — Lean checks the inherited term and converse on each real edge of the constructed forest. No overlap hypothesis is needed. The original-graph to labelled-quotient bridge remains open.
- [EX3.3](TASKS.md#ex33) — Lean verifies exact exit transfer on the constructed forest of a supplied flat labelled quotient and replays Figure 1's exact union terms and actual computed pair-parent edge and vertex labels. The original-graph quotient construction and EX3 dependencies remain open.
- [EX4.1](TASKS.md#ex41) — Lean verifies two-coordinate map composition and interval joins. Computed rank summaries compose over concatenation, and their endpoint test is equivalent to all listed tail ranks lying in the half-open subtree interval, with an explicit empty case. Integration with stored exit tails and bounded word accounting remain open.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

