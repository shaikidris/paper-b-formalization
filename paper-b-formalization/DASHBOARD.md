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

- Completed work packages **3/27**. Planning audits **1** and verified proof packages **2**.
- Remaining work packages **24**. 12 in progress, 12 planned.
- Milestones 2 in progress, 5 planned.
- [EX2.2 unattended batch](unattended/README.md) has its own declaration-by-declaration status.

## In progress

- [EX1.1](TASKS.md#ex11) — The path-preserving equivalence for the actual compact graph transports arbitrary deleted predicates through inverse IDs, including length-zero paths and endpoints. Combine with executable failure-set and target encoding and decreasing-index model.
- [EX1.2](TASKS.md#ex12) — Lean verifies the ordinary dominator tree semantically on every acyclic input, with ancestral equivalence on all reachable vertices. The proof refines any topological rank to an injective one and verifies strict descent for the parent. EX1.2’s tracker closure awaits EX1.1; the executable predecessor-LCA constructor remains under EX1.5.
- [EX1.3](TASKS.md#ex13) — Lean verifies the actual finite quotient’s path equivalence and flatness. Across all distinct reachable roots the emitted adjacency arrays contain at most m original arc occurrences. The actual vertex-copy bound and formal task closure remain open.
- [EX1.5](TASKS.md#ex15) — Lean verifies the semantic LCA recurrence on all reachable predecessors. The executable growing-tree fold and topological scan, resource costs and full constructor proof remain open.
- [EX2.1](TASKS.md#ex21) — Lean identifies the two endpoints as exactly the distinct predecessors of an earliest proper loss. The characterization now feeds the topological sweep. Statement-level certification is pending.
- [EX2.2](TASKS.md#ex22) — Lean verified the bundled semantic Lemma 3.1 on a flat quotient with a supplied injective topological rank. The construction has exactly the canonical effective keys, a single artificial root, exact inclusive ancestor labels, nesting, fresh endpoint order and at most one real node per vertex in the count. Paper-level certification awaits the dependent input representation and statement audit.
- [EX2.3](TASKS.md#ex23) — Lean verified the growing-tree invariant, unique depth-target traversal, the logarithmic move bound, and the array-backed jump implementation under a preallocated word layout. A leaf insertion uses 14 word accesses. The traversal and ancestry test have explicit logarithmic word-read bounds. The full EX0.3 package and end-to-end statement audit remain open.
- [EX2.4](TASKS.md#ex24) — Lean verifies exact predecessor cutoff, pair lookup and proper-loss query on a correct layout. A new executable DFS stack writes entry and exit arrays with verified per-step counts and sizes. Establish complete traversal and exact table values, then wire the sweep and costs.
- [EX3.1](TASKS.md#ex31) — Lean checks the fresh-endpoint term on every real edge of the constructed forest of a supplied flat labelled quotient. The original-graph to labelled-quotient bridge remains open.
- [EX3.2](TASKS.md#ex32) — Lean checks the inherited term and converse on each real edge of the constructed forest. No overlap hypothesis is needed. The original-graph to labelled-quotient bridge remains open.
- [EX3.3](TASKS.md#ex33) — Lean now instantiates exit transfer on the actual Fin-labelled sibling quotient built from original DAG arcs. It carries the exact physical tail. Figure 1 replays. Whole task and paper-statement acceptance await EX1.3 and EX2 evidence and the dependent task checklist.
- [EX4.1](TASKS.md#ex41) — Lean verifies two-coordinate map composition and interval joins. Computed rank summaries compose over concatenation, and their endpoint test is equivalent to all listed tail ranks lying in the half-open subtree interval, with an explicit empty case. Integration with stored exit tails and bounded word accounting remain open.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

