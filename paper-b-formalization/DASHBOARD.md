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

- Completed work packages **6/27**. Planning audits **1** and verified proof packages **5**.
- Remaining work packages **21**. 10 in progress, 11 planned.
- Milestones 2 in progress, 5 planned.
- [EX2.2 unattended batch](unattended/README.md) has its own declaration-by-declaration status.

## In progress

- [EX1.2](TASKS.md#ex12) — Lean verifies the ordinary dominator tree semantically on every acyclic input, with ancestral equivalence on all reachable vertices. The proof refines any topological rank to an injective one and verifies strict descent for the parent. EX1.2’s tracker closure awaits EX1.1; the executable predecessor-LCA constructor remains under EX1.5.
- [EX1.3](TASKS.md#ex13) — The actual finite sibling quotient vertex keys sum to at most twice the original vertex count over distinct root IDs. Discharge the predecessor task certificates before closing EX1.3.
- [EX1.4](TASKS.md#ex14) — For a proper loss under two distinct nonroot failures, both original-tail sets in the finite flat quotient are nonempty, including a direct exit to the target. Instantiate on constructed sibling quotients and prove surviving original paths iff one usable exit in the remaining third-block case.
- [EX1.5](TASKS.md#ex15) — Lean verifies the predecessor-LCA characterization and the logarithmic deepest-common-depth search. Jump getter instantiation, topological fold and whole-constructor costs remain open.
- [EX2.2](TASKS.md#ex22) — Lean verified the bundled semantic Lemma 3.1 on a flat quotient with a supplied injective topological rank. The construction has exactly the canonical effective keys, a single artificial root, exact inclusive ancestor labels, nesting, fresh endpoint order and at most one real node per vertex in the count. Paper-level certification awaits the dependent input representation and statement audit.
- [EX2.4](TASKS.md#ex24) — The interval traversal over the actual child buckets executes exactly 2N commands and empties its stack. Table value refinement and sweep integration remain open.
- [EX3.1](TASKS.md#ex31) — Lean checks the fresh-endpoint term on every real edge of the constructed forest of a supplied flat labelled quotient. The original-graph to labelled-quotient bridge remains open.
- [EX3.2](TASKS.md#ex32) — Lean checks the inherited term and converse on each real edge of the constructed forest. No overlap hypothesis is needed. The original-graph to labelled-quotient bridge remains open.
- [EX3.3](TASKS.md#ex33) — Lean now instantiates exit transfer on the actual Fin-labelled sibling quotient built from original DAG arcs. It carries the exact physical tail. Figure 1 replays. Whole task and paper-statement acceptance await EX1.3 and EX2 evidence and the dependent task checklist.
- [EX4.1](TASKS.md#ex41) — Lean verifies two-coordinate map composition and interval joins. Computed rank summaries compose over concatenation, and their endpoint test is equivalent to all listed tail ranks lying in the half-open subtree interval, with an explicit empty case. Integration with stored exit tails and bounded word accounting remain open.

## Ready to start

- EX6.1 — Prove the guarded-path and shrinking-witness equivalence.

See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).

See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).

