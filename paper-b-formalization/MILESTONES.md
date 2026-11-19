# Paper B formalization milestones

The work packages come from tasks.json. Use their dependencies to schedule parallel work. The counts distinguish planning from proof acceptance.

## EX0 — Freeze the graph, algorithm and cost contracts

Pin the source and toolchain. Elaborate two candidate Lean types with their full quantifiers and cost units.

Work packages: 3; planning audits complete: 1; verified proof packages: 2.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [EX0.1](TASKS.md#ex01) — Freeze paper identities and statement locations | contract | DONE_PLAN | none |
| [EX0.2](TASKS.md#ex02) — Pin the environment and elaborate candidate interfaces | contract | VERIFIED | EX0.1 |
| [EX0.3](TASKS.md#ex03) — Define execution and storage units | cost model | VERIFIED | EX0.2 |

## EX1 — Build the dominator and labelled quotient interface

Prove the semantic quotient and last-exit results. Supply costed dominator and static tree indices for the executable branch.

Work packages: 6; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [EX1.1](TASKS.md#ex11) — Normalize original vertices and failure sets | graph | IN_PROGRESS | EX0.2 |
| [EX1.2](TASKS.md#ex12) — Characterize the ordinary dominator tree | dominator | IN_PROGRESS | EX1.1 |
| [EX1.3](TASKS.md#ex13) — Project and lift labelled sibling paths | dominator | IN_PROGRESS | EX1.2 |
| [EX1.4](TASKS.md#ex14) — Characterize partial-block reachability | dominator | IN_PROGRESS | EX1.3 |
| [EX1.5](TASKS.md#ex15) — Construct the ordinary dominator tree within the oracle budget | dominator | IN_PROGRESS | EX1.2, EX0.3, EX2.3 |
| [EX1.6](TASKS.md#ex16) — Implement static tree intervals, child lookup and LCA | dominator | PLANNED | EX1.2, EX0.3 |

## EX2 — Build the forest of effective separating pairs

Construct one record per effective pair, prove membership by ancestry and bound the charged predecessor scans.

Work packages: 4; planning audits complete: 0; verified proof packages: 1.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [EX2.1](TASKS.md#ex21) — Identify the first proper loss | cuts | IN_PROGRESS | EX1.1 |
| [EX2.2](TASKS.md#ex22) — Prove the topological forest invariant | cuts | IN_PROGRESS | EX2.1 |
| [EX2.3](TASKS.md#ex23) — Implement depth jumps under leaf insertion | data structures | VERIFIED | EX0.3 |
| [EX2.4](TASKS.md#ex24) — Charge forest construction and membership | cuts | IN_PROGRESS | EX2.2, EX2.3 |

## EX3 — Prove the exit-set transfer identity

Independently replay Theorem 4.1 on the constructed forest, including disjoint pairs. Preserve original tails and check Figure 1.

Work packages: 3; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [EX3.1](TASKS.md#ex31) — Lift each fresh endpoint contribution | cuts | IN_PROGRESS | EX2.2, EX1.3 |
| [EX3.2](TASKS.md#ex32) — Handle inherited tails and the reverse inclusion | cuts | IN_PROGRESS | EX3.1 |
| [EX3.3](TASKS.md#ex33) — Certify the set-level transfer theorem | cuts | IN_PROGRESS | EX3.2 |

## EX4 — Implement compressed exit summaries and queries

Prove the chronological construction, constant-size map composition and all online cases for the executable index.

Work packages: 4; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [EX4.1](TASKS.md#ex41) — Implement the two-coordinate map algebra | oracle | IN_PROGRESS | EX3.3, EX1.2 |
| [EX4.2](TASKS.md#ex42) — Install maps before bases in topological order | oracle | PLANNED | EX4.1, EX2.4 |
| [EX4.3](TASKS.md#ex43) — Build and evaluate composed jump maps | oracle | PLANNED | EX4.2, EX2.3, EX1.6 |
| [EX4.4](TASKS.md#ex44) — Decide arbitrary post-build queries | oracle | PLANNED | EX1.4, EX4.3, EX1.5 |

## EX5 — Certify a single oracle and its resource bounds

Tie correctness and all four time and space bounds to the same build and query programs, and derive the batch corollary.

Work packages: 5; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [EX5.1](TASKS.md#ex51) — Account for discovery and every edge scan | cost model | PLANNED | EX0.3, EX2.4, EX4.3, EX1.5, EX1.6 |
| [EX5.2](TASKS.md#ex52) — Bound peak workspace and the retained index | cost model | PLANNED | EX5.1 |
| [EX5.3](TASKS.md#ex53) — Bound each later query and exclude adjacency access | cost model | PLANNED | EX4.4, EX5.2 |
| [EX5.4](TASKS.md#ex54) — Join correctness and costs in the oracle theorem | integration | PLANNED | EX5.3 |
| [EX5.5](TASKS.md#ex55) — Derive the listed-target Boolean vector | application | PLANNED | EX5.4 |

## EX6 — Transfer to a supplied healthy-zero guarded output

Account for every guard incidence and target and recover a detecting admissible set.

Work packages: 2; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [EX6.1](TASKS.md#ex61) — Prove the guarded-path and shrinking-witness equivalence | application | PLANNED | EX1.1 |
| [EX6.2](TASKS.md#ex62) — Account for all label and terminal incidences | application | PLANNED | EX6.1, EX5.5 |

