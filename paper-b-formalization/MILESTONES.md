# Paper B formalization milestones

Generated from tasks.json. Milestone numbers group work; dependencies determine order. Planning completion is separate from proof acceptance.

## PB0 — Freeze scope, statement surface and build environment

A small, approved graph/RAM contract and a reproducible supported toolchain; no theorem proof inferred from setup.

Work packages: 5; planning audits complete: 2; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [PB0.1](TASKS.md#pb01) — Pin the active draft and published baseline | coordinator | DONE_PLAN | none |
| [PB0.2](TASKS.md#pb02) — Audit existing Lean and registry reuse | coordinator | DONE_PLAN | PB0.1 |
| [PB0.3](TASKS.md#pb03) — Approve selected roots and module ownership | coordinator | READY | PB0.1, PB0.2 |
| [PB0.4](TASKS.md#pb04) — Elaborate a nonvacuous statement and cost surface | coordinator | PLANNED | PB0.3, PB0.5 |
| [PB0.5](TASKS.md#pb05) — Pin and rehearse the supported environment | infrastructure | PLANNED | PB0.3 |

## PB1 — Graph semantics, normalization and dominators

A finite explicit DAG model, failure semantics and actual preprocessing contracts.

Work packages: 5; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [PB1.1](TASKS.md#pb11) — Define per-query reachability and the answer vector | graph | PLANNED | PB0.4, PB0.5 |
| [PB1.2](TASKS.md#pb12) — Normalize input while preserving every query answer | graph | PLANNED | PB1.1, PB4.1 |
| [PB1.3](TASKS.md#pb13) — Prove single-failure and domination semantics | graph | PLANNED | PB1.1 |
| [PB1.4](TASKS.md#pb14) — Construct the dominator tree and LCA index | graph | PLANNED | PB1.2, PB1.3, PB1.5 |
| [PB1.5](TASKS.md#pb15) — Implement indices, answer maps and timestamp arrays | resources | PLANNED | PB1.2, PB4.1 |

## PB2 — Two-failure residual kernel

An executable kernel answers arbitrary original targets and tests proper cuts, with proved construction charges.

Work packages: 7; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [PB2.1](TASKS.md#pb21) — Vertex-split capacities and deletion correspondence | kernel | PLANNED | PB1.1, PB1.3 |
| [PB2.2](TASKS.md#pb22) — Bounded augmentation and max-cut certificate | kernel | PLANNED | PB2.1, PB1.5 |
| [PB2.3](TASKS.md#pb23) — Decompose the two flow paths | kernel | PLANNED | PB2.2 |
| [PB2.4](TASKS.md#pb24) — Compute residual path-rank labels | kernel | PLANNED | PB2.3 |
| [PB2.5](TASKS.md#pb25) — Prove arbitrary-target residual membership | kernel | PLANNED | PB2.3, PB2.4 |
| [PB2.6](TASKS.md#pb26) — Recognize proper cuts at a proposed vertex | kernel | PLANNED | PB1.4, PB2.5 |
| [PB2.7](TASKS.md#pb27) — Join kernel correctness and construction resources | kernel | PLANNED | PB2.6, PB1.5 |

## PB3 — Threshold scheduler correctness

Every original query receives its exact Boolean answer; direct positives, kernel positives and negatives, root arrivals and final negatives are covered.

Work packages: 4; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [PB3.1](TASKS.md#pb31) — Define the all-query reverse-topological scheduler | scheduler | PLANNED | PB1.2, PB1.5, PB0.4 |
| [PB3.2](TASKS.md#pb32) — Maintain the surviving-suffix invariant | scheduler | PLANNED | PB3.1 |
| [PB3.3](TASKS.md#pb33) — Verify Resolve and positive/negative retirement | scheduler | PLANNED | PB3.2, PB2.6 |
| [PB3.4](TASKS.md#pb34) — Prove vector correctness, completeness and termination | scheduler | PLANNED | PB3.3 |

## PB4 — End-to-end time and workspace

All-query Theorem 3.2: one implemented vector solver, complete scan/target/construction charges and peak live words.

Work packages: 6; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [PB4.1](TASKS.md#pb41) — Ground the operational and live-space model | resources | PLANNED | PB0.4, PB0.5 |
| [PB4.2](TASKS.md#pb42) — Amortize every completed kernel by retirement | resources | PLANNED | PB3.3, PB4.1 |
| [PB4.3](TASKS.md#pb43) — Charge stale positive/negative labels and original targets | resources | PLANNED | PB3.4, PB4.1 |
| [PB4.4](TASKS.md#pb44) — Prove peak words including complete answer storage | resources | PLANNED | PB4.1, PB4.2, PB4.3, PB2.7 |
| [PB4.5](TASKS.md#pb45) — Close all-query Theorem 3.2 on original inputs | coordinator | PLANNED | PB1.4, PB2.7, PB3.4, PB4.2, PB4.3, PB4.4 |
| [PB4.6](TASKS.md#pb46) — Derive threshold corollaries and the existential projection | coordinator | PLANNED | PB4.5 |

## PB5 — Exact historical-set sharing

Proposition 3.3, plus explicit representation examples, with its original time bound.

Work packages: 4; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [PB5.1](TASKS.md#pb51) — Represent immutable exact historical sets | sharing | PLANNED | PB3.1, PB4.1 |
| [PB5.2](TASKS.md#pb52) — Refine the answer-vector scheduler through shared handles | sharing | PLANNED | PB5.1, PB3.4 |
| [PB5.3](TASKS.md#pb53) — Close sharing time and space bounds | sharing | PLANNED | PB5.2, PB4.5 |
| [PB5.4](TASKS.md#pb54) — Formalize the two representation families | structural | PLANNED | PB5.3 |

## PB6 — Common anchors and structural algorithms

Section4 plus constructed-width4.7 and weighted-cover4.8; discovery and OPT scope remain explicit.

Work packages: 11; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [PB6.1](TASKS.md#pb61) — Sorted dead-region intersection and anchor recognition | structural | PLANNED | PB1.4, PB2.7 |
| [PB6.2](TASKS.md#pb62) — Single-occurrence linear theorem | structural | PLANNED | PB1.3, PB8.1 |
| [PB6.3](TASKS.md#pb63) — Independent trees and deletion localization | structural | PLANNED | PB1.3 |
| [PB6.4](TASKS.md#pb64) — Output-sensitive dominator updates and Sigma charge | structural | PLANNED | PB6.3, PB1.4, PB4.1 |
| [PB6.5](TASKS.md#pb65) — Explicit-update obstruction and Hamiltonian cases | structural | PLANNED | PB6.3, PB6.7 |
| [PB6.6](TASKS.md#pb66) — Later-failure crossing and target compression | structural | PLANNED | PB1.3 |
| [PB6.7](TASKS.md#pb67) — Streamed columns and original-edge range indexes | structural | PLANNED | PB6.6, PB1.4, PB4.1 |
| [PB6.8](TASKS.md#pb68) — Construct width-aware greedy reachability chains | structural | PLANNED | PB1.2, PB4.1, PB6.6 |
| [PB6.9](TASKS.md#pb69) — Compose constructed-width all-query bound | structural | PLANNED | PB6.8, PB6.7 |
| [PB6.10](TASKS.md#pb610) — Verify linear-time weighted cover selection | structural | PLANNED | PB6.3, PB1.5, PB4.1 |
| [PB6.11](TASKS.md#pb611) — Compose weighted region optimum bound | structural | PLANNED | PB6.10, PB6.4 |

## PB7 — Explicit reductions and conditional bounds

Source reductions, sizes and construction costs, followed by precisely conditional machine-model consequences.

Work packages: 6; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [PB7.1](TASKS.md#pb71) — Selectors, triangle and representation padding | reductions | PLANNED | PB8.2 |
| [PB7.2](TASKS.md#pb72) — Clique windows and fixed polynomial ratios | reductions | PLANNED | PB7.1 |
| [PB7.3](TASKS.md#pb73) — Copied-layer multiplicity tradeoff | reductions | PLANNED | PB7.1 |
| [PB7.4](TASKS.md#pb74) — Directed-cycle reduction and essentiality | reductions | PLANNED | PB7.1 |
| [PB7.5](TASKS.md#pb75) — Fix algorithm models and conditional transfers | complexity | PLANNED | PB7.1, PB7.2, PB7.3, PB7.4, PB4.1 |
| [PB7.6](TASKS.md#pb76) — Balanced algebraic clique implication | complexity | PLANNED | PB7.2, PB7.5 |

## PB8 — Remaining baselines, summaries and controller interface

Appendices A–D and Corollary 6.1 with each imported input and resource gap exposed.

Work packages: 8; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [PB8.1](TASKS.md#pb81) — Guarded-path and linear OSR equivalence | adapters | PLANNED | PB1.1, PB0.2 |
| [PB8.2](TASKS.md#pb82) — Baseline detector, dual-Horn and blocked bitsets | adapters | PLANNED | PB8.1, PB4.1 |
| [PB8.3](TASKS.md#pb83) — Algebraic one-sided algorithm | algebra | PLANNED | PB8.1 |
| [PB8.4](TASKS.md#pb84) — Canonical summaries, shortcuts and equality queries | structural | PLANNED | PB2.2, PB1.4 |
| [PB8.5](TASKS.md#pb85) — Uniform capacity, Kraft and optimal budgets | selectors | PLANNED | PB2.1 |
| [PB8.6](TASKS.md#pb86) — Shared Hitting Set reduction and construction cost | adapters | PLANNED | PB8.1, PB8.2, PB4.1 |
| [PB8.7](TASKS.md#pb87) — Conditional Hitting Set and joint exponents | adapters | PLANNED | PB8.6, PB7.5, PB7.2 |
| [PB8.8](TASKS.md#pb88) — Physical and native-encoding application | adapters | PLANNED | PB8.1, PB8.7, PB7.6, PB4.6, PB5.3, PB6.1, PB6.2, PB6.4, PB6.7, PB8.3, PB8.4, PB6.9, PB6.11 |

## PB9 — Fidelity, replay and release handoff

Per-statement paper/Lean comparison, clean reproducible checks and an exact user-controlled registration packet.

Work packages: 4; planning audits complete: 0; verified proof packages: 0.

| Task | Owner | Status | Prerequisites |
|---|---|---|---|
| [PB9.1](TASKS.md#pb91) — Audit all-query statement fidelity and trust | reviewer | PLANNED | PB4.6 |
| [PB9.2](TASKS.md#pb92) — Clean replay, Comparator and negative controls | reviewer | PLANNED | PB9.1 |
| [PB9.3](TASKS.md#pb93) — Extension fidelity and exact coverage status | reviewer | PLANNED | PB5.3, PB6.1, PB6.2, PB6.4, PB6.5, PB7.5, PB7.6, PB8.3, PB8.4, PB8.5, PB8.7, PB8.8, PB5.4, PB6.9, PB6.11 |
| [PB9.4](TASKS.md#pb94) — Prepare the selected release and manual registry packet | coordinator | PLANNED | PB9.2 |

