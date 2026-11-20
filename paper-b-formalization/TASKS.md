# Paper B task tracker

Each handoff has a proposed owner, prerequisites and acceptance evidence. Worker assignments and verified proof status are recorded separately.

<a id="ex01"></a>

## EX0.1 — Freeze paper identities and statement locations

- Milestone: EX0; status: **DONE_PLAN**; proof status: PLANNING_ONLY.
- Owner: contract; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: none.
- Proposed owner module: `release-core/Challenge.lean`.
- Paper consumers: 1.1, 4.1; risk: ordinary.

Bind the deposited ten-page source, Figure 1 and the separate proof location of Theorem 1.1.

Acceptance:

- Match the ten numbered items and nine proofs to the source in the deposit ZIP. Check the PDF and figure hashes against the publication packet.

Planning/evidence references: [sources/source-lock.json](sources/source-lock.json).

<a id="ex02"></a>

## EX0.2 — Pin the environment and elaborate candidate interfaces

- Milestone: EX0; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: contract; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX0.1.
- Proposed owner module: `release-core/Challenge.lean`.
- Paper consumers: 1.1, 4.1; risk: ordinary.

Typecheck candidate signatures for a finite labelled DAG, tail sets, immutable index and costed programs.

Acceptance:

- Record the toolchain, supported imports, exact elaborated types and a review of the quantifier order.
- Replay only needed existing declarations in the selected environment. Record exact matches, adapters, and new obligations, including input orientation, multiarcs, batch quantifiers and cost primitives.

The exact published and v1.3 oracle contracts allow one fixed layout-specific address allowance with checked logarithmic word-width bounds. Use the actual chosen layout slack from the complete implementation.

Planning/evidence references: [release-core/Challenge.lean](release-core/Challenge.lean), [release-core/PaperB/ExitPaths.lean](release-core/PaperB/ExitPaths.lean), [evidence/ex02-carbon-start/review.md](evidence/ex02-carbon-start/review.md), [evidence/ex02-carbon-start/verification.json](evidence/ex02-carbon-start/verification.json), [evidence/exit-transfer-nested/review.md](evidence/exit-transfer-nested/review.md), [evidence/ex02-oracle-contract/verification.json](evidence/ex02-oracle-contract/verification.json), [evidence/ex02-fixed-word-slack/verification.json](evidence/ex02-fixed-word-slack/verification.json).

<a id="ex03"></a>

## EX0.3 — Define execution and storage units

- Milestone: EX0; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: cost model; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX0.2.
- Proposed owner module: `release-core/PaperB/Machine.lean`.
- Paper consumers: 1.1, 3.2, 5.1; risk: ordinary.

Specify word size, addressable arrays, peak live words, retained index size and the available query input.

Acceptance:

- Define all four resource observables, including construction temporaries and input-sized addresses for parallel arcs.
- Use the existing word-machine definitions where the primitive bounds match. Check address fit, determinism, logarithmic word width, and the cost of comparisons, lowbit and allocation.

Lean verifies the executable fixed-width machine, trace determinism and exact peak. The same build and query runs measure construction operations, construction peak, retained words and later query operations on one sealed array. Fixed control and header costs are explicit. EX1–EX6 still need the paper’s programs, serialization, capacity and asymptotic bounds.

Planning/evidence references: [evidence/ex03-machine-foundation/verification.json](evidence/ex03-machine-foundation/verification.json), [evidence/ex03-word-operations/verification.json](evidence/ex03-word-operations/verification.json), [evidence/ex03-ram-program/verification.json](evidence/ex03-ram-program/verification.json), [evidence/ex03-ram-traces/verification.json](evidence/ex03-ram-traces/verification.json), [evidence/ex03-sealed-build/verification.json](evidence/ex03-sealed-build/verification.json), [evidence/ex03-sealed-query/verification.json](evidence/ex03-sealed-query/verification.json), [evidence/ex03-ram-lifecycle/verification.json](evidence/ex03-ram-lifecycle/verification.json).

<a id="ex11"></a>

## EX1.1 — Normalize original vertices and failure sets

- Milestone: EX1; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: graph; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX0.2.
- Proposed owner module: `release-core/PaperB/Graph.lean`.
- Paper consumers: 1.1, 2.1, 2.2; risk: ordinary.

Define reachability, source deletion, zero-length paths, repeated failures, unreachable vertices, and parallel input arcs.

Acceptance:

- Prove translation to the retained DAG preserves every original query, including failed targets and discarded identifiers.
- Relate arbitrary IDs and counted parallel input entries to the existing decreasing-index ReachAvoid specification. Charge constructing the ordering and reachability mask in the executable branch.

Actual Kahn-order inversion validates the decreasing-index graph adapter and charges one order read and rank write per vertex, preserving parallel occurrence counts. The normalized graph and its exact semantics are accepted. The later machine compilation and oracle-wide resource accounting remain separate.

Planning/evidence references: [evidence/ex11-retained-graph/verification.json](evidence/ex11-retained-graph/verification.json), [evidence/ex11-reach-scan/verification.json](evidence/ex11-reach-scan/verification.json), [evidence/ex11-reach-sound/verification.json](evidence/ex11-reach-sound/verification.json), [evidence/ex11-reach-scan-correct/verification.json](evidence/ex11-reach-scan-correct/verification.json), [evidence/ex11-indegree-prepass/verification.json](evidence/ex11-indegree-prepass/verification.json), [evidence/ex11-kahn-loop/verification.json](evidence/ex11-kahn-loop/verification.json), [evidence/ex11-kahn-row/verification.json](evidence/ex11-kahn-row/verification.json), [evidence/ex11-kahn-prefix/verification.json](evidence/ex11-kahn-prefix/verification.json), [evidence/ex11-kahn-residual-graph/verification.json](evidence/ex11-kahn-residual-graph/verification.json), [evidence/ex11-kahn-topological/verification.json](evidence/ex11-kahn-topological/verification.json), [evidence/ex11-kahn-exact-counts/verification.json](evidence/ex11-kahn-exact-counts/verification.json), [evidence/ex11-compact-id-maps/verification.json](evidence/ex11-compact-id-maps/verification.json), [evidence/ex11-compact-graph/verification.json](evidence/ex11-compact-graph/verification.json), [evidence/ex11-compact-paths/verification.json](evidence/ex11-compact-paths/verification.json), [evidence/ex11-compact-failures/verification.json](evidence/ex11-compact-failures/verification.json), [evidence/ex11-compact-counts/verification.json](evidence/ex11-compact-counts/verification.json), [evidence/ex11-query-normalization/verification.json](evidence/ex11-query-normalization/verification.json), [evidence/ex11-decreasing-paths/verification.json](evidence/ex11-decreasing-paths/verification.json), [evidence/ex11-accept-normalization/verification.json](evidence/ex11-accept-normalization/verification.json).

<a id="ex12"></a>

## EX1.2 — Characterize the ordinary dominator tree

- Milestone: EX1; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.1.
- Proposed owner module: `release-core/PaperB/Dom.lean`.
- Paper consumers: 1.1, 2.1, 2.2, 5.1; risk: ordinary.

Prove inclusive ancestor iff ordinary domination on the reachable DAG, with LCA, child subtrees and prefix/suffix facts.

Acceptance:

- Give a tree construction or existence proof on all retained DAGs and characterize single deletion. Justify the root, singleton, and reachable nonroot predecessor cases.
- This semantic result supplies the labelled quotient independently of machine code.

Verified the semantic tree for every DAG, with exact inclusive ancestry and a unique LCA on every nonempty collection of reachable vertices.

Planning/evidence references: [evidence/ex12-dominator-predecessors/verification.json](evidence/ex12-dominator-predecessors/verification.json), [evidence/ex12-dominator-chain/verification.json](evidence/ex12-dominator-chain/verification.json), [evidence/ex12-immediate-dominator/verification.json](evidence/ex12-immediate-dominator/verification.json), [evidence/ex12-dominator-tree/verification.json](evidence/ex12-dominator-tree/verification.json), [evidence/ex12-topological-rank/verification.json](evidence/ex12-topological-rank/verification.json), [evidence/ex12-semantic-tree-accept/verification.json](evidence/ex12-semantic-tree-accept/verification.json).

<a id="ex13"></a>

## EX1.3 — Project and lift labelled sibling paths

- Milestone: EX1; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.2.
- Proposed owner module: `release-core/PaperB/Quotient.lean`.
- Paper consumers: 1.1, 2.1; risk: ordinary.

Assign each retained arc to its head parent, store its original tail, and prove flatness, projection and lifting.

Acceptance:

- Any sequence of parallel labelled exits lifts. Sum all quotient sizes: at most 2n vertex copies and one quotient arc per arc.
- Prove unique outside-to-root entry and internal reachability, keep parallel tails distinguishable, and prove that every nonroot vertex of the quotient has the quotient root as immediate dominator.

Verified the exact sibling quotients for all original DAGs, with chosen labelled path lifting, flatness and the full occurrence and vertex budgets.

Planning/evidence references: [evidence/ex13-dominator-boundary/verification.json](evidence/ex13-dominator-boundary/verification.json), [evidence/ex13-block-lifting/verification.json](evidence/ex13-block-lifting/verification.json), [evidence/ex13-block-projection/verification.json](evidence/ex13-block-projection/verification.json), [evidence/ex13-dominator-segment/verification.json](evidence/ex13-dominator-segment/verification.json), [evidence/ex13-unique-child/verification.json](evidence/ex13-unique-child/verification.json), [evidence/ex13-sibling-blocks/verification.json](evidence/ex13-sibling-blocks/verification.json), [evidence/ex13-failed-suffix/verification.json](evidence/ex13-failed-suffix/verification.json), [evidence/ex13-sibling-system/verification.json](evidence/ex13-sibling-system/verification.json), [evidence/ex13-sibling-flatness/verification.json](evidence/ex13-sibling-flatness/verification.json), [evidence/ex13-arc-ownership/verification.json](evidence/ex13-arc-ownership/verification.json), [evidence/ex13-sibling-encoding/verification.json](evidence/ex13-sibling-encoding/verification.json), [evidence/ex13-occurrence-budget/verification.json](evidence/ex13-occurrence-budget/verification.json), [evidence/ex13-quotient-arrays/verification.json](evidence/ex13-quotient-arrays/verification.json), [evidence/ex13-original-emissions/verification.json](evidence/ex13-original-emissions/verification.json), [evidence/ex13-finite-sibling/verification.json](evidence/ex13-finite-sibling/verification.json), [evidence/ex13-finite-flatness/verification.json](evidence/ex13-finite-flatness/verification.json), [evidence/ex13-quotient-array-counts/verification.json](evidence/ex13-quotient-array-counts/verification.json), [evidence/ex13-unique-arc-budget/verification.json](evidence/ex13-unique-arc-budget/verification.json), [evidence/ex13-actual-arc-budget/verification.json](evidence/ex13-actual-arc-budget/verification.json), [evidence/ex13-vertex-budget/verification.json](evidence/ex13-vertex-budget/verification.json), [evidence/paper-21-siblings-certified/verification.json](evidence/paper-21-siblings-certified/verification.json).

<a id="ex14"></a>

## EX1.4 — Characterize partial-block reachability

- Milestone: EX1; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.3.
- Proposed owner module: `release-core/PaperB/Quotient.lean`.
- Paper consumers: 1.1, 2.2; risk: ordinary.

Separate outside, own-block and third-block targets and translate the last usable exit into a subtree test.

Acceptance:

- Prove nonemptiness of both exit sets and the inclusive ancestry tests for the LCA of physical tails.
- Cover a failure equal to a block root, the LCA target, a target outside its subtree and a direct last exit to a third block.

Verified the complete original-DAG last-exit classification for all incomparable failures, including outside, common ancestor, both own blocks and the third-block exact LCA tests.

Planning/evidence references: [evidence/ex14-last-exit-outside-own/verification.json](evidence/ex14-last-exit-outside-own/verification.json), [evidence/ex14-both-exits/verification.json](evidence/ex14-both-exits/verification.json), [evidence/ex14-forward-last-exit/verification.json](evidence/ex14-forward-last-exit/verification.json), [evidence/ex14-third-block-lift/verification.json](evidence/ex14-third-block-lift/verification.json), [evidence/ex14-third-block-equivalence/verification.json](evidence/ex14-third-block-equivalence/verification.json), [evidence/ex14-third-block-lca/verification.json](evidence/ex14-third-block-lca/verification.json), [evidence/ex14-failures-below-lca/verification.json](evidence/ex14-failures-below-lca/verification.json), [evidence/paper-22-last-exit-certified/verification.json](evidence/paper-22-last-exit-certified/verification.json).

<a id="ex15"></a>

## EX1.5 — Construct the ordinary dominator tree within the oracle budget

- Milestone: EX1; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, cost model; assigned worker: unassigned.
- Dependencies: EX1.2, EX0.3, EX2.3.
- Proposed owner module: `release-core/PaperB/DomBuild.lean`.
- Paper consumers: 1.1; risk: resource bound.

Implement a checked constructor for the semantic tree on explicit DAG input. The proposed DAG route uses growing-tree LCAs of predecessors.

Acceptance:

- Prove that the immediate dominator of a reachable nonroot equals the LCA of its predecessors in the partial tree and that leaf insertion preserves all earlier ancestor relations, or provide a costed Lengauer–Tarjan implementation.
- For the DAG route, bound depth search, leaf insertion and all predecessor folds within O((n+m)L³) operations and O(n+m) peak words. State separately if the faster subroutine bound in Section 2 is established.

Verified the ordinary dominator build on the actual original DAG. Exact parent semantics, individual quadratic-log LCA charges, total input occurrences and exact fourteen-word leaf charges establish the component budget.

Planning/evidence references: [evidence/ex15-predecessor-lca/verification.json](evidence/ex15-predecessor-lca/verification.json), [evidence/ex15-common-depth-search/verification.json](evidence/ex15-common-depth-search/verification.json), [evidence/ex15-growing-lca/verification.json](evidence/ex15-growing-lca/verification.json), [evidence/ex15-predecessor-fold/verification.json](evidence/ex15-predecessor-fold/verification.json), [evidence/ex15-dominator-step/verification.json](evidence/ex15-dominator-step/verification.json), [evidence/ex15-concrete-jump-backend/verification.json](evidence/ex15-concrete-jump-backend/verification.json), [evidence/ex15-full-dom-sweep/verification.json](evidence/ex15-full-dom-sweep/verification.json), [evidence/ex15-actual-root-word-region/verification.json](evidence/ex15-actual-root-word-region/verification.json), [evidence/dom-from-original-audit/verification.json](evidence/dom-from-original-audit/verification.json).

<a id="ex16"></a>

## EX1.6 — Implement static tree intervals, child lookup and LCA

- Milestone: EX1; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, cost model; assigned worker: unassigned.
- Dependencies: EX1.2, EX0.3.
- Proposed owner module: `release-core/PaperB/TreeIndex.lean`.
- Paper consumers: 1.1, 5.1; risk: resource bound.

Construct inclusive subtree intervals, ordered child ranges and a heavy-path index on the actual ordinary tree.

Acceptance:

- Prove interval ancestry and child lookup in O(1) and O(L) operations respectively, including both range endpoints.
- Use maximum subtree-size heavy children to bound light-edge crossings; prove O(L) per original-tree LCA, O(n) shared words, and construction within the oracle budget.

Verified the complete actual ordinary-tree index component. One run of the original DAG dominator build supplies the stored subtree columns, sorted child intervals and heavy-head table. Original dominance, exact child and LCA reads, linear static build/space and logarithmic query costs are checked.

Planning/evidence references: [evidence/ex16-heavy-child/verification.json](evidence/ex16-heavy-child/verification.json), [evidence/ex16-heavy-path-lca/verification.json](evidence/ex16-heavy-path-lca/verification.json), [evidence/ex16-static-head-words/verification.json](evidence/ex16-static-head-words/verification.json), [evidence/ex16-child-interval-search/verification.json](evidence/ex16-child-interval-search/verification.json), [evidence/ex16-packed-static-layout/verification.json](evidence/ex16-packed-static-layout/verification.json), [evidence/actual-child-audit/verification.json](evidence/actual-child-audit/verification.json), [evidence/static-linear-audit/verification.json](evidence/static-linear-audit/verification.json), [evidence/static-from-dom-audit/verification.json](evidence/static-from-dom-audit/verification.json), [evidence/static-tree-reader-audit/verification.json](evidence/static-tree-reader-audit/verification.json), [evidence/static-oracle-tree-audit/verification.json](evidence/static-oracle-tree-audit/verification.json).

<a id="ex21"></a>

## EX2.1 — Identify the first proper loss

- Milestone: EX2; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.1.
- Proposed owner module: `release-core/PaperB/Forest.lean`.
- Paper consumers: 1.1, 3.1; risk: ordinary.

Show the first strict loss follows both endpoints and has exactly those distinct predecessors.

Acceptance:

- Handle parallel arcs, direct root edges and the absence of any proper loss.

The first proper loss follows both endpoints and its distinct predecessor set equals the failed pair.

Planning/evidence references: [evidence/carbon-last-arc/review.md](evidence/carbon-last-arc/review.md), [evidence/carbon-first-proper-loss/review.md](evidence/carbon-first-proper-loss/review.md), [evidence/ex21-earliest-loss-audit/verification.json](evidence/ex21-earliest-loss-audit/verification.json).

<a id="ex22"></a>

## EX2.2 — Prove the topological forest invariant

- Milestone: EX2; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX2.1.
- Proposed owner module: `release-core/PaperB/Forest.lean`.
- Paper consumers: 1.1, 3.1, 4.1; risk: ordinary.

Show raw predecessor losses form a prefix, and that each vertex label represents all its proper separating pairs.

Acceptance:

- Prove existing ordered pair keys keep the same parent, endpoint inclusion, nested proper-loss sets and the linear node count.
- Maintain the induction for every processed label and every real edge, including raw losses at endpoints. Cover the latest predecessor and why an existing pair key retains its parent.

The actual sweep constructs the exact proper-loss forest on every finite flat quotient.

Planning/evidence references: [evidence/carbon-forest-sweep/progress.json](evidence/carbon-forest-sweep/progress.json), [evidence/carbon-sweep-latest-member/verification.json](evidence/carbon-sweep-latest-member/verification.json), [evidence/carbon-forest-prefix/verification.json](evidence/carbon-forest-prefix/verification.json), [evidence/ex22-unattended/f0686845-5aaf-419e-ac39-903e187dc284-prefix.json](evidence/ex22-unattended/f0686845-5aaf-419e-ac39-903e187dc284-prefix.json), [evidence/ex22-unattended/f0686845-5aaf-419e-ac39-903e187dc284-pair-key-reuse.json](evidence/ex22-unattended/f0686845-5aaf-419e-ac39-903e187dc284-pair-key-reuse.json), [evidence/ex22-unattended/native-swarm-sweep-step.json](evidence/ex22-unattended/native-swarm-sweep-step.json), [evidence/ex22-unattended/native-swarm-global-sweep.json](evidence/ex22-unattended/native-swarm-global-sweep.json), [evidence/ex22-unattended/native-swarm-forest-parents.json](evidence/ex22-unattended/native-swarm-forest-parents.json), [evidence/ex22-unattended/native-swarm-lemma-3-1.json](evidence/ex22-unattended/native-swarm-lemma-3-1.json), [evidence/ex22-forest-invariant-audit/verification.json](evidence/ex22-forest-invariant-audit/verification.json).

<a id="ex23"></a>

## EX2.3 — Implement depth jumps under leaf insertion

- Milestone: EX2; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: data structures; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX0.3.
- Proposed owner module: `release-core/PaperB/Jumps.lean`.
- Paper consumers: 1.1, 3.2, 5.1; risk: ordinary.

Use the v1.3 skew-binary parent, depth and jump records to reach a prescribed ancestor depth.

Acceptance:

- Prove constant-time insertion, O(L) moves per level search and O(L) online ancestry with one jump per node. See the [v1.3 acceptance addendum](../evidence/paper-b-log-shave-20261118/formalization-v1.3.md).

Verified for the actual preallocated jump region. Leaf insertion uses exactly 14 word accesses, depth lookup and online ancestry have logarithmic read bounds, and the concrete region has one size header and three fields per node.

Planning/evidence references: [evidence/ex22-unattended/native-swarm-jump-foundation.json](evidence/ex22-unattended/native-swarm-jump-foundation.json), [evidence/ex22-unattended/native-swarm-jump-invariant.json](evidence/ex22-unattended/native-swarm-jump-invariant.json), [evidence/ex22-unattended/native-swarm-jump-traversal.json](evidence/ex22-unattended/native-swarm-jump-traversal.json), [evidence/ex22-unattended/native-swarm-jump-move-bound.json](evidence/ex22-unattended/native-swarm-jump-move-bound.json), [evidence/ex22-unattended/native-swarm-word-memory.json](evidence/ex22-unattended/native-swarm-word-memory.json), [evidence/ex23-jump-kernel-audit/verification.json](evidence/ex23-jump-kernel-audit/verification.json).

<a id="ex24"></a>

## EX2.4 — Charge forest construction and membership

- Milestone: EX2; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX2.2, EX2.3.
- Proposed owner module: `release-core/PaperB/ForestBuild.lean`.
- Paper consumers: 1.1, 3.2; risk: resource bound.

Implement raw-predecessor tests, depth search, candidate key lookup and final ancestry intervals.

Acceptance:

- For v1.3, prove per-quotient O((n_H+m_H)L²) build, O(n_H+m_H) peak, O(n_H) retained, O(L) key lookup and O(1) known-node test.
- Deduplicate only for predecessor tests. Charge O(L) prefix probes, O(L) per level search and every repeated predecessor scan. Include deterministic dictionary construction, query and final intervals. See the [v1.3 acceptance addendum](../evidence/paper-b-log-shave-20261118/formalization-v1.3.md).

The actual packed read costs per probe are now bounded using grounded labels and tested predecessors. Compose across the depth search and meter the remaining work and peak space.

Planning/evidence references: [evidence/ex22-unattended/native-swarm-charging.json](evidence/ex22-unattended/native-swarm-charging.json), [evidence/public-lean-flatmap-split/verification.json](evidence/public-lean-flatmap-split/verification.json), [evidence/public-lean-interval-assembly/verification.json](evidence/public-lean-interval-assembly/verification.json), [evidence/public-lean-prefix-probe/verification.json](evidence/public-lean-prefix-probe/verification.json), [evidence/ex24-ancestry-interval/verification.json](evidence/ex24-ancestry-interval/verification.json), [evidence/ex24-prefix-cutoff/verification.json](evidence/ex24-prefix-cutoff/verification.json), [evidence/ex24-array-interval/verification.json](evidence/ex24-array-interval/verification.json), [evidence/ex24-predecessor-search/verification.json](evidence/ex24-predecessor-search/verification.json), [evidence/ex24-pair-lookup/verification.json](evidence/ex24-pair-lookup/verification.json), [evidence/ex24-dfs-array-builder/verification.json](evidence/ex24-dfs-array-builder/verification.json), [evidence/ex24-dfs-stack-potential/verification.json](evidence/ex24-dfs-stack-potential/verification.json), [evidence/ex24-dfs-exact-count/verification.json](evidence/ex24-dfs-exact-count/verification.json), [evidence/ex24-actual-trace-refinement/verification.json](evidence/ex24-actual-trace-refinement/verification.json), [evidence/ex24-merge-keys/verification.json](evidence/ex24-merge-keys/verification.json), [evidence/ex24-dfs-array-values/verification.json](evidence/ex24-dfs-array-values/verification.json), [evidence/ex24-predecessor-stamps/verification.json](evidence/ex24-predecessor-stamps/verification.json), [evidence/ex24-balanced-dictionary/verification.json](evidence/ex24-balanced-dictionary/verification.json), [evidence/ex24-actual-known-node-query/verification.json](evidence/ex24-actual-known-node-query/verification.json), [evidence/ex24-verified-head-step/verification.json](evidence/ex24-verified-head-step/verification.json), [evidence/ex24-dynamic-key-install/verification.json](evidence/ex24-dynamic-key-install/verification.json), [evidence/ex24-small-quotient/verification.json](evidence/ex24-small-quotient/verification.json), [evidence/ex24-ready-embedding/verification.json](evidence/ex24-ready-embedding/verification.json), [evidence/forest-embedding-step-audit/verification.json](evidence/forest-embedding-step-audit/verification.json), [evidence/forest-canonical-audit/verification.json](evidence/forest-canonical-audit/verification.json), [evidence/forest-word-audit/verification.json](evidence/forest-word-audit/verification.json), [evidence/forest-rank-members-audit/verification.json](evidence/forest-rank-members-audit/verification.json), [evidence/forest-packed-rows-audit/verification.json](evidence/forest-packed-rows-audit/verification.json), [evidence/prepared-head-audit/verification.json](evidence/prepared-head-audit/verification.json), [evidence/forest-endpoints-audit/verification.json](evidence/forest-endpoints-audit/verification.json), [evidence/forest-compact-audit/verification.json](evidence/forest-compact-audit/verification.json), [evidence/forest-exact-dict-audit/verification.json](evidence/forest-exact-dict-audit/verification.json), [evidence/forest-actual-step-audit/verification.json](evidence/forest-actual-step-audit/verification.json), [evidence/measured-cut-audit/verification.json](evidence/measured-cut-audit/verification.json), [evidence/compact-loop-public-audit/verification.json](evidence/compact-loop-public-audit/verification.json), [evidence/prepared-parent-audit/verification.json](evidence/prepared-parent-audit/verification.json), [evidence/forest-topological-audit/verification.json](evidence/forest-topological-audit/verification.json), [evidence/forest-actual-full-audit/verification.json](evidence/forest-actual-full-audit/verification.json), [evidence/forest-reflection-audit/verification.json](evidence/forest-reflection-audit/verification.json), [evidence/forest-measured-work-audit/verification.json](evidence/forest-measured-work-audit/verification.json), [evidence/forest-physical-intervals-audit/verification.json](evidence/forest-physical-intervals-audit/verification.json), [evidence/forest-site-depth-audit/verification.json](evidence/forest-site-depth-audit/verification.json), [evidence/forest-real-prefix-audit/verification.json](evidence/forest-real-prefix-audit/verification.json), [evidence/forest-ordered-reader-audit/verification.json](evidence/forest-ordered-reader-audit/verification.json), [evidence/forest-real-counts-audit/verification.json](evidence/forest-real-counts-audit/verification.json), [evidence/forest-slim-index-audit/verification.json](evidence/forest-slim-index-audit/verification.json), [evidence/forest-packed-probe-audit/verification.json](evidence/forest-packed-probe-audit/verification.json).

<a id="ex31"></a>

## EX3.1 — Lift each fresh endpoint contribution

- Milestone: EX3; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX2.2, EX1.3.
- Proposed owner module: `release-core/PaperB/Exit.lean`.
- Paper consumers: 4.1; risk: ordinary.

Give the forward witness using topological order for each fresh child endpoint, for arbitrary parallel exit tails.

Acceptance:

- Prove inclusion for every output coordinate and target in the child proper-loss set.

The universal fresh contribution preserves each original physical tail on every real parent-child edge.

Planning/evidence references: [evidence/ex33-forest-exit/verification.json](evidence/ex33-forest-exit/verification.json), [evidence/ex31-fresh-certified/verification.json](evidence/ex31-fresh-certified/verification.json).

<a id="ex32"></a>

## EX3.2 — Handle inherited tails and the reverse inclusion

- Milestone: EX3; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX3.1.
- Proposed owner module: `release-core/PaperB/Exit.lean`.
- Paper consumers: 4.1; risk: path semantics.

Prove the bypass argument for a shared endpoint and the converse for each child visitation pattern.

Acceptance:

- Discharge disjoint pairs, inherited-only exits and exits through a fresh endpoint with exact tail identity.

The inherited contribution and converse preserve exact physical tails with the required endpoint guard.

Planning/evidence references: [evidence/ex33-forest-exit/verification.json](evidence/ex33-forest-exit/verification.json), [evidence/ex32-inherited-certified/verification.json](evidence/ex32-inherited-certified/verification.json).

<a id="ex33"></a>

## EX3.3 — Certify the set-level transfer theorem

- Milestone: EX3; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX3.2.
- Proposed owner module: `release-core/PaperB/Exit.lean`.
- Paper consumers: 4.1; risk: ordinary.

Assemble both inclusions as an equality of finite sets of physical tails before compression.

Acceptance:

- An independent statement audit verifies quantification over every real forest edge, both coordinates and every proper-loss target.
- Instantiate the structural identity on the actual constructed forest and the original-tail labels. Figure 1 checks both exact contributions and all three failure outcomes as a regression control.

The full exact exit-transfer set equality is certified for the published declaration on actual original-DAG quotients.

Planning/evidence references: [evidence/ex33-forest-exit/verification.json](evidence/ex33-forest-exit/verification.json), [evidence/ex33-figure-1/verification.json](evidence/ex33-figure-1/verification.json), [evidence/ex13-finite-flatness/verification.json](evidence/ex13-finite-flatness/verification.json), [evidence/paper-41-transfer-certified/verification.json](evidence/paper-41-transfer-certified/verification.json).

<a id="ex41"></a>

## EX4.1 — Implement the two-coordinate map algebra

- Milestone: EX4; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: oracle; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX3.3, EX1.2.
- Proposed owner module: `release-core/PaperB/Index.lean`.
- Paper consumers: 1.1, 5.1; risk: ordinary.

Formalize the LCA join with an empty sentinel and constant-plus-optional-coordinate maps.

Acceptance:

- Prove identity, evaluation and composition, including missing slots and endpoint reordering with bounded storage.

Verified exact composition and endpoint orientation for empty-aware exit maps, including their bounded fixed-width word encoding.

Planning/evidence references: [evidence/ex41-exit-map-algebra/verification.json](evidence/ex41-exit-map-algebra/verification.json), [evidence/ex41-exit-extrema/verification.json](evidence/ex41-exit-extrema/verification.json), [evidence/ex41-exact-lca-summary/verification.json](evidence/ex41-exact-lca-summary/verification.json), [evidence/ex41-exit-word-encoding/verification.json](evidence/ex41-exit-word-encoding/verification.json).

<a id="ex42"></a>

## EX4.2 — Install maps before bases in topological order

- Milestone: EX4; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: oracle; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX4.1, EX2.4.
- Proposed owner module: `release-core/PaperB/Index.lean`.
- Paper consumers: 1.1, 5.1; risk: dependency order.

Show every map and predecessor base read at installation already exists.

Acceptance:

- Prove the induction for initial seeds, repeated seeds, artificial-root maps and all labelled incoming arcs.
- The path above the already processed fresh endpoint has maps installed. For an earlier off-endpoint predecessor, propagate its base; for an endpoint arc add its own physical tail.

The real forest log now proves exact first-install vertices and occupancy for every non-top-level transfer record. The raw occurrence fold is also checked against its typed read contracts. The combined indexed schedule and actual mapped callbacks remain open.

Planning/evidence references: [evidence/ex42-seed-chronology/verification.json](evidence/ex42-seed-chronology/verification.json), [evidence/ex42-actual-seeds/verification.json](evidence/ex42-actual-seeds/verification.json), [evidence/ex42-incoming-tails/verification.json](evidence/ex42-incoming-tails/verification.json), [evidence/ex42-topological-array-sweep/verification.json](evidence/ex42-topological-array-sweep/verification.json), [evidence/ex42-exact-exit-kernels/verification.json](evidence/ex42-exact-exit-kernels/verification.json), [evidence/physical-exit-audit/verification.json](evidence/physical-exit-audit/verification.json), [evidence/exit-indexed-audit/verification.json](evidence/exit-indexed-audit/verification.json), [evidence/physical-entry-audit/verification.json](evidence/physical-entry-audit/verification.json), [evidence/forest-event-chronology-audit/verification.json](evidence/forest-event-chronology-audit/verification.json), [evidence/exit-grouped-fresh-audit/verification.json](evidence/exit-grouped-fresh-audit/verification.json), [evidence/exit-real-log-audit/verification.json](evidence/exit-real-log-audit/verification.json), [evidence/exit-earliest-label-audit/verification.json](evidence/exit-earliest-label-audit/verification.json), [evidence/exit-raw-incoming-audit/verification.json](evidence/exit-raw-incoming-audit/verification.json), [evidence/exit-real-first-label-audit/verification.json](evidence/exit-real-first-label-audit/verification.json).

<a id="ex43"></a>

## EX4.3 — Build and evaluate composed jump maps

- Milestone: EX4; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: oracle; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX4.2, EX2.3, EX1.6.
- Proposed owner module: `release-core/PaperB/Index.lean`.
- Paper consumers: 1.1, 5.1; risk: ordinary.

Construct one upward jump map per real pair and recover both summary coordinates from the vertex base.

Acceptance:

- Match the set semantics for any target and allowed ancestor in O(L²) moves and O(L³) word operations.
- Prove all of Lemma 5.1 locally: per-quotient build O((n_H+m_H)L³), O(n_H+m_H) temporary words and O(n_H) retained records. Charge each arc and each installation.

The actual exit-map traversal fuses jump selection and composition in a fixed-register tail loop, agrees with the ghost trace and uses one packed record probe and composition per step. Exact record installation remains in progress.

Planning/evidence references: [evidence/ex43-checked-map-fold/verification.json](evidence/ex43-checked-map-fold/verification.json), [evidence/ex43-actual-skew-route/verification.json](evidence/ex43-actual-skew-route/verification.json), [evidence/fused-jump-audit/verification.json](evidence/fused-jump-audit/verification.json).

<a id="ex44"></a>

## EX4.4 — Decide arbitrary post-build queries

- Milestone: EX4; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: oracle; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.4, EX4.3, EX1.5.
- Proposed owner module: `release-core/PaperB/Oracle.lean`.
- Paper consumers: 1.1; risk: ordinary.

Implement the full case split once on the retained index; include missing pair keys and comparable failures.

Acceptance:

- Prove output iff reachability after deletion for any subset of size at most two and any original target.
- Sort the two quotient endpoints and carry their corresponding original failures with them. Cover missing keys, pairs off the target label's ancestor chain, and zero-length paths.

The actual paired ID maps and static parent column now give the original graph's exact ParentSpec and parent queries, enabling concrete LCA and child-block adapters.

Planning/evidence references: [evidence/ex44-early-query-cases/verification.json](evidence/ex44-early-query-cases/verification.json), [evidence/ex44-retained-query-runtime/verification.json](evidence/ex44-retained-query-runtime/verification.json), [evidence/ex44-query-leaf-proofs/verification.json](evidence/ex44-query-leaf-proofs/verification.json), [evidence/retained-early-audit/verification.json](evidence/retained-early-audit/verification.json), [evidence/both-reachable-audit/verification.json](evidence/both-reachable-audit/verification.json), [evidence/third-leaf-audit/verification.json](evidence/third-leaf-audit/verification.json), [evidence/all-original-audit/verification.json](evidence/all-original-audit/verification.json), [evidence/exit-span-audit/verification.json](evidence/exit-span-audit/verification.json), [evidence/held-id-audit/verification.json](evidence/held-id-audit/verification.json), [evidence/static-tree-held-audit/verification.json](evidence/static-tree-held-audit/verification.json), [evidence/original-static-connector-audit/verification.json](evidence/original-static-connector-audit/verification.json), [evidence/original-parent-audit/verification.json](evidence/original-parent-audit/verification.json).

<a id="ex51"></a>

## EX5.1 — Account for discovery and every edge scan

- Milestone: EX5; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: cost model; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX0.3, EX2.4, EX4.3, EX1.5, EX1.6.
- Proposed owner module: `release-core/PaperB/Resources.lean`.
- Paper consumers: 1.1; risk: resource bound.

Sum all phases, including sorting, dominator construction, repeated predecessor scans and LCA operations.

Acceptance:

- Prove deterministic O((n+m)L³) build time for the compiled data layout.

Concrete dense local positions and original structural sibling keys now have checked inverses. Transport labelled adjacency and topological order next.

Planning/evidence references: [evidence/ex51-ram-trace-composition/verification.json](evidence/ex51-ram-trace-composition/verification.json), [evidence/ex51-linear-occurrence-buckets/verification.json](evidence/ex51-linear-occurrence-buckets/verification.json), [evidence/ex51-one-word-midpoint/verification.json](evidence/ex51-one-word-midpoint/verification.json), [evidence/global-sibling-audit/verification.json](evidence/global-sibling-audit/verification.json), [evidence/ram-midpoint-audit/verification.json](evidence/ram-midpoint-audit/verification.json), [evidence/dense-quotient-audit/verification.json](evidence/dense-quotient-audit/verification.json), [evidence/actual-sibling-emitter-audit/verification.json](evidence/actual-sibling-emitter-audit/verification.json), [evidence/dense-arc-local-slot-audit/verification.json](evidence/dense-arc-local-slot-audit/verification.json), [evidence/dense-arc-row-audit/verification.json](evidence/dense-arc-row-audit/verification.json), [evidence/dense-real-ownership-audit/verification.json](evidence/dense-real-ownership-audit/verification.json), [evidence/dense-runtime-graph-audit/verification.json](evidence/dense-runtime-graph-audit/verification.json), [evidence/dense-key-iso-audit/verification.json](evidence/dense-key-iso-audit/verification.json).

<a id="ex52"></a>

## EX5.2 — Bound peak workspace and the retained index

- Milestone: EX5; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: cost model; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX5.1.
- Proposed owner module: `release-core/PaperB/Resources.lean`.
- Paper consumers: 1.1; risk: resource bound.

Give allocation lifetimes and index serialization for the same construction.

Acceptance:

- Prove O(n+m) construction words and O(n) retained words including original IDs, and discard input adjacency.
- Prove a peak over all intermediate states, and a separate bound on storage reachable from the query index after disposal, including ID translation and copy or serialization costs.

The arena and sealed prefix are reserved solely from declared input counts with the exact oracle contract bit width. Dense offsets, headers, retained words and legal query address ranges are bounded uniformly. Choose constant final block widths and instantiate the same built/queried machine programs in this layout.

Planning/evidence references: [evidence/ex52-exact-memory-layout/verification.json](evidence/ex52-exact-memory-layout/verification.json), [evidence/ex52-uniform-sealed-arena/verification.json](evidence/ex52-uniform-sealed-arena/verification.json).

<a id="ex53"></a>

## EX5.3 — Bound each later query and exclude adjacency access

- Milestone: EX5; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: cost model; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX4.4, EX5.2.
- Proposed owner module: `release-core/PaperB/Resources.lean`.
- Paper consumers: 1.1; risk: ordinary.

Run the fixed query program on only the stored index, failure set and one target.

Acceptance:

- Give an O(L³) bound independent of graph density, target choice, batch size and previous queries.

The complete register-remapped worker trace preserves every executed step, its halt and the external register frame. Linked code and actual sealed index reads remain open.

Planning/evidence references: [evidence/ram-static-lca-audit/verification.json](evidence/ram-static-lca-audit/verification.json), [evidence/ram-fixed-relocation-audit/verification.json](evidence/ram-fixed-relocation-audit/verification.json), [evidence/ram-predecessor-worker-audit/verification.json](evidence/ram-predecessor-worker-audit/verification.json), [evidence/ram-search-correct-audit/verification.json](evidence/ram-search-correct-audit/verification.json), [evidence/ram-register-frame-audit/verification.json](evidence/ram-register-frame-audit/verification.json), [evidence/ram-register-trace-audit/verification.json](evidence/ram-register-trace-audit/verification.json).

<a id="ex54"></a>

## EX5.4 — Join correctness and costs in the oracle theorem

- Milestone: EX5; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: integration; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX5.3.
- Proposed owner module: `release-core/Solution.lean`.
- Paper consumers: 1.1; risk: public theorem.

Bind one uniform build/query pair to correctness, preprocessing time, peak space, retained words and query time.

Acceptance:

- Require exact paper-to-type correspondence, a pinned build, dependency and axiom audits, and independent replay of the closed root.
- Discharge all imported constructor, tree and RAM assumptions. A proved functional query or a theorem conditional on a supplied index is recorded at its own scope.

<a id="ex55"></a>

## EX5.5 — Derive the listed-target Boolean vector

- Milestone: EX5; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: application; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX5.4.
- Proposed owner module: `extensions/Batch.lean`.
- Paper consumers: 1.2; risk: ordinary.

Aggregate online memberships as disjunctions while charging list accesses and explicit output writes.

Acceptance:

- Handle q empty lists, repetitions, arbitrary overlap, O(SL³) total time and O(S) workspace with S=n+m+q+M.
- Produce one Boolean per original list in order, prove the later-single-list bound, and allow logarithmic words in S+2.

The listed-target transfer verifies the v1.3 mixed quadratic-log build plus linear-log per-target time, ordered output, and explicit-space bounds under the exact oracle contract. The whole-oracle instantiation remains open.

Planning/evidence references: [evidence/ex55-listed-batch-support/verification.json](evidence/ex55-listed-batch-support/verification.json), [evidence/ex55-v13-batch-bound/verification.json](evidence/ex55-v13-batch-bound/verification.json).

<a id="ex61"></a>

## EX6.1 — Prove the guarded-path and shrinking-witness equivalence

- Milestone: EX6; status: **VERIFIED**; proof status: CERTIFIED.
- Owner: application; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.1.
- Proposed owner module: `extensions/Guarded.lean`.
- Paper consumers: 6.1; risk: ordinary.

Relate truth of a supplied healthy-zero root to a surviving labelled terminal and shrink the witness to Q union a candidate singleton.

Acceptance:

- Cover constant-zero terminals, repeated labels, forced guard deletions and both choices of Q.

A true guarded output is equivalent to a surviving path to a true labelled terminal. Healthy-zero admissible witnesses shrink to the forced set plus one non-reference label. The residual query equivalence handles deleted guards and root. Construct and charge all failure and terminal lists for the residual multiplicity-two batch under EX6.2.

Planning/evidence references: [evidence/ex61-guarded-witness/verification.json](evidence/ex61-guarded-witness/verification.json).

<a id="ex62"></a>

## EX6.2 — Account for all label and terminal incidences

- Milestone: EX6; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: application; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX6.1, EX5.5.
- Proposed owner module: `extensions/Guarded.lean`.
- Paper consumers: 6.1; risk: ordinary.

Encode each candidate with at most two residual guard failures and its full terminal list.

Acceptance:

- Return an admissible detecting set for each positive case and prove O(G_dec log³(G_dec+2)) time and O(G_dec) words.
- Map each positive output index back to i, including multiple terminals of one label, and return Q union {i}. The number of failed vertices per candidate counts distinct guards after the shared deletion.

Under the exact single-target oracle contract, Lean checks the whole guarded application from shared deletion and grouped rows to the first actual detecting witness and complete negative answer. Full sealed oracle instantiation remains open.

Planning/evidence references: [evidence/guarded-incidences-audit/verification.json](evidence/guarded-incidences-audit/verification.json), [evidence/guarded-residual-graph-audit/verification.json](evidence/guarded-residual-graph-audit/verification.json), [evidence/guarded-listed-witness-audit/verification.json](evidence/guarded-listed-witness-audit/verification.json).

