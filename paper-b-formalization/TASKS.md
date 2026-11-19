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

The pinned toolchain elaborates both candidate interfaces. The exit-set type retains exact original-tail membership. The static oracle contract fixes one build and one query, quantifies all queries after the build, and uses all four resource bounds. Lean checks the v1.3-to-v1.2 bound relaxation. The executable observer and theorem proof remain under EX0.3 and EX5.

Planning/evidence references: [release-core/Challenge.lean](release-core/Challenge.lean), [release-core/PaperB/ExitPaths.lean](release-core/PaperB/ExitPaths.lean), [evidence/ex02-carbon-start/review.md](evidence/ex02-carbon-start/review.md), [evidence/ex02-carbon-start/verification.json](evidence/ex02-carbon-start/verification.json), [evidence/exit-transfer-nested/review.md](evidence/exit-transfer-nested/review.md), [evidence/ex02-oracle-contract/verification.json](evidence/ex02-oracle-contract/verification.json).

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

- Milestone: EX1; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: graph; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX0.2.
- Proposed owner module: `release-core/PaperB/Graph.lean`.
- Paper consumers: 1.1, 2.1, 2.2; risk: ordinary.

Define reachability, source deletion, zero-length paths, repeated failures, unreachable vertices, and parallel input arcs.

Acceptance:

- Prove translation to the retained DAG preserves every original query, including failed targets and discarded identifiers.
- Relate arbitrary IDs and counted parallel input entries to the existing decreasing-index ReachAvoid specification. Charge constructing the ordering and reachability mask in the executable branch.

Executable normalization builds the compact reachable DAG by Kahn traversal, reachability scan, compact mapping and adjacency sweep. Every original root query with up to two failed IDs is equivalent after translation; initially unreachable targets and failed source or target are rejected, preserving original zero-length cases. Exact phase counters are bounded by original sizes. Complete the decreasing-index adapter and rank map, then close EX1.1.

Planning/evidence references: [evidence/ex11-retained-graph/verification.json](evidence/ex11-retained-graph/verification.json), [evidence/ex11-reach-scan/verification.json](evidence/ex11-reach-scan/verification.json), [evidence/ex11-reach-sound/verification.json](evidence/ex11-reach-sound/verification.json), [evidence/ex11-reach-scan-correct/verification.json](evidence/ex11-reach-scan-correct/verification.json), [evidence/ex11-indegree-prepass/verification.json](evidence/ex11-indegree-prepass/verification.json), [evidence/ex11-kahn-loop/verification.json](evidence/ex11-kahn-loop/verification.json), [evidence/ex11-kahn-row/verification.json](evidence/ex11-kahn-row/verification.json), [evidence/ex11-kahn-prefix/verification.json](evidence/ex11-kahn-prefix/verification.json), [evidence/ex11-kahn-residual-graph/verification.json](evidence/ex11-kahn-residual-graph/verification.json), [evidence/ex11-kahn-topological/verification.json](evidence/ex11-kahn-topological/verification.json), [evidence/ex11-kahn-exact-counts/verification.json](evidence/ex11-kahn-exact-counts/verification.json), [evidence/ex11-compact-id-maps/verification.json](evidence/ex11-compact-id-maps/verification.json), [evidence/ex11-compact-graph/verification.json](evidence/ex11-compact-graph/verification.json), [evidence/ex11-compact-paths/verification.json](evidence/ex11-compact-paths/verification.json), [evidence/ex11-compact-failures/verification.json](evidence/ex11-compact-failures/verification.json), [evidence/ex11-compact-counts/verification.json](evidence/ex11-compact-counts/verification.json), [evidence/ex11-query-normalization/verification.json](evidence/ex11-query-normalization/verification.json).

<a id="ex12"></a>

## EX1.2 — Characterize the ordinary dominator tree

- Milestone: EX1; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.1.
- Proposed owner module: `release-core/PaperB/Dom.lean`.
- Paper consumers: 1.1, 2.1, 2.2, 5.1; risk: ordinary.

Prove inclusive ancestor iff ordinary domination on the reachable DAG, with LCA, child subtrees and prefix/suffix facts.

Acceptance:

- Give a tree construction or existence proof on all retained DAGs and characterize single deletion. Justify the root, singleton, and reachable nonroot predecessor cases.
- This semantic result supplies the labelled quotient independently of machine code.

Lean verifies the ordinary dominator tree semantically on every acyclic input, with ancestral equivalence on all reachable vertices. The proof refines any topological rank to an injective one and verifies strict descent for the parent. EX1.2’s tracker closure awaits EX1.1; the executable predecessor-LCA constructor remains under EX1.5.

Planning/evidence references: [evidence/ex12-dominator-predecessors/verification.json](evidence/ex12-dominator-predecessors/verification.json), [evidence/ex12-dominator-chain/verification.json](evidence/ex12-dominator-chain/verification.json), [evidence/ex12-immediate-dominator/verification.json](evidence/ex12-immediate-dominator/verification.json), [evidence/ex12-dominator-tree/verification.json](evidence/ex12-dominator-tree/verification.json), [evidence/ex12-topological-rank/verification.json](evidence/ex12-topological-rank/verification.json).

<a id="ex13"></a>

## EX1.3 — Project and lift labelled sibling paths

- Milestone: EX1; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.2.
- Proposed owner module: `release-core/PaperB/Quotient.lean`.
- Paper consumers: 1.1, 2.1; risk: ordinary.

Assign each retained arc to its head parent, store its original tail, and prove flatness, projection and lifting.

Acceptance:

- Any sequence of parallel labelled exits lifts. Sum all quotient sizes: at most 2n vertex copies and one quotient arc per arc.
- Prove unique outside-to-root entry and internal reachability, keep parallel tails distinguishable, and prove that every nonroot vertex of the quotient has the quotient root as immediate dominator.

The actual finite sibling quotient vertex keys sum to at most twice the original vertex count over distinct root IDs. Discharge the predecessor task certificates before closing EX1.3.

Planning/evidence references: [evidence/ex13-dominator-boundary/verification.json](evidence/ex13-dominator-boundary/verification.json), [evidence/ex13-block-lifting/verification.json](evidence/ex13-block-lifting/verification.json), [evidence/ex13-block-projection/verification.json](evidence/ex13-block-projection/verification.json), [evidence/ex13-dominator-segment/verification.json](evidence/ex13-dominator-segment/verification.json), [evidence/ex13-unique-child/verification.json](evidence/ex13-unique-child/verification.json), [evidence/ex13-sibling-blocks/verification.json](evidence/ex13-sibling-blocks/verification.json), [evidence/ex13-failed-suffix/verification.json](evidence/ex13-failed-suffix/verification.json), [evidence/ex13-sibling-system/verification.json](evidence/ex13-sibling-system/verification.json), [evidence/ex13-sibling-flatness/verification.json](evidence/ex13-sibling-flatness/verification.json), [evidence/ex13-arc-ownership/verification.json](evidence/ex13-arc-ownership/verification.json), [evidence/ex13-sibling-encoding/verification.json](evidence/ex13-sibling-encoding/verification.json), [evidence/ex13-occurrence-budget/verification.json](evidence/ex13-occurrence-budget/verification.json), [evidence/ex13-quotient-arrays/verification.json](evidence/ex13-quotient-arrays/verification.json), [evidence/ex13-original-emissions/verification.json](evidence/ex13-original-emissions/verification.json), [evidence/ex13-finite-sibling/verification.json](evidence/ex13-finite-sibling/verification.json), [evidence/ex13-finite-flatness/verification.json](evidence/ex13-finite-flatness/verification.json), [evidence/ex13-quotient-array-counts/verification.json](evidence/ex13-quotient-array-counts/verification.json), [evidence/ex13-unique-arc-budget/verification.json](evidence/ex13-unique-arc-budget/verification.json), [evidence/ex13-actual-arc-budget/verification.json](evidence/ex13-actual-arc-budget/verification.json), [evidence/ex13-vertex-budget/verification.json](evidence/ex13-vertex-budget/verification.json).

<a id="ex14"></a>

## EX1.4 — Characterize partial-block reachability

- Milestone: EX1; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.3.
- Proposed owner module: `release-core/PaperB/Quotient.lean`.
- Paper consumers: 1.1, 2.2; risk: ordinary.

Separate outside, own-block and third-block targets and translate the last usable exit into a subtree test.

Acceptance:

- Prove nonemptiness of both exit sets and the inclusive ancestry tests for the LCA of physical tails.
- Cover a failure equal to a block root, the LCA target, a target outside its subtree and a direct last exit to a third block.

For a proper loss under two distinct nonroot failures, both original-tail sets in the finite flat quotient are nonempty, including a direct exit to the target. Instantiate on constructed sibling quotients and prove surviving original paths iff one usable exit in the remaining third-block case.

Planning/evidence references: [evidence/ex14-last-exit-outside-own/verification.json](evidence/ex14-last-exit-outside-own/verification.json), [evidence/ex14-both-exits/verification.json](evidence/ex14-both-exits/verification.json).

<a id="ex15"></a>

## EX1.5 — Construct the ordinary dominator tree within the oracle budget

- Milestone: EX1; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, cost model; assigned worker: unassigned.
- Dependencies: EX1.2, EX0.3, EX2.3.
- Proposed owner module: `release-core/PaperB/DomBuild.lean`.
- Paper consumers: 1.1; risk: resource bound.

Implement a checked constructor for the semantic tree on explicit DAG input. The proposed DAG route uses growing-tree LCAs of predecessors.

Acceptance:

- Prove that the immediate dominator of a reachable nonroot equals the LCA of its predecessors in the partial tree and that leaf insertion preserves all earlier ancestor relations, or provide a costed Lengauer–Tarjan implementation.
- For the DAG route, bound depth search, leaf insertion and all predecessor folds within O((n+m)L³) operations and O(n+m) peak words. State separately if the faster subroutine bound in Section 2 is established.

Lean verifies the semantic LCA recurrence on all reachable predecessors. The executable growing-tree fold and topological scan, resource costs and full constructor proof remain open.

Planning/evidence references: [evidence/ex15-predecessor-lca/verification.json](evidence/ex15-predecessor-lca/verification.json).

<a id="ex16"></a>

## EX1.6 — Implement static tree intervals, child lookup and LCA

- Milestone: EX1; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, cost model; assigned worker: unassigned.
- Dependencies: EX1.2, EX0.3.
- Proposed owner module: `release-core/PaperB/TreeIndex.lean`.
- Paper consumers: 1.1, 5.1; risk: resource bound.

Construct inclusive subtree intervals, ordered child ranges and a heavy-path index on the actual ordinary tree.

Acceptance:

- Prove interval ancestry and child lookup in O(1) and O(L) operations respectively, including both range endpoints.
- Use maximum subtree-size heavy children to bound light-edge crossings; prove O(L) per original-tree LCA, O(n) shared words, and construction within the oracle budget.

<a id="ex21"></a>

## EX2.1 — Identify the first proper loss

- Milestone: EX2; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.1.
- Proposed owner module: `release-core/PaperB/Forest.lean`.
- Paper consumers: 1.1, 3.1; risk: ordinary.

Show the first strict loss follows both endpoints and has exactly those distinct predecessors.

Acceptance:

- Handle parallel arcs, direct root edges and the absence of any proper loss.

Lean identifies the two endpoints as exactly the distinct predecessors of an earliest proper loss. The characterization now feeds the topological sweep. Statement-level certification is pending.

Planning/evidence references: [evidence/carbon-last-arc/review.md](evidence/carbon-last-arc/review.md), [evidence/carbon-first-proper-loss/review.md](evidence/carbon-first-proper-loss/review.md).

<a id="ex22"></a>

## EX2.2 — Prove the topological forest invariant

- Milestone: EX2; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX2.1.
- Proposed owner module: `release-core/PaperB/Forest.lean`.
- Paper consumers: 1.1, 3.1, 4.1; risk: ordinary.

Show raw predecessor losses form a prefix, and that each vertex label represents all its proper separating pairs.

Acceptance:

- Prove existing ordered pair keys keep the same parent, endpoint inclusion, nested proper-loss sets and the linear node count.
- Maintain the induction for every processed label and every real edge, including raw losses at endpoints. Cover the latest predecessor and why an existing pair key retains its parent.

Lean verified the bundled semantic Lemma 3.1 on a flat quotient with a supplied injective topological rank. The construction has exactly the canonical effective keys, a single artificial root, exact inclusive ancestor labels, nesting, fresh endpoint order and at most one real node per vertex in the count. Paper-level certification awaits the dependent input representation and statement audit.

Planning/evidence references: [evidence/carbon-forest-sweep/progress.json](evidence/carbon-forest-sweep/progress.json), [evidence/carbon-sweep-latest-member/verification.json](evidence/carbon-sweep-latest-member/verification.json), [evidence/carbon-forest-prefix/verification.json](evidence/carbon-forest-prefix/verification.json), [evidence/ex22-unattended/f0686845-5aaf-419e-ac39-903e187dc284-prefix.json](evidence/ex22-unattended/f0686845-5aaf-419e-ac39-903e187dc284-prefix.json), [evidence/ex22-unattended/f0686845-5aaf-419e-ac39-903e187dc284-pair-key-reuse.json](evidence/ex22-unattended/f0686845-5aaf-419e-ac39-903e187dc284-pair-key-reuse.json), [evidence/ex22-unattended/native-swarm-sweep-step.json](evidence/ex22-unattended/native-swarm-sweep-step.json), [evidence/ex22-unattended/native-swarm-global-sweep.json](evidence/ex22-unattended/native-swarm-global-sweep.json), [evidence/ex22-unattended/native-swarm-forest-parents.json](evidence/ex22-unattended/native-swarm-forest-parents.json), [evidence/ex22-unattended/native-swarm-lemma-3-1.json](evidence/ex22-unattended/native-swarm-lemma-3-1.json).

<a id="ex23"></a>

## EX2.3 — Implement depth jumps under leaf insertion

- Milestone: EX2; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: data structures; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX0.3.
- Proposed owner module: `release-core/PaperB/Jumps.lean`.
- Paper consumers: 1.1, 3.2, 5.1; risk: ordinary.

Use the v1.3 skew-binary parent, depth and jump records to reach a prescribed ancestor depth.

Acceptance:

- Prove constant-time insertion, O(L) moves per level search and O(L) online ancestry with one jump per node. See the [v1.3 acceptance addendum](../evidence/paper-b-log-shave-20261118/formalization-v1.3.md).

Lean verified the growing-tree invariant, unique depth-target traversal, the logarithmic move bound, and the array-backed jump implementation under a preallocated word layout. A leaf insertion uses 14 word accesses. The traversal and ancestry test have explicit logarithmic word-read bounds. The full EX0.3 package and end-to-end statement audit remain open.

Planning/evidence references: [evidence/ex22-unattended/native-swarm-jump-foundation.json](evidence/ex22-unattended/native-swarm-jump-foundation.json), [evidence/ex22-unattended/native-swarm-jump-invariant.json](evidence/ex22-unattended/native-swarm-jump-invariant.json), [evidence/ex22-unattended/native-swarm-jump-traversal.json](evidence/ex22-unattended/native-swarm-jump-traversal.json), [evidence/ex22-unattended/native-swarm-jump-move-bound.json](evidence/ex22-unattended/native-swarm-jump-move-bound.json), [evidence/ex22-unattended/native-swarm-word-memory.json](evidence/ex22-unattended/native-swarm-word-memory.json).

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

The interval traversal over the actual child buckets executes exactly 2N commands and empties its stack. Table value refinement and sweep integration remain open.

Planning/evidence references: [evidence/ex22-unattended/native-swarm-charging.json](evidence/ex22-unattended/native-swarm-charging.json), [evidence/public-lean-flatmap-split/verification.json](evidence/public-lean-flatmap-split/verification.json), [evidence/public-lean-interval-assembly/verification.json](evidence/public-lean-interval-assembly/verification.json), [evidence/public-lean-prefix-probe/verification.json](evidence/public-lean-prefix-probe/verification.json), [evidence/ex24-ancestry-interval/verification.json](evidence/ex24-ancestry-interval/verification.json), [evidence/ex24-prefix-cutoff/verification.json](evidence/ex24-prefix-cutoff/verification.json), [evidence/ex24-array-interval/verification.json](evidence/ex24-array-interval/verification.json), [evidence/ex24-predecessor-search/verification.json](evidence/ex24-predecessor-search/verification.json), [evidence/ex24-pair-lookup/verification.json](evidence/ex24-pair-lookup/verification.json), [evidence/ex24-dfs-array-builder/verification.json](evidence/ex24-dfs-array-builder/verification.json), [evidence/ex24-dfs-stack-potential/verification.json](evidence/ex24-dfs-stack-potential/verification.json), [evidence/ex24-dfs-exact-count/verification.json](evidence/ex24-dfs-exact-count/verification.json).

<a id="ex31"></a>

## EX3.1 — Lift each fresh endpoint contribution

- Milestone: EX3; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX2.2, EX1.3.
- Proposed owner module: `release-core/PaperB/Exit.lean`.
- Paper consumers: 4.1; risk: ordinary.

Give the forward witness using topological order for each fresh child endpoint, for arbitrary parallel exit tails.

Acceptance:

- Prove inclusion for every output coordinate and target in the child proper-loss set.

Lean checks the fresh-endpoint term on every real edge of the constructed forest of a supplied flat labelled quotient. The original-graph to labelled-quotient bridge remains open.

Planning/evidence references: [evidence/ex33-forest-exit/verification.json](evidence/ex33-forest-exit/verification.json).

<a id="ex32"></a>

## EX3.2 — Handle inherited tails and the reverse inclusion

- Milestone: EX3; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX3.1.
- Proposed owner module: `release-core/PaperB/Exit.lean`.
- Paper consumers: 4.1; risk: path semantics.

Prove the bypass argument for a shared endpoint and the converse for each child visitation pattern.

Acceptance:

- Discharge disjoint pairs, inherited-only exits and exits through a fresh endpoint with exact tail identity.

Lean checks the inherited term and converse on each real edge of the constructed forest. No overlap hypothesis is needed. The original-graph to labelled-quotient bridge remains open.

Planning/evidence references: [evidence/ex33-forest-exit/verification.json](evidence/ex33-forest-exit/verification.json).

<a id="ex33"></a>

## EX3.3 — Certify the set-level transfer theorem

- Milestone: EX3; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX3.2.
- Proposed owner module: `release-core/PaperB/Exit.lean`.
- Paper consumers: 4.1; risk: ordinary.

Assemble both inclusions as an equality of finite sets of physical tails before compression.

Acceptance:

- An independent statement audit verifies quantification over every real forest edge, both coordinates and every proper-loss target.
- Instantiate the structural identity on the actual constructed forest and the original-tail labels. Figure 1 checks both exact contributions and all three failure outcomes as a regression control.

Lean now instantiates exit transfer on the actual Fin-labelled sibling quotient built from original DAG arcs. It carries the exact physical tail. Figure 1 replays. Whole task and paper-statement acceptance await EX1.3 and EX2 evidence and the dependent task checklist.

Planning/evidence references: [evidence/ex33-forest-exit/verification.json](evidence/ex33-forest-exit/verification.json), [evidence/ex33-figure-1/verification.json](evidence/ex33-figure-1/verification.json), [evidence/ex13-finite-flatness/verification.json](evidence/ex13-finite-flatness/verification.json).

<a id="ex41"></a>

## EX4.1 — Implement the two-coordinate map algebra

- Milestone: EX4; status: **IN_PROGRESS**; proof status: NOT_CERTIFIED.
- Owner: oracle; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX3.3, EX1.2.
- Proposed owner module: `release-core/PaperB/Index.lean`.
- Paper consumers: 1.1, 5.1; risk: ordinary.

Formalize the LCA join with an empty sentinel and constant-plus-optional-coordinate maps.

Acceptance:

- Prove identity, evaluation and composition, including missing slots and endpoint reordering with bounded storage.

Lean verifies two-coordinate map composition and interval joins. Computed rank summaries compose over concatenation, and their endpoint test is equivalent to all listed tail ranks lying in the half-open subtree interval, with an explicit empty case. Integration with stored exit tails and bounded word accounting remain open.

Planning/evidence references: [evidence/ex41-exit-map-algebra/verification.json](evidence/ex41-exit-map-algebra/verification.json), [evidence/ex41-exit-extrema/verification.json](evidence/ex41-exit-extrema/verification.json).

<a id="ex42"></a>

## EX4.2 — Install maps before bases in topological order

- Milestone: EX4; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: oracle; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX4.1, EX2.4.
- Proposed owner module: `release-core/PaperB/Index.lean`.
- Paper consumers: 1.1, 5.1; risk: dependency order.

Show every map and predecessor base read at installation already exists.

Acceptance:

- Prove the induction for initial seeds, repeated seeds, artificial-root maps and all labelled incoming arcs.
- The path above the already processed fresh endpoint has maps installed. For an earlier off-endpoint predecessor, propagate its base; for an endpoint arc add its own physical tail.

<a id="ex43"></a>

## EX4.3 — Build and evaluate composed jump maps

- Milestone: EX4; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: oracle; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX4.2, EX2.3, EX1.6.
- Proposed owner module: `release-core/PaperB/Index.lean`.
- Paper consumers: 1.1, 5.1; risk: ordinary.

Construct one upward jump map per real pair and recover both summary coordinates from the vertex base.

Acceptance:

- Match the set semantics for any target and allowed ancestor in O(L²) moves and O(L³) word operations.
- Prove all of Lemma 5.1 locally: per-quotient build O((n_H+m_H)L³), O(n_H+m_H) temporary words and O(n_H) retained records. Charge each arc and each installation.

<a id="ex44"></a>

## EX4.4 — Decide arbitrary post-build queries

- Milestone: EX4; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: oracle; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.4, EX4.3, EX1.5.
- Proposed owner module: `release-core/PaperB/Oracle.lean`.
- Paper consumers: 1.1; risk: ordinary.

Implement the full case split once on the retained index; include missing pair keys and comparable failures.

Acceptance:

- Prove output iff reachability after deletion for any subset of size at most two and any original target.
- Sort the two quotient endpoints and carry their corresponding original failures with them. Cover missing keys, pairs off the target label's ancestor chain, and zero-length paths.

<a id="ex51"></a>

## EX5.1 — Account for discovery and every edge scan

- Milestone: EX5; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: cost model; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX0.3, EX2.4, EX4.3, EX1.5, EX1.6.
- Proposed owner module: `release-core/PaperB/Resources.lean`.
- Paper consumers: 1.1; risk: resource bound.

Sum all phases, including sorting, dominator construction, repeated predecessor scans and LCA operations.

Acceptance:

- Prove deterministic O((n+m)L³) build time for the compiled data layout.

<a id="ex52"></a>

## EX5.2 — Bound peak workspace and the retained index

- Milestone: EX5; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: cost model; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX5.1.
- Proposed owner module: `release-core/PaperB/Resources.lean`.
- Paper consumers: 1.1; risk: resource bound.

Give allocation lifetimes and index serialization for the same construction.

Acceptance:

- Prove O(n+m) construction words and O(n) retained words including original IDs, and discard input adjacency.
- Prove a peak over all intermediate states, and a separate bound on storage reachable from the query index after disposal, including ID translation and copy or serialization costs.

<a id="ex53"></a>

## EX5.3 — Bound each later query and exclude adjacency access

- Milestone: EX5; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: cost model; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX4.4, EX5.2.
- Proposed owner module: `release-core/PaperB/Resources.lean`.
- Paper consumers: 1.1; risk: ordinary.

Run the fixed query program on only the stored index, failure set and one target.

Acceptance:

- Give an O(L³) bound independent of graph density, target choice, batch size and previous queries.

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

- Milestone: EX5; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: application; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX5.4.
- Proposed owner module: `extensions/Batch.lean`.
- Paper consumers: 1.2; risk: ordinary.

Aggregate online memberships as disjunctions while charging list accesses and explicit output writes.

Acceptance:

- Handle q empty lists, repetitions, arbitrary overlap, O(SL³) total time and O(S) workspace with S=n+m+q+M.
- Produce one Boolean per original list in order, prove the later-single-list bound, and allow logarithmic words in S+2.

<a id="ex61"></a>

## EX6.1 — Prove the guarded-path and shrinking-witness equivalence

- Milestone: EX6; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: application; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.1.
- Proposed owner module: `extensions/Guarded.lean`.
- Paper consumers: 6.1; risk: ordinary.

Relate truth of a supplied healthy-zero root to a surviving labelled terminal and shrink the witness to Q union a candidate singleton.

Acceptance:

- Cover constant-zero terminals, repeated labels, forced guard deletions and both choices of Q.

<a id="ex62"></a>

## EX6.2 — Account for all label and terminal incidences

- Milestone: EX6; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: application; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX6.1, EX5.5.
- Proposed owner module: `extensions/Guarded.lean`.
- Paper consumers: 6.1; risk: ordinary.

Encode each candidate with at most two residual guard failures and its full terminal list.

Acceptance:

- Return an admissible detecting set for each positive case and prove O(G_dec log³(G_dec+2)) time and O(G_dec) words.
- Map each positive output index back to i, including multiple terminals of one label, and return Q union {i}. The number of failed vertices per candidate counts distinct guards after the shared deletion.

