# Paper B task tracker

Generated from tasks.json. Owner roles are proposed responsibilities, not active agents. Acceptance means exact theorem fidelity and required evidence, not a file count.

<a id="ex01"></a>

## EX0.1 — Freeze paper identities and statement locations

- Milestone: EX0; status: **DONE_PLAN**; proof status: PLANNING_ONLY.
- Owner: contract; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: none.
- Proposed owner module: `release-core/Challenge.lean`.
- Paper consumers: 1.1, 4.1; risk: ordinary.

Bind the active article, prior editions and companion to their sources.

Acceptance:

- Preserve content hashes, ten numbered statements, and the distinct proof location of Theorem 1.1.

Planning/evidence references: [sources/source-lock.json](sources/source-lock.json).

<a id="ex02"></a>

## EX0.2 — Pin the environment and elaborate candidate interfaces

- Milestone: EX0; status: **READY**; proof status: NOT_CERTIFIED.
- Owner: contract; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX0.1.
- Proposed owner module: `release-core/Challenge.lean`.
- Paper consumers: 1.1, 4.1; risk: ordinary.

Typecheck candidate signatures for a finite labelled DAG, tail sets, immutable index and costed programs.

Acceptance:

- Record the toolchain, supported imports, exact elaborated types and a review of the quantifier order.

<a id="ex03"></a>

## EX0.3 — Define execution and storage units

- Milestone: EX0; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: cost model; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX0.2.
- Proposed owner module: `release-core/PaperB/Machine.lean`.
- Paper consumers: 1.1, 3.2, 5.1; risk: ordinary.

Specify word size, addressable arrays, peak live words, retained index size and the available query input.

Acceptance:

- Define all four resource observables, including construction temporaries and input-sized addresses for parallel arcs.

<a id="ex11"></a>

## EX1.1 — Normalize original vertices and failure sets

- Milestone: EX1; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: graph; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX0.2.
- Proposed owner module: `release-core/PaperB/Graph.lean`.
- Paper consumers: 1.1, 2.1, 2.2; risk: ordinary.

Define reachability, source deletion, zero-length paths, repeated failures, unreachable vertices, and parallel input arcs.

Acceptance:

- Prove translation to the retained DAG preserves every original query, including failed targets and discarded identifiers.

<a id="ex12"></a>

## EX1.2 — Construct the original dominator tree

- Milestone: EX1; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.1, EX0.3.
- Proposed owner module: `release-core/PaperB/Dom.lean`.
- Paper consumers: 1.1, 2.1, 2.2, 5.1; risk: ordinary.

Realize dominators, interval ancestry, child location and lowest common ancestors on the same graph.

Acceptance:

- Provide algorithmic provenance and time and live-word bounds for the actual tree and query primitives.

<a id="ex13"></a>

## EX1.3 — Project and lift labelled sibling paths

- Milestone: EX1; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.2.
- Proposed owner module: `release-core/PaperB/Quotient.lean`.
- Paper consumers: 1.1, 2.1; risk: ordinary.

Assign each retained arc to its head parent, store its original tail, and prove flatness, projection and lifting.

Acceptance:

- Any sequence of parallel labelled exits lifts. Sum all quotient sizes: at most 2n vertex copies and one quotient arc per arc.

<a id="ex14"></a>

## EX1.4 — Characterize partial-block reachability

- Milestone: EX1; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: dominator; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.3.
- Proposed owner module: `release-core/PaperB/Quotient.lean`.
- Paper consumers: 1.1, 2.2; risk: ordinary.

Separate outside, own-block and third-block targets and translate the last usable exit into a subtree test.

Acceptance:

- Prove nonemptiness of both exit sets and the inclusive ancestry tests for the LCA of physical tails.

<a id="ex21"></a>

## EX2.1 — Identify the first proper loss

- Milestone: EX2; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.3.
- Proposed owner module: `release-core/PaperB/Forest.lean`.
- Paper consumers: 1.1, 3.1; risk: ordinary.

Show the first strict loss follows both endpoints and has exactly those distinct predecessors.

Acceptance:

- Handle parallel arcs, direct root edges and the absence of any proper loss.

<a id="ex22"></a>

## EX2.2 — Prove the topological forest invariant

- Milestone: EX2; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX2.1.
- Proposed owner module: `release-core/PaperB/Forest.lean`.
- Paper consumers: 1.1, 3.1, 4.1; risk: ordinary.

Show raw predecessor losses form a prefix, and that each vertex label represents all its proper separating pairs.

Acceptance:

- Prove existing ordered pair keys keep the same parent, endpoint inclusion, nested proper-loss sets and the linear node count.

<a id="ex23"></a>

## EX2.3 — Implement depth jumps under leaf insertion

- Milestone: EX2; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: data structures; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.1, EX0.3.
- Proposed owner module: `release-core/PaperB/Jumps.lean`.
- Paper consumers: 1.1, 3.2, 5.1; risk: ordinary.

Reach a prescribed ancestor depth by one low-bit pointer and a parent pointer per node.

Acceptance:

- Bound the number of traversal steps by O(L²), including construction of each new jump and overshoots.

<a id="ex24"></a>

## EX2.4 — Charge forest construction and membership

- Milestone: EX2; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX2.2, EX2.3.
- Proposed owner module: `release-core/PaperB/Forest.lean`.
- Paper consumers: 1.1, 3.2; risk: resource bound.

Implement raw-predecessor tests, depth search, candidate key lookup and final ancestry intervals.

Acceptance:

- Prove per-quotient O((n_H+m_H)L³) build, O(n_H+m_H) peak, O(n_H) retained, O(L) key lookup and O(1) known-node test.

<a id="ex31"></a>

## EX3.1 — Lift each fresh endpoint contribution

- Milestone: EX3; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX2.2.
- Proposed owner module: `release-core/PaperB/Exit.lean`.
- Paper consumers: 4.1; risk: ordinary.

Give the forward witness using topological order for each fresh child endpoint, for arbitrary parallel exit tails.

Acceptance:

- Prove inclusion for every output coordinate and target in the child proper-loss set.

<a id="ex32"></a>

## EX3.2 — Handle inherited tails and the reverse inclusion

- Milestone: EX3; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX3.1.
- Proposed owner module: `release-core/PaperB/Exit.lean`.
- Paper consumers: 4.1; risk: path semantics.

Prove the bypass argument for a shared endpoint and the converse for each child visitation pattern.

Acceptance:

- Discharge disjoint pairs, inherited-only exits and exits through a fresh endpoint with exact tail identity.

<a id="ex33"></a>

## EX3.3 — Certify the set-level transfer theorem

- Milestone: EX3; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: cuts; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX3.2.
- Proposed owner module: `release-core/PaperB/Exit.lean`.
- Paper consumers: 4.1; risk: ordinary.

Assemble both inclusions as an equality of finite sets of physical tails before compression.

Acceptance:

- An independent statement audit verifies quantification over every real forest edge, both coordinates and every proper-loss target.

<a id="ex41"></a>

## EX4.1 — Implement the two-coordinate map algebra

- Milestone: EX4; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: oracle; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX3.3, EX1.2.
- Proposed owner module: `release-core/PaperB/Index.lean`.
- Paper consumers: 1.1, 5.1; risk: ordinary.

Formalize the LCA join with an empty sentinel and constant-plus-optional-coordinate maps.

Acceptance:

- Prove identity, evaluation and composition, including missing slots and endpoint reordering with bounded storage.

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

<a id="ex43"></a>

## EX4.3 — Build and evaluate composed jump maps

- Milestone: EX4; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: oracle; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX4.2, EX2.3.
- Proposed owner module: `release-core/PaperB/Index.lean`.
- Paper consumers: 1.1, 5.1; risk: ordinary.

Construct one upward jump map per real pair and recover both summary coordinates from the vertex base.

Acceptance:

- Match the set semantics for any target and allowed ancestor in O(L²) moves and O(L³) word operations.

<a id="ex44"></a>

## EX4.4 — Decide arbitrary post-build queries

- Milestone: EX4; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: oracle; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX1.4, EX4.3.
- Proposed owner module: `release-core/PaperB/Oracle.lean`.
- Paper consumers: 1.1; risk: ordinary.

Implement the full case split once on the retained index; include missing pair keys and comparable failures.

Acceptance:

- Prove output iff reachability after deletion for any subset of size at most two and any original target.

<a id="ex51"></a>

## EX5.1 — Account for discovery and every edge scan

- Milestone: EX5; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: cost model; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX0.3, EX2.4, EX4.3.
- Proposed owner module: `release-core/PaperB/Resources.lean`.
- Paper consumers: 1.1, 3.2, 5.1; risk: resource bound.

Sum all phases, including sorting, dominator construction, repeated predecessor scans and LCA operations.

Acceptance:

- Prove deterministic O((n+m)L³) build time for the compiled data layout.

<a id="ex52"></a>

## EX5.2 — Bound peak workspace and the retained index

- Milestone: EX5; status: **PLANNED**; proof status: NOT_CERTIFIED.
- Owner: cost model; reviewers: statement fidelity, independent replay; assigned worker: unassigned.
- Dependencies: EX5.1.
- Proposed owner module: `release-core/PaperB/Resources.lean`.
- Paper consumers: 1.1, 3.2, 5.1; risk: resource bound.

Give allocation lifetimes and index serialization for the same construction.

Acceptance:

- Prove O(n+m) construction words and O(n) retained words including original IDs, and discard input adjacency.

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

