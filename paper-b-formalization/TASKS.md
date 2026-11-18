# Paper B task tracker

Generated from tasks.json. Owner roles are proposed responsibilities, not active agents. Acceptance means exact theorem fidelity and required evidence, not a file count.

<a id="pb01"></a>

## PB0.1 — Pin the active draft and published baseline

- Milestone: PB0; status: **DONE_PLAN**; proof status: PLANNING_ONLY.
- Owner: coordinator; reviewers: to assign; assigned worker: unassigned.
- Dependencies: none.
- Proposed owner module: `sources/source-lock.json`.
- Paper consumers: ; risk: S.

Bind the v1.1 draft, its 32-entry statement inventory and companions, preserving the published v1.0 source/PDF lock.

Acceptance:

- Published v1.0 PDF/source identities remain protected.
- The active v1.1 draft and 32 statement/proof blocks are hashed separately; no v1.1 PDF or DOI is asserted.

Planning/evidence references: [sources/source-lock.json](sources/source-lock.json), [sources/authority-retrieval.json](sources/authority-retrieval.json).

<a id="pb02"></a>

## PB0.2 — Audit existing Lean and registry reuse

- Milestone: PB0; status: **DONE_PLAN**; proof status: PLANNING_ONLY.
- Owner: coordinator; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB0.1.
- Proposed owner module: `reuse-audit.json`.
- Paper consumers: ; risk: M.

Separate local B01 evidence, registered Paper A inputs, obsolete board entries and missing replay environment.

Acceptance:

- Historical successful and failed runs distinguished.
- No Paper B headline promoted from Paper A registration.

Planning/evidence references: [reuse-audit.json](reuse-audit.json), [REUSE.md](REUSE.md).

<a id="pb03"></a>

## PB0.3 — Approve selected roots and module ownership

- Milestone: PB0; status: **READY**; proof status: PLANNING_ONLY.
- Owner: coordinator; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB0.1, PB0.2.
- Proposed owner module: `contracts/release-contract.md`.
- Paper consumers: 3.2, 3.3; risk: M.

Approve the narrow first release, full-paper extension sequence and source-size review thresholds.

Acceptance:

- Selected root names, nonclaims, owners and zero-unreachable-module invariant approved as an architecture; exact typed signature approval follows PB0.4.
- No implementation until this architecture decision is recorded.
- The informal all-query/width/weighted scope is authorized; this does not substitute for approval of elaborated Lean signatures.

<a id="pb04"></a>

## PB0.4 — Elaborate a nonvacuous statement and cost surface

- Milestone: PB0; status: **PLANNED**; proof status: PLANNING_ONLY.
- Owner: coordinator; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB0.3, PB0.5.
- Proposed owner module: `release-core/Challenge.lean`.
- Paper consumers: 3.2, 3.3; risk: L.

Type-check the actual graph, encoding, fixed solver/step and resource contracts before proving the headline.

Acceptance:

- Challenge uses only allowed imports and explicit definitions.
- Reject per-input hardcoded solver, arbitrary zero work, uncharged oracle and hidden average-case interpretation.
- Exact signatures replace the design sketches in INTERFACES.md.
- Record author approval of the final elaborated Challenge/release contract before any theorem proof begins.
- The Challenge requires a full original-index Boolean vector; the OR is a derived projection, not the advertised correctness claim.

<a id="pb05"></a>

## PB0.5 — Pin and rehearse the supported environment

- Milestone: PB0; status: **PLANNED**; proof status: PLANNING_ONLY.
- Owner: infrastructure; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB0.3.
- Proposed owner module: `release-core/lake-manifest.json`.
- Paper consumers: 3.2, 3.3; risk: L.

Select a supported Lean/Mathlib pair and bounded graph/data-structure library reuse; run a small clean pilot.

Acceptance:

- Full commits, licenses and trusted Challenge dependency ancestry pinned.
- Current floor checked; local legacy 4.33 environment is not reused silently.
- No whole historical Controller import.

<a id="pb11"></a>

## PB1.1 — Define per-query reachability and the answer vector

- Milestone: PB1; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: graph; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB0.4, PB0.5.
- Proposed owner module: `release-core/PaperB/Spec.lean`.
- Paper consumers: 3.1, 3.2, 3.3, 4.2, 4.3, 4.5, B.1, B.2, B.3; risk: M.

Define valid inputs, per-query success and a complete vector indexed by original query IDs; define existential success as its OR.

Acceptance:

- Length-zero path is allowed exactly at a surviving vertex.
- Failed root/target, empty batch and empty target list specified.
- Count target occurrences and stored arcs; distinguish set sensitivity from raw list size.

<a id="pb12"></a>

## PB1.2 — Normalize input while preserving every query answer

- Milestone: PB1; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: graph; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.1, PB4.1.
- Proposed owner module: `release-core/PaperB/Normalize.lean`.
- Paper consumers: 3.1, 3.2, 4.3, 4.5; risk: M.

Return settled original-index answers plus an injectively mapped unresolved batch; positive normalization must continue.

Acceptance:

- Both directions of answer equivalence and original-target correspondence.
- All scans and reindexing charged to explicit input.
- Legacy decreasing-rank edges are reindexed, not reversed.

<a id="pb13"></a>

## PB1.3 — Prove single-failure and domination semantics

- Milestone: PB1; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: graph; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.1.
- Proposed owner module: `release-core/PaperB/Dominators.lean`.
- Paper consumers: 3.1, 3.2, 4.1, 4.3, 4.5, B.1; risk: M.

Connect path-based domination, reflexive ancestry, failed targets and dominance-comparable failure pairs.

Acceptance:

- Domination is restricted appropriately to initially reachable vertices.
- Removing a dominated second failure changes no surviving answer.

<a id="pb14"></a>

## PB1.4 — Construct the dominator tree and LCA index

- Milestone: PB1; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: graph; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.2, PB1.3, PB1.5.
- Proposed owner module: `release-core/PaperB/Dominators.lean`.
- Paper consumers: 3.1, 3.2, 4.3, 4.5, B.2; risk: L.

Prove predecessor-LCA insertion on a DAG and binary-lifting/Euler query implementation.

Acceptance:

- Construction O((V+E) log(V+2)), O(V log(V+2)) words established in the cost model.
- No assumed constant-time construction or free tree index.

<a id="pb15"></a>

## PB1.5 — Implement indices, answer maps and timestamp arrays

- Milestone: PB1; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: resources; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.2, PB4.1.
- Proposed owner module: `release-core/PaperB/Primitives.lean`.
- Paper consumers: 3.2, 3.3, 4.5; risk: L.

Implement target indexing, activity/deduplication arrays and original-index answer storage with charged initialization.

Acceptance:

- Targets are indexed in O(q_b+M) work.
- Array reset/epoch overflow and actual storage bounds are proved.
- No search over all queries per vertex.

<a id="pb21"></a>

## PB2.1 — Vertex-split capacities and deletion correspondence

- Milestone: PB2; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: kernel; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.1, PB1.3.
- Proposed owner module: `release-core/PaperB/SplitNetwork.lean`.
- Paper consumers: 3.1, 3.2, B.1; risk: L.

Build capacity-one gates and capacity-three transit/protected arcs with explicit reverse-arc identities.

Acceptance:

- Original surviving paths correspond to split-network paths.
- Parallel/reverse arcs cannot collapse identities.
- At most O(V+E) network entries.

<a id="pb22"></a>

## PB2.2 — Bounded augmentation and max-cut certificate

- Milestone: PB2; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: kernel; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB2.1, PB1.5.
- Proposed owner module: `release-core/PaperB/BoundedFlow.lean`.
- Paper consumers: 3.1, 3.2, B.1; risk: L.

Implement at most three unit augmenting searches and prove value-3 or maximum-value-2 alternatives.

Acceptance:

- Residual capacity, conservation and cut certificates proved.
- Search/decomposition workspace and all failed scans counted.
- No unproved max-flow oracle premise in selected roots.

<a id="pb23"></a>

## PB2.3 — Decompose the two flow paths

- Milestone: PB2; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: kernel; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB2.2.
- Proposed owner module: `release-core/PaperB/BoundedFlow.lean`.
- Paper consumers: 3.1, 3.2; risk: M.

Extract ordered paths and gate positions from the integral flow in the acyclic split network.

Acceptance:

- Each unprotected unit gate is on at most one path.
- Protected vertices may be shared; full vertex-disjointness is not assumed.

<a id="pb24"></a>

## PB2.4 — Compute residual path-rank labels

- Milestone: PB2; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: kernel; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB2.3.
- Proposed owner module: `release-core/PaperB/PathRanks.lean`.
- Paper consumers: 3.1, 3.2; risk: L.

Construct SCC/condensation and propagate two minima to characterize residual reachability.

Acceptance:

- Residual graph may be cyclic even though the input is a DAG.
- Infinity/sentinel cases and reverse-path monotonicity exact.
- O(V+E) total work/space, not repeated per-target reachability.

<a id="pb25"></a>

## PB2.5 — Prove arbitrary-target residual membership

- Milestone: PB2; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: kernel; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB2.3, PB2.4.
- Proposed owner module: `release-core/PaperB/Kernel.lean`.
- Paper consumers: 3.1, 3.2; risk: L.

Prove equation (3.1e) for every original target under a proper two-cut.

Acceptance:

- Targets outside the anchor cone, the root, and failed vertices included.
- Both directions of the union-of-residual-closures argument.

<a id="pb26"></a>

## PB2.6 — Recognize proper cuts at a proposed vertex

- Milestone: PB2; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: kernel; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.4, PB2.5.
- Proposed owner module: `release-core/PaperB/Kernel.lean`.
- Paper consumers: 3.2; risk: L.

Prove necessity and sufficiency of all four inequalities (3.2b), including orientation rejection and flow-3 success.

Acceptance:

- Requires failures disjoint from the anchor dominators.
- No-cut classification yields a surviving prefix, not a batch answer without a suffix.

<a id="pb27"></a>

## PB2.7 — Join kernel correctness and construction resources

- Milestone: PB2; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: kernel; reviewers: resources; assigned worker: unassigned.
- Dependencies: PB2.6, PB1.5.
- Proposed owner module: `release-core/PaperB/Kernel.lean`.
- Paper consumers: 3.1, 3.2; risk: L.

Export one implemented kernel with correctness and counted construction/evaluation costs.

Acceptance:

- Build O(V+E), evaluate O(1) per target after preprocessing.
- Graph scanning, flow, SCC, labels and reusable scratch included.
- No caller-supplied answer table or kernel-running-time assumption.

<a id="pb31"></a>

## PB3.1 — Define the all-query reverse-topological scheduler

- Milestone: PB3; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: scheduler; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.2, PB1.5, PB0.4.
- Proposed owner module: `release-core/PaperB/Scheduler.lean`.
- Paper consumers: 3.2; risk: M.

Implement vector answers, unknown/active state and historical light lists; record and retire positive and negative queries.

Acceptance:

- Fixed program determined before individual inputs.
- Effective threshold tau_eff=min(tau,q_prime+1); zero-query exits explicit.
- Kernel interface may be a named provisional hypothesis only until PB4.5.

<a id="pb32"></a>

## PB3.2 — Maintain the surviving-suffix invariant

- Milestone: PB3; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: scheduler; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB3.1.
- Proposed owner module: `release-core/PaperB/Scheduler.lean`.
- Paper consumers: 3.2; risk: M.

Each stored ID certifies a suffix to an original target avoiding its failures.

Acceptance:

- Pulling across original arcs preserves the invariant.
- Duplicate and stale labels have defined filter behavior.

<a id="pb33"></a>

## PB3.3 — Verify Resolve and positive/negative retirement

- Milestone: PB3; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: scheduler; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB3.2, PB2.6.
- Proposed owner module: `release-core/PaperB/Scheduler.lean`.
- Paper consumers: 3.2; risk: L.

Resolve records YES via a certified surviving prefix or target, otherwise scans the entire original target list before recording NO; either answer retires its own query.

Acceptance:

- Every call returns a definitive Boolean and retires only that query.
- NO requires all original targets to fail; YES may use a surviving prefix and the certified suffix.
- Record root arrivals and direct normalization positives without terminating the batch.
- Every later candidate at one heavy vertex uses the same one live kernel.

<a id="pb34"></a>

## PB3.4 — Prove vector correctness, completeness and termination

- Milestone: PB3; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: scheduler; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB3.3.
- Proposed owner module: `release-core/PaperB/Scheduler.lean`.
- Paper consumers: 3.2; risk: L.

Every recorded Boolean matches its own original query; no successful query remains active at the end; final unknown entries are NO.

Acceptance:

- Prove forall original i, answer[i]=true iff Success(I,i).
- Query-index map is injective and covers direct, resolved, root and final-negative cases exactly once.
- No successful still-active query can survive the path-following completeness argument.

<a id="pb41"></a>

## PB4.1 — Ground the operational and live-space model

- Milestone: PB4; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: resources; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB0.4, PB0.5.
- Proposed owner module: `release-core/PaperB/CostModel.lean`.
- Paper consumers: 3.2, 3.3, 2.2; risk: L.

Implement the frozen instruction, execution and live-storage semantics before algorithm proofs consume them; expose concrete primitive events and encoded-word constraints.

Acceptance:

- The model cannot grant arbitrary answers, ticks or peak-space fields to a candidate program.
- Instruction steps, array/word operations and memory lifetime are concrete; algorithm-specific refinements are proved in their owner modules.
- A fixed program or uniform program family precedes the individual input quantifier.
- The Proposition 2.2 construction counters require an actual primitive-refinement bridge before its linear-time claim is accepted.

<a id="pb42"></a>

## PB4.2 — Amortize every completed kernel by retirement

- Milestone: PB4; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: resources; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB3.3, PB4.1.
- Proposed owner module: `release-core/PaperB/Amortization.lean`.
- Paper consumers: 3.2; risk: M.

Prove K*tau_eff<=q_prime for the all-query schedule; every kernel completes and there is no final-positive-kernel slack.

Acceptance:

- Initial tau_eff buffered IDs are distinct and active; each is retired by this kernel.
- Retirement sets of all kernels are disjoint; K<=floor(q_prime/tau_eff).
- If threshold is capped above q_prime, no kernel is constructed.

<a id="pb43"></a>

## PB4.3 — Charge stale positive/negative labels and original targets

- Milestone: PB4; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: resources; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB3.4, PB4.1.
- Proposed owner module: `release-core/PaperB/Amortization.lean`.
- Paper consumers: 3.2; risk: L.

Prove every historical edge pull, including stale YES labels, is counted; a query enters Resolve at most once and all target scans total O(M).

Acceptance:

- Edge-induced entries <=E(tau_eff-1), including stale positives and negatives.
- Full target scans occur at most once per query; seeding and normalization are charged separately.
- Deduplication, resets and adjacency scans are not hidden.

<a id="pb44"></a>

## PB4.4 — Prove peak words including complete answer storage

- Milestone: PB4; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: resources; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB4.1, PB4.2, PB4.3, PB2.7.
- Proposed owner module: `release-core/PaperB/Resources.lean`.
- Paper consumers: 3.2; risk: L.

Bound all historical lists, output/ID maps, preprocessing, scratch and one live kernel in the concrete live-space model.

Acceptance:

- Peak <= explicit C(S+V tau_eff) times a fixed polylog.
- Workspace actually reused; no hidden list of all residual networks.
- Integer counters, sentinels and allocations fit the chosen logarithmic word width.
- Complete answer vector and original-index maps use O(q_b) words, absorbed by S; do not compute an individual-target table.

<a id="pb45"></a>

## PB4.5 — Close all-query Theorem 3.2 on original inputs

- Milestone: PB4; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: coordinator; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.4, PB2.7, PB3.4, PB4.2, PB4.3, PB4.4.
- Proposed owner module: `release-core/Solution.lean`.
- Paper consumers: 3.2; risk: L.

Join one fixed implemented vector solver with every-index correctness, total time and peak workspace; derive the existential projection without extra asymptotic cost.

Acceptance:

- Uniform constants/polylog exponent independent of the input and tau.
- Correct answer and both advertised total bounds in the same theorem cone.
- No abstract kernel, dominator, SCC or primitive-cost premise remains.

<a id="pb46"></a>

## PB4.6 — Derive threshold corollaries and the existential projection

- Milestone: PB4; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: coordinator; reviewers: resources, reviewer; assigned worker: unassigned.
- Dependencies: PB4.5.
- Proposed owner module: `release-core/Solution.lean`.
- Paper consumers: 3.2; risk: M.

Prove cap/ceil/empty-batch specializations and OR aggregation, with resource corollaries in Solution to avoid an import cycle.

Acceptance:

- Sparse E,q_b,M=O(V) gives soft-O(V^(3/2)) time.
- No claim of near-linear unrestricted time or all query answers from an OR solver.
- Derived root corollaries stay in Solution; Resources must not import Solution.

<a id="pb51"></a>

## PB5.1 — Represent immutable exact historical sets

- Milestone: PB5; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: sharing; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB3.1, PB4.1.
- Proposed owner module: `release-core/PaperB/Interning.lean`.
- Paper consumers: 3.3; risk: M.

Sort and intern actual ID tuples; define Lambda from all distinct nonempty retained historical tuples.

Acceptance:

- Equality is deterministic exact comparison, not a hash-collision assumption.
- Activity changes do not mutate shared tuples.

<a id="pb52"></a>

## PB5.2 — Refine the answer-vector scheduler through shared handles

- Milestone: PB5; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: sharing; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB5.1, PB3.4.
- Proposed owner module: `release-core/PaperB/Interning.lean`.
- Paper consumers: 3.3; risk: M.

Preserve every recorded answer and both retirement outcomes under exact immutable historical-set interning.

Acceptance:

- Same complete original-index answer vector and per-query retirement decisions.
- No assumption that overlapping sets are equal.

<a id="pb53"></a>

## PB5.3 — Close sharing time and space bounds

- Milestone: PB5; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: sharing; reviewers: resources; assigned worker: unassigned.
- Dependencies: PB5.2, PB4.5.
- Proposed owner module: `release-core/PaperB/Interning.lean`.
- Paper consumers: 3.3; risk: L.

Prove dictionary/sort costs fit the original time bound and space is soft-O(S+Lambda).

Acceptance:

- Lambda<=V(tau_eff-1), with all historically retained arrays counted.
- Small graph/zero batch cases avoid invalid E>=V-1 absorption.
- A balanced dictionary implementation or pinned proved realization supplies its costs.
- Interning consumes generic Resources/Scheduler bounds, not Solution, avoiding a cycle when Solution later selects the sharing root.

<a id="pb54"></a>

## PB5.4 — Formalize the two representation families

- Milestone: PB5; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: sharing; assigned worker: unassigned.
- Dependencies: PB5.3.
- Proposed owner module: `research/Examples.lean`.
- Paper consumers: E.1, E.2; risk: M.

Prove both all-m valid constructions and their V,E,q_b,M,S,Lambda formulas.

Acceptance:

- Power-of-two and minimum-m assumptions literal.
- Representation growth is not a universal space lower bound.
- Example-only code stays outside the first release unless explicitly selected.

<a id="pb61"></a>

## PB6.1 — Sorted dead-region intersection and anchor recognition

- Milestone: PB6; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.4, PB2.7.
- Proposed owner module: `research/CommonAnchor.lean`.
- Paper consumers: 3.1; risk: L.

Prove (3.1a)–(3.1c), shrinking seed-set updates, exact recognition and counted release queue.

Acceptance:

- New seeds flagged before removed seeds can be released.
- Each vertex/arc released once; sorting and target aggregation charged.
- Rejecting an anchor does not return UNSAT/NO for the original batch.

<a id="pb62"></a>

## PB6.2 — Single-occurrence linear theorem

- Milestone: PB6; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.3, PB8.1.
- Proposed owner module: `research/SingleFailure.lean`.
- Paper consumers: 4.1; risk: L.

Implement candidate/terminal grouping and single-dominator ancestry queries.

Acceptance:

- Semantic result may use a supplied tree, but full O(G) needs a proved exact-linear dominator construction.
- Do not replace BGK linear time by Lengauer–Tarjan or binary lifting without changing the advertised bound.

<a id="pb63"></a>

## PB6.3 — Independent trees and deletion localization

- Milestone: PB6; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.3.
- Proposed owner module: `research/Localization.lean`.
- Paper consumers: 4.2, 4.3; risk: M.

Prove dead/fixed/symmetric-difference partition and unchanged dominators for fixed vertices, under the exact independent-tree hypothesis.

Acceptance:

- Lemma 4.2 conditional inputs match its paper setup.
- Tree construction/cost is separately discharged for Theorem 4.3.

<a id="pb64"></a>

## PB6.4 — Output-sensitive dominator updates and Sigma charge

- Milestone: PB6; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB6.3, PB1.4, PB4.1.
- Proposed owner module: `research/Localization.lean`.
- Paper consumers: 4.3; risk: L.

Report subtree differences, maintain implicit unchanged parents and binary-lifting LCAs, and sum weighted work over a pair cover.

Acceptance:

- Independent-tree construction is proved/imported at an audited pin.
- Sigma identity and <=(V+E)min(|C|,2h) proved.
- No all-vertex reset per deletion; all target costs charged.

<a id="pb65"></a>

## PB6.5 — Explicit-update obstruction and Hamiltonian cases

- Milestone: PB6; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB6.3, PB6.7.
- Proposed owner module: `research/Examples.lean`.
- Paper consumers: 4.4, 4.6; risk: M.

Prove the skip-DAG idom changes, every-cover lower bound, easy batch rule and p=1 recognition corollary.

Acceptance:

- Every V>=12 and every independent-tree/cover choice quantified.
- Obstruction concerns explicit updates only; no Boolean-batch lower bound.

<a id="pb66"></a>

## PB6.6 — Later-failure crossing and target compression

- Milestone: PB6; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.3.
- Proposed owner module: `research/Chains.lean`.
- Paper consumers: 4.5; risk: L.

Prove the u<b<w crossing characterization and retain the last target per reachability chain.

Acceptance:

- Chain connecting paths may be nonedges.
- Suffix is safe only after the later failure.
- R_star<=min(M,q_b p) and compression work O(S).

<a id="pb67"></a>

## PB6.7 — Streamed columns and original-edge range indexes

- Milestone: PB6; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB6.6, PB1.4, PB4.1.
- Proposed owner module: `research/Chains.lean`.
- Paper consumers: 4.5, 4.6; risk: L.

Implement one coordinate column and one edge index at a time, validate proposed chains and aggregate query extrema.

Acceptance:

- Prove the full p(V+E), pR_star and q_b p log^2 V charges.
- Keep original transitive arcs; no contraction producing spurious paths.
- Near-linear workspace for every p; no small-p assumption in space theorem.

<a id="pb68"></a>

## PB6.8 — Construct width-aware greedy reachability chains

- Milestone: PB6; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: resources, reviewer; assigned worker: unassigned.
- Dependencies: PB1.2, PB4.1, PB6.6.
- Proposed owner module: `research/Width.lean`.
- Paper consumers: 4.7; risk: L.

Define width as minimum reachability-chain partition size; prove the overlapping-cover equivalence, max-uncovered-path DP and discovery bounds.

Acceptance:

- Algorithm does not receive kappa or an optimal partition.
- For remaining U vertices some fixed kappa-cover path contains at least U/kappa; prove termination and p=O(kappa log(V+2)), including kappa=1.
- Assign each vertex once to a selected path subsequence; storage O(V+E), all scans/iterations charged.

<a id="pb69"></a>

## PB6.9 — Compose constructed-width all-query bound

- Milestone: PB6; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: resources, reviewer; assigned worker: unassigned.
- Dependencies: PB6.8, PB6.7.
- Proposed owner module: `research/Width.lean`.
- Paper consumers: 4.7; risk: L.

Feed the actually constructed partition to the streamed solver and close Corollary 4.7.

Acceptance:

- Discovery plus validation plus p(V+E), pR_star and q_b p log^2 V fit soft-O(kappa*S).
- Peak working words stay soft-O(S), without storing every overlapping full path or all coordinate columns.
- No assertion that minimum disjoint edge-path count equals reachability width.

<a id="pb610"></a>

## PB6.10 — Verify linear-time weighted cover selection

- Milestone: PB6; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: resources, reviewer; assigned worker: unassigned.
- Dependencies: PB6.3, PB1.5, PB4.1.
- Proposed owner module: `research/WeightedCover.lean`.
- Paper consumers: 4.8; risk: L.

Implement residual weights and one-pass primal-dual selection on the remaining pair graph.

Acceptance:

- Zero weights, ties, duplicate edges and empty graphs covered.
- Maintain dual feasibility and selected-vertex tightness; prove cost(C)<=2 OPT_c without computing OPT_c.
- O(V+q_b) time/words; bounded integer weights and sums fit logarithmic word width.

<a id="pb611"></a>

## PB6.11 — Compose weighted region optimum bound

- Milestone: PB6; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: resources, reviewer; assigned worker: unassigned.
- Dependencies: PB6.10, PB6.4.
- Proposed owner module: `research/WeightedCover.lean`.
- Paper consumers: 4.8; risk: L.

Compute subtree costs, identify Sigma(C)=sum c(u), and close Corollary 4.8 under the same fixed independent trees.

Acceptance:

- Three bottom-up passes include weight discovery O(V+E).
- For fixed B,R prove O((S+OPT_c)log(V+2)) time and O(S+Vlog(V+2)) space with all-query answers.
- No exact optimum cover, global tree optimization, or free bipartite min-cut oracle is assumed.

<a id="pb71"></a>

## PB7.1 — Selectors, triangle and representation padding

- Milestone: PB7; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: reductions; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB8.2.
- Proposed owner module: `research/Triangle.lean`.
- Paper consumers: 5.1, 5.2; risk: L.

Construct the shared-layer selector and triangle equivalence, with actual declared-label/incidence counts and padding.

Acceptance:

- Guard multiplicity and forced-target conventions exact.
- Semantic equivalence, size and construction time exported separately.
- No copied shared layers hiding nG overhead.

<a id="pb72"></a>

## PB7.2 — Clique windows and fixed polynomial ratios

- Milestone: PB7; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: reductions; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB7.1.
- Proposed owner module: `research/Clique.lean`.
- Paper consumers: 5.3; risk: L.

Prove cyclic tuple consistency for k=2c+1, b>=a and all window-pair checks.

Acceptance:

- Every coordinate pair has cyclic distance <=c.
- n=a^c+2, G=Theta(b^(c+1)) and construction time proved with fixed-c constants.
- Integer rounding and every fixed gamma in (0,1) handled.

<a id="pb73"></a>

## PB7.3 — Copied-layer multiplicity tradeoff

- Milestone: PB7; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: reductions; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB7.1.
- Proposed owner module: `research/Selectors.lean`.
- Paper consumers: 5.7; risk: M.

Prove mu=s-h and size Theta(2^h p^2) for p=2^s.

Acceptance:

- Endpoints h=0,h=s and s=0 are explicit.
- No constant-mu superlinear lower bound inferred.

<a id="pb74"></a>

## PB7.4 — Directed-cycle reduction and essentiality

- Milestone: PB7; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: reductions; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB7.1.
- Proposed owner module: `research/Cycles.lean`.
- Paper consumers: 5.5, 5.6; risk: L.

Build the layered cycle instance, preserve all incidences and prove its YES-essentiality/two-sided promise.

Acceptance:

- k-Cycle quantifier order is forall epsilon exists k, not one fixed k for every epsilon.
- Unused-label and inaccessible padding is counted; NO instances remain in the promise.

<a id="pb75"></a>

## PB7.5 — Fix algorithm models and conditional transfers

- Milestone: PB7; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: complexity; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB7.1, PB7.2, PB7.3, PB7.4, PB4.1.
- Proposed owner module: `research/FineGrained.lean`.
- Paper consumers: 5.1, 5.2, 5.3, 5.5, 5.6, 5.7, D.1, D.2; risk: L.

Give exact deterministic/log-word-RAM and source-hypothesis contracts; prove reduction closure and exponent-transfer inequalities.

Acceptance:

- Combinatorial is not an unconstrained Boolean tag.
- Conjectures are explicit hypotheses; proved construction inputs are not silently axiomatized.
- Real asymptotic families, parameter promises and fixed constants preserve their quantifier order.

<a id="pb76"></a>

## PB7.6 — Balanced algebraic clique implication

- Milestone: PB7; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: complexity; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB7.2, PB7.5.
- Proposed owner module: `research/FineGrained.lean`.
- Paper consumers: 5.4; risk: L.

Prove the large-clique grouping, exponent slack and rounding under precisely the F=omega hypothesis.

Acceptance:

- Every fixed c>=2; no c=1 boundary claim.
- Only deterministic conclusions unless randomized assumptions are independently supplied.

<a id="pb81"></a>

## PB8.1 — Guarded-path and linear OSR equivalence

- Milestone: PB8; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: adapters; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB1.1, PB0.2.
- Proposed owner module: `research/Guarded.lean`.
- Paper consumers: 2.1, 2.2; risk: L.

Port the smallest B01 semantic cone, complete both explicit transformations, query counts and sensitivity equality.

Acceptance:

- Common forced deletion performed once.
- Healthy-zero condition, root deletion and repeated target labels handled.
- Linear operation counters are not called RAM time until their implementation bridge is proved.

<a id="pb82"></a>

## PB8.2 — Baseline detector, dual-Horn and blocked bitsets

- Milestone: PB8; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: adapters; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB8.1, PB4.1.
- Proposed owner module: `research/Baselines.lean`.
- Paper consumers: A.1, A.2; risk: L.

Reuse audited Paper A detector ingredients and prove bitset block semantics and streaming storage.

Acceptance:

- Last partial word, unused labels and Q conventions exact.
- Support masks are not incorrectly asserted nodewise truth on every forced-target input.
- No all-block retention; no repeated scan hidden outside the bound.

<a id="pb83"></a>

## PB8.3 — Algebraic one-sided algorithm

- Milestone: PB8; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: algebra; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB8.1.
- Proposed owner module: `research/Algebraic.lean`.
- Paper consumers: A.3; risk: L.

Prove path-generating matrix identities, deleted-vertex correction, randomized nonzero test and hybrid search/minimum cost.

Acceptance:

- Field size and total error bound over all terminal tests proved.
- Matrix arithmetic cost and word/bit representation not conflated.
- Algebraic matrix multiplication time requires a proved model interface, not only an identity.

<a id="pb84"></a>

## PB8.4 — Canonical summaries, shortcuts and equality queries

- Milestone: PB8; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: structural; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB2.2, PB1.4.
- Proposed owner module: `research/Canonical.lean`.
- Paper consumers: B.1, B.2, B.3; risk: L.

Prove farthest-cut summary existence/uniqueness, same-vertex shortcut preservation and listed summary-equality reduction.

Acceptance:

- All failure sets of size <=2, including failed root and summary vertices.
- Summary vertices may be outside the original port set.
- Construction and streamed residual trees charged; summary discovery is not assumed near-linear.

<a id="pb85"></a>

## PB8.5 — Uniform capacity, Kraft and optimal budgets

- Milestone: PB8; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: selectors; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB2.1.
- Proposed owner module: `research/SelectorCapacity.lean`.
- Paper consumers: 5.8, C.1; risk: L.

Prove/import the actual preserver/anti-isolation input, vertex splitting, private-tree amplification, Kraft converse and total incidence optimum.

Acceptance:

- Selectors may have cycles: do not apply a DAG-only theorem.
- Until the external theorem is discharged, downstream results are explicitly conditional, not full formalization.
- n=1, mu=0, zero budgets and non-power-of-two n covered; construction output size charged.

<a id="pb86"></a>

## PB8.6 — Shared Hitting Set reduction and construction cost

- Milestone: PB8; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: adapters; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB8.1, PB8.2, PB4.1.
- Proposed owner module: `research/Applications.lean`.
- Paper consumers: D.1, D.2; risk: L.

Prove shared-U Hitting Set equivalence, exact incidence-size bounds and actual construction cost, before applying conditional algorithm-model transfers.

Acceptance:

- Empty requirements/candidates correct; shared U stored once.
- Healthy-one falsification is distinct from the OSR path contract.
- Explicit O_c(m log m) construction, not just semantic reduction.

<a id="pb87"></a>

## PB8.7 — Conditional Hitting Set and joint exponents

- Milestone: PB8; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: adapters; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB8.6, PB7.5, PB7.2.
- Proposed owner module: `research/Applications.lean`.
- Paper consumers: D.1, D.2; risk: L.

Compose the fully charged Hitting Set and clique reductions under their separate literal hypotheses.

Acceptance:

- Preserve every epsilon, gamma and beta quantifier and size regime.
- Match the O((n+q)G) upper bound using the same count conventions.

<a id="pb88"></a>

## PB8.8 — Physical and native-encoding application

- Milestone: PB8; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: adapters; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB8.1, PB8.7, PB7.6, PB4.6, PB5.3, PB6.1, PB6.2, PB6.4, PB6.7, PB8.3, PB8.4, PB6.9, PB6.11.
- Proposed owner module: `research/Applications.lean`.
- Paper consumers: 6.1; risk: L.

Compose the published Paper A fault-image and guarded-decision interfaces with Paper B algorithms/reductions and native-size accounting.

Acceptance:

- Source pins and selected Paper A declarations checked literally.
- Supplied role annotations, one bus/one driver, native N=Theta(G), model lifting and physical witness output are separately charged.
- No claim about arbitrary unannotated CNF or general 3-SAT.

<a id="pb91"></a>

## PB9.1 — Audit all-query statement fidelity and trust

- Milestone: PB9; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: reviewer; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB4.6.
- Proposed owner module: `release-core/Audit.lean`.
- Paper consumers: 3.2; risk: L.

Compare the frozen v1.1 statement with every-index correctness, the same solver in resource declarations, and exact dependency/trust closure.

Acceptance:

- Correctness is per original index; time and space apply to the very same fixed vector program.
- No sorryAx, native_decide trust extension, or project axiom in selected roots.
- Paper all-size statement is not replaced by finite test evidence.

<a id="pb92"></a>

## PB9.2 — Clean replay, Comparator and negative controls

- Milestone: PB9; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: reviewer; reviewers: infrastructure; assigned worker: unassigned.
- Dependencies: PB9.1.
- Proposed owner module: `release-core/Audit.lean`.
- Paper consumers: 3.2; risk: L.

Build the immutable selected cone from a clean snapshot and run statement comparison and independent mandatory kernel rehearsals.

Acceptance:

- Positive and deliberately invalid comparator/control cases checked.
- No stale oleans, missing manifest or invisible local dependency.
- Source headers, licenses and all public theorem axioms audited.

<a id="pb93"></a>

## PB9.3 — Extension fidelity and exact coverage status

- Milestone: PB9; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: reviewer; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB5.3, PB6.1, PB6.2, PB6.4, PB6.5, PB7.5, PB7.6, PB8.3, PB8.4, PB8.5, PB8.7, PB8.8, PB5.4, PB6.9, PB6.11.
- Proposed owner module: `research/Audit.lean`.
- Paper consumers: 2.1, 2.2, 3.1, 3.3, 4.1, 4.2, 4.3, 4.4, 4.5, 4.6, 5.1, 5.2, 5.3, 5.4, 5.5, 5.6, 5.7, 5.8, 6.1, A.1, A.2, A.3, B.1, B.2, B.3, C.1, D.1, D.2, 4.7, 4.8; risk: L.

Certify each additional paper claim only after its semantic, algorithmic and imported-input obligations close.

Acceptance:

- Never count Question 6.2 as a missing proof.
- A supported partial release is distinguished from whole-paper coverage.
- No registered Paper A declaration automatically counts as a Paper B theorem.

<a id="pb94"></a>

## PB9.4 — Prepare the selected release and manual registry packet

- Milestone: PB9; status: **PLANNED**; proof status: NOT_YET_CERTIFIED.
- Owner: coordinator; reviewers: to assign; assigned worker: unassigned.
- Dependencies: PB9.2.
- Proposed owner module: `release-core/formalization.yaml`.
- Paper consumers: 3.2; risk: M.

Freeze the narrow exact proof cone, provenance, license, declarations and user-controlled registration handoff.

Acceptance:

- No public push or registry state change without the applicable authorization.
- Submission, kernel verification, registry review and registration have distinct statuses.
- Adding 3.3 or other roots requires approved cone expansion and its own completed audit.

