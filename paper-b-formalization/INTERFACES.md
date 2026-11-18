# Mathematical and computational interfaces

These are design specifications for task coordination. **They are not elaborated Lean signatures, approved Challenge declarations, or proved interfaces.** PB0.4 must replace the release portion with exact type-checked declarations before theorem proofs begin. Proposed theorem names below are labels for that work, not declarations that already exist.

## I0. Explicit input and result

An input contains a finite nonempty vertex type, an explicit directed adjacency representation, a root, and indexed query records. Each query has a failure **set** of cardinality at most two and an explicit target list. The graph is acyclic; reachability allows a path of length zero exactly when its vertex survives.

For query `i`, define

\[
 Success(I,i) \iff \exists t\in T_i,\ \exists\text{ an }r\text{-to-}t
 \text{ path in }D-F_i.
\]

The primary result is an original-index Boolean vector `Answer(I)` satisfying `∀ i, Answer(I)[i]=true ↔ Success(I,i)`. The derived existential projection is `BatchSuccess(I) := ∃ i, Success(I,i)`. An empty batch returns an empty vector; an empty target list answers false. Failing the root makes that query false. Target lists may overlap across queries and may contain duplicates; the input count `M` counts their listed occurrences.

For the main theorem, `S=V+E+q_b+M`. If accepting raw failure lists rather than canonical sets, charge the raw length before deduplication; the cardinality-two promise does not bound an arbitrarily repeated raw list. Unused labels and explicit padding are part of the input, not free metadata.

Owner: PB1.1 / graph. Consumers: normalization, kernel and scheduler. Boundary checks: singleton graph; empty edge set; failed root; target equal to root; failed target; unreachable target; repeated target; empty batch; duplicate failure spelling.

## I1. Normalization and one-failure answers

`normalize` returns an explicit topological reindexing, reachable induced graph, normalized query records and a map back to original query identities. Prove preservation of each answer and linear or soft-linear construction/scanning bounds. Root-reachable vertices may be reindexed with the root first.

The legacy `FailureDAG` has edges to decreasing indices. Translate indices to the chosen convention; **do not reverse the actual arcs**. Normalization returns their settled answers under original IDs; it must continue after a positive direct answer. Its unresolved-index map is injective and disjoint from settled entries.

Dominator semantics is: `u` dominates `v` iff every root-to-`v` path contains `u`, for initially reachable `v`. After failure of `u`, the unreachable set is the dominator subtree of `u`. Implement tree parent construction, LCA and subtree indexing; merely assuming a correct tree does not supply construction complexity. Comparable two-failure pairs reduce to the earlier dominator; incomparable pairs proceed to the main kernel.

Owners: PB1.2–PB1.5. Consumer interfaces expose actual normalized arrays, indices and cost theorems, not only existence of an equivalent graph.

## I2. Residual kernel at a proposed anchor

Input: normalized graph and proposed anchor `v`. Split vertices into capacity gates, protecting `Dom(v)` with capacity three and giving other gates capacity one; transit and terminal arcs have the published capacity three. Treat original arc identity, reverse arcs and parallel arcs explicitly.

At most three augmenting searches yield either the flow-three certificate or a maximum flow of value two with its residual graph and two flow paths. The protected vertices can belong to both paths; unprotected unit gates cannot. Prove the precise case classification consumed by the caller rather than postulating that a successful branch always has two paths.

For a two-flow kernel and the two path orders, let `λ_j(x)` be the minimum position on path `j` that reaches residual vertex `x`, or an infinity sentinel. Reverse path arcs make the reaching positions a suffix. The residual graph can have cycles, so build SCCs or another proved general-digraph propagation algorithm. Original DAG acyclicity is insufficient here.

Two exported facts are needed:

1. The four strict rank inequalities of paper equation (3.2b) recognize a **proper** cut at `v`, with the two failures oriented onto their separate paths.
2. For that cut with positions `α,β` and **any original target** `t`, paper equation (3.1e) gives
   \[
   Reach_{D-F}(r,t)\iff \alpha\ge\lambda_1(t^+)\ \lor\ \beta\ge\lambda_2(t^+).
   \]

The second fact is not restricted to ancestors of `v`. Infinity, deleted targets, protected nodes and root cases must use the same representation as the executable query routine.

Construction target: `Õ(V+E)` time and workspace for one kernel, including network discovery, augmentations, SCCs, labels, indices and their initialization. Once constructed, proper-cut and target tests have the explicitly proved constant/logarithmic costs claimed by their data representation. The final selected root cannot retain an assumption granting either fact or this cost.

Owners: PB2.1–PB2.7. Reviewer: resources. Consumers: Resolve and the optional common-anchor algorithm.

## I3. Scheduler state and retirement

State includes reverse-topological position, active-query flags, immutable retained light sets, current timestamp arrays, bounded transient buffers and at most one live residual kernel. A retained list has length less than the effective threshold. Once stored, it remains a historical list even if its queries later become inactive.

The key invariant describes surviving current-vertex-to-original-target suffixes for active unresolved queries. Pulling a child's list can encounter stale or duplicate labels: filter them after charging the pull. A proposed heavy vertex must resolve both its buffered candidates and later streamed candidates, using the same kernel.

A negative query may be retired only after testing **all its original targets** under the queried failure pair. A positive target records YES and retires that query, while the batch continues. Root arrivals are handled the same way. Every still-active query at termination must be proved negative. A query's presence at a vertex is not enough to pronounce it false, and testing only the targets that propagated to the anchor is insufficient.

Export: concrete state-machine termination and `∀ i, result[i]=true ↔ Success(I,i)`, initially under named kernel interface hypotheses. PB4.5 composes the verified kernel and removes those hypotheses. The full result cannot call a whole-query oracle whose correctness already assumes the required batch computation.

Owner: PB3.1–PB3.4 / scheduler.

## I4. Actual work, words and asymptotic constants

The program or program family is fixed **before individual input selection**. The intended form is `∃ P,C,k, ∀ valid I,τ, ...` (or a fixed coded `P`), not `∀ I, ∃ P_I, ...`. It is deterministic and uses the published combinatorial primitives.

Freeze an explicit instruction/primitive model and prove refinement of the concrete implementation to its executions. Every primitive must have a proved implementation or a visible still-open dependency. A type containing arbitrary `answer`, `ticks` and `peakWords` fields is not such a model. Measured Python timings do not prove the RAM theorem.

Use the effective threshold `τ_eff=min(τ,q'+1)`, where `q'` is the residual query count after direct cases. Handle `q'=0` separately. If the cap applies, no threshold kernel is triggered; prove that this recovers the paper's bound for the original `τ`, rather than replacing it with a weaker formula silently. A large binary-encoded threshold must either have its read cost charged or be an algorithm-selection parameter as in the theorem.

A useful explicit bound before asymptotic cleanup is

\[
 ticks\le C\bigl[S+E\tau_{eff}+(V+E)
 \lfloor q'/\tau_{eff}\rfloor\bigr]\ell^k,
 \quad \ell=\lceil\log_2(S+2)\rceil,
\]

with uniform constants; sharpen the capped branch to derive the published expression. Peak live words must satisfy `C(S+V τ_eff) ℓ^k`. Prove addresses, counters, timestamps, rank sentinels and loop indices fit the permitted logarithmic word width. Cumulative allocations are not peak space.

Required amortization exports:

- at most `floor(q'/τ_eff)` kernels in total; every one completes and retires distinct positive or negative queries;
- all list pulls, including stale and duplicate entries, bounded by `E(τ_eff-1)`;
- input target seeding plus a constant number of full original-target tests per retired query, hence `O(M)` aggregate target work;
- at most one live kernel and bounded transient state; all historical payloads, the full answer vector and original-ID maps are counted.

Owners: PB4.1–PB4.6 / resources. The end-to-end join at PB4.5 is the first headline consumer.

## I5. Exact sharing

Represent each retained nonempty set by an immutable sorted tuple. A deterministic balanced dictionary interns equal tuples and returns a stable handle. Prove exact equality tests, insertion/lookup work including tuple comparisons, reference stability and simulation of the original scheduler.

`Λ` is the sum of tuple lengths over **all distinct tuples retained during the run**, not just active sets and not just pairwise differences. One handle per retained vertex and the dictionary/node overhead are absorbed by `S+Λ`. Prove `Λ<=V(τ_eff-1)`. Do not assume arbitrary partially overlapping tuples can be stored by a cheap interval or shared-array representation.

Owners: PB5.1–PB5.3 / sharing, resource review. Consumer: Proposition 3.3.

## I6. Separate extension interfaces

- **Common anchor (3.1):** recognize absence/existence of a proper anchor and charge discovery; rejection does not answer the unresolved queries. Dead-region intersections, seed replacement and protected proper cuts need their own correctness proof.
- **Localization (4.2–4.3):** independent trees share exactly the dominators of each root path. Fixed vertices outside the two subtree union retain dominators after one deletion; dead vertices are their intersection; recompute only the symmetric difference. Lemma 4.2 can be conditional on valid trees; Theorem 4.3 must also construct them and charge reporting, LCAs and original edges.
- **Streamed chains (4.5):** supplied reachability chains need not be edge paths. Validate them while computing one column at a time; retain at most one relevant target per chain, with `R_*<=min(M,q_b p)`. Charge `p(V+E)`, `pR_*` and `q_b p log²(V+2)`. Do not store the full `pV` label table or assume small `p`.
- **Reductions:** output equivalence, representation size, executable construction cost, source-domain conditions, algorithm-model closure and hypothesis implication are distinct exports. Known complexity conjectures may be explicit hypotheses; a cited proved graph theorem is not thereby a Lean theorem.
- **Application:** compose Proposition 2.2 with exact pinned Paper A interfaces. Supplied circuit roles, native `N=Θ(G)`, primary-input realization and witness output size must be matched explicitly.

- **Constructed width (4.7):** minimum chain-partition width is not minimum disjoint edge-path count. Greedy maximum-uncovered paths do not require kappa as input; assigned subsequences occupy linear space. Charge discovery, chain validation and every streamed graph/target pass.
- **Weighted cover (4.8):** costs refer to the fixed B,R,D trees. Prove weight discovery, dual feasibility, selected-vertex tightness and factor two, including zero weights and duplicate pair incidences. The algorithm does not compute OPT_c or optimize the tree choice.

## Nonvacuity and rejection controls

Each eventual selected root needs both valid positive examples and deliberate invalid candidates. Controls should reject a constant vector or an OR-only solver, an oracle with zero cost, omission of a late target, a residual-DAG assumption, and a program chosen after inspecting the input. Boundary examples and finite differential tests help expose contract errors but do not replace universal proofs.
