# Offline Threshold Algorithms for Two-Failure Reachability

Idris Ali Shaik\
Independent researcher (unaffiliated)

**Technical companion, 18 November 2026.**

Given a rooted directed acyclic graph and a list of failure queries, a backward scan can group queries at a vertex whose disconnection they test together. This note gives the common-anchor recognition algorithm, the complete threshold proof, and the space bound for interning identical query sets. The accompanying article *Near-Linear Preprocessing for Reachability After Two Vertex Failures in Directed Acyclic Graphs* constructs a static index that also handles queries supplied later.

## Graph and query conventions

The input is a DAG with a fixed source, `V` vertices, `E` arcs and `q_b` listed queries. Query `i` deletes a set `F_i` of at most two vertices. It answers YES if any vertex in its original target list `T_i` is reachable after deletion. A path of length zero is permitted. Deleting the source, or giving an empty target list, produces NO. Write `M=sum_i |T_i|` and `S=V+E+q_b+M`. Costs are for a deterministic word RAM with logarithmic word size in the explicit input. A vertex dominates another if every path to the latter from the source contains the former. On the initially reachable graph, the vertices lost under one failure are its descendants in the dominator tree, including itself. The notation `Õ` suppresses polylogarithmic factors.

## 3.1. A Shared Cut and Arbitrary Targets

A common cut permits sharing across different failure pairs and different
listed targets. The relevant condition concerns the failures: there must
be a nonempty vertex set `P` that every pair disconnects, although neither
member of any pair disconnects all of `P` alone. Call `P` a *proper common
anchor*. It may be disjoint from all target lists. The algorithm below
finds such an anchor when one exists; it does not require a supplied one.

Residual closure and path-rank labels are classical minimum-cut tools
[PQ79, Theorem I; ACPP+26, Appendix A.2]. We specialize them to two vertex
failures and charge the discovery of the common anchor as well as the
arbitrary-target queries. Priority for this combined batch formulation
and its sorted intersection computation is unestablished.

<a id="statement-3-1"></a>

**Theorem 3.1 (recognized common-anchor batches).** Let `D` be a rooted
DAG whose `V` retained vertices are initially reachable, with `E` arcs.
Given a nonempty list of `q_b` pairs of distinct nonroot failures, one can
decide whether they have a proper common anchor in
`O((V+E)log(V+2)+q_b log(q_b+2))` time. If they do, every listed target
membership, and hence every query answer, can be computed in total time
\[
 O((V+E)\log(V+2)+q_b\log(q_b+2)+M),
\]
using `O(S+V log(V+2))` working words. The bound includes discovery, all
graph passes and the `M` target incidences. No depth or chain-partition
bound is required. Rejection certifies the absence of a proper common
anchor; it gives no answer to the unresolved two-failure queries.

*Proof.* Number vertices topologically, and construct the ordinary
dominator tree `T` with ancestry and LCA operations. For a nonroot seed
set `B`, let
\[
 Z(B)=V(D)\setminus\operatorname{Reach}_{D-B}(r).
\]
In particular, failed vertices belong to `Z(B)`. For sets `B,C` of at
most two vertices put
\[
 E_{B,C}=(B\cap Z(C))\cup(C\cap Z(B)).
\]
Then
\[
 Z(B)\cap Z(C)=Z(E_{B,C}).                     \tag{3.1a}
\]
Indeed, the intersection contains `E_{B,C}` and is closed under the
rule that a nonroot vertex with all predecessors dead is dead. For the
reverse inclusion, process vertices topologically. A vertex in the
intersection either is in `E_{B,C}`, or belongs to neither seed set;
in the latter case all its predecessors are in the intersection.
The root is in neither dead region, so no empty-predecessor exception
arises. This proves (3.1a).

The intersection has a seed set of size at most two. If `B` is contained
in `Z(C)`, retain `B`; every path to `Z(B)` meets `B`, so `Z(B)` is
contained in `Z(C)`. The symmetric case retains `C`. Otherwise both
intersections defining `E_{B,C}` have size at most one, so retain their
union.

**Discovering the intersection.** Sort the pairs `(a,b)`, with `a<b`, by
increasing `b`. Maintain a set `A` of at most two seeds and the Boolean
array for `Z(A)`, equal to the intersection of processed dead regions.
Every seed was selected from a processed pair. Hence, for the next
pair `(a,b)`, each `x` in `A` satisfies `x<=b`, and
\[
 x\in Z(\{a,b\})\quad\Longleftrightarrow\quad
 x=b\ \text{or}\ a\text{ dominates }x.        \tag{3.1b}
\]
For `x<b`, the later failure `b` cannot affect a path to `x` in a DAG.
Thus `I=A intersect Z({a,b})` is found by at most two ordinary ancestry
tests; `J={a,b} intersect Z(A)` uses two array accesses. If `I=A`, retain
`A`. Otherwise replace it by `{a,b}` when `J={a,b}`, and by `I union J`
in the remaining case. Equation (3.1a) proves the updated seed invariant.

Initialize the dead array for the first pair in one topological pass,
mark that pair as the seed set, and for each vertex store the number
of predecessors outside the dead region. On replacement of `A` by
`A'`, the region can only shrink and every new seed is already in
the old region. Mark all seeds in `A'` before processing releases,
retain flags for `A intersect A'`, and clear only those in
`A minus A'`. Release a removed seed if it has an outside
predecessor. Whenever a
vertex is released, scan its outgoing arcs, increment the corresponding
outside-predecessor counts, and release any dead nonseed whose count
becomes positive. Mark vertices at enqueue time. A dead nonseed can
become reachable only after a predecessor does, so topological induction
proves completeness. Each vertex is released at most once over the
entire batch, and each outgoing arc is then scanned once. Seed changes
cost constant time per pair. Initialization and all releases cost
`O(V+E+q_b)`, in addition to sorting and ordinary dominator preprocessing.

**Recognizing an anchor.** At the end,
`Z(A)=intersection_i Z(F_i)`. If `A` is empty, no anchor exists.
Otherwise put `d=LCA_T(A)`. Accept precisely when
\[
 F_i\cap\operatorname{Anc}_T(d)=\varnothing
 \quad\text{for every }i.                    \tag{3.1c}
\]
If (3.1c) holds, `A` itself is a proper common anchor. Each pair kills all
of `A`, and a single vertex kills all of `A` exactly when it dominates
`d`. Conversely any proper common anchor `P` is contained in `Z(A)`.
Every ancestor of `d` dominates all of `A`, and therefore every vertex
of `Z(A)`, since every root path to that vertex meets `A`. A pair
containing such an ancestor would kill all of `P` by that failure alone.
This proves necessity. The additional recognition work is `O(q_b)`.

**Building one residual representation.** For an accepted batch, add a
protected sink `sigma` with arcs from `A`. Split every vertex `v` into
`v^-` and `v^+`. Give its gate arc capacity one, except for ancestors of
`d`, whose gates have capacity three; transit and sink arcs also have
capacity three. Use `r^+` as source. There is no capacity-one cut, because
all single-vertex separators of `A` have been protected. Every listed
pair is a capacity-two cut by (3.1c), so the maximum flow is exactly two.
At most three unit augmenting searches find it in `O(V+E)` work.
Decompose the flow into two paths `P_1,P_2`. Every unprotected gate on
these paths belongs to exactly one of them.

Let `R` be the residual graph. Number the split vertices along each
flow path and define
\[
 \lambda_j(x)=\min\{\ell:P_j[\ell]\leadsto_R x\},
 \qquad j\in\{1,2\},
\]
with value infinity for an empty set. Residual reverse arcs run
backwards along each flow path, so
\[
 P_j[k]\leadsto_R x\quad\Longleftrightarrow\quad
 k\ge\lambda_j(x).                            \tag{3.1d}
\]
Compute the SCCs of `R`, initialize each component with its minimum
position on each path, and propagate the two minima forwards through
the condensation DAG. This computes all labels in `O(V+E)` time and
space. It is the usual path-rank representation of residual reachability,
with two paths rather than a variable number of paths.

**Answering arbitrary targets.** For a listed pair `F={a,b}`, orient its
gates so that `a` lies on `P_1` and `b` on `P_2`, and put
`alpha=pos_{P_1}(a^-)`, `beta=pos_{P_2}(b^-)`. Every flow path crosses the
minimum cut exactly once, so this orientation exists. For every target
`t`, including one outside the ancestor cone of `A`,
\[
 r\leadsto_{D-F}t\quad\Longleftrightarrow\quad
 \alpha\ge\lambda_1(t^+)\ \text{or}\
 \beta\ge\lambda_2(t^+).                      \tag{3.1e}
\]
To prove this, let `U_F` be the source-reachable set in the split network
with the two failed gates removed. Its outgoing cut has capacity two,
so `U_F` is residual-closed [PQ79]. Both cut tails are in `U_F`, by their
flow-path prefixes. Their residual closures are therefore contained in
`U_F`.

Conversely, take a surviving root-to-`t` path. It cannot visit a vertex
strictly beyond a failed gate on its flow path: following that flow
path's suffix would reach `sigma` without either failure, contradicting
that `F` is a cut. Every saturated unit gate traversed by the surviving
path therefore precedes the failed gate on its flow path. The head of
the last such gate is residual-reachable backwards from the corresponding
cut tail; the rest of the surviving path has positive forward residual
capacity. If there is no such gate, the path starts at the source, which
is residual-reachable backwards from either cut tail. Transit and
protected arcs retain forward capacity because their capacity is three
and the total flow is two. This proves that `t^+` belongs to one of the
two residual closures. Equation (3.1d) gives (3.1e).

Ordinary dominators by topological predecessor LCAs and binary lifting
cost `O((V+E)log(V+2))` time and `O(V log(V+2))` words. Sorting costs
`O(q_b log(q_b+2))`; intersection discovery, flow, decomposition, SCCs and
label propagation each use a constant number of graph passes. Each
listed target now needs two comparisons, and grouping its Boolean
answer under the original query label costs `O(q_b+M)`. Input normalization,
failed roots, initially unreachable targets, and zero or single failures
are processed in `O(S)` using the ordinary dominator tree. These charges
give the stated total bounds. ∎

The anchor condition can hold across crossing query groups. Take two
independent root chains `x_1,...,x_k` and `y_1,...,y_k`, and a sink `t_i`
with parents `x_i,y_{k+1-i}` for each `i`. The pairs
`F_i={x_i,y_{k+1-i}}` have the proper common anchor `{x_k,y_k}`. No listed
`t_i` lies in their common dead region when `k>=2`, yet one residual
representation answers all their target queries. The running-intersection
procedure avoids enumerating the quadratically many distinct regions
`Z(F_i) intersect Z(F_j)`.

The theorem does not imply that arbitrary batches can be divided into
such groups with near-linear graph work. Whole-graph reconstruction per
group can be quadratic even when `S=Theta(V)`: add arcs `r->v_j` and
`v_j->v_{j+1}`, and a sink `t_j` with parents `v_j,v_{j+1}`. The pairs
`{v_j,v_{j+1}}` have dead regions `{v_j,v_{j+1},t_j}`, and no two distinct
pairs share a proper common anchor. Direct inspection of the target
parents solves this example in linear time. It is an obstruction to
that reconstruction schedule, not a lower bound for the Boolean batch
problem. The threshold schedule below bounds these repeated scans by
charging completed kernels to disjoint sets of resolved queries.

## 3.2. The Threshold Algorithm

The common-anchor kernel also gives a time-space tradeoff without a
common-anchor promise. Propagate query labels backwards from their
targets and retain a short list at each vertex. When a list reaches a
threshold, build one residual kernel there and use it to settle whole
queries. Recording both positive and negative answers permits continued
processing, while every completed kernel pays for itself through a
specified number of retirements.

<a id="statement-3-2"></a>

**Theorem 3.2 (threshold tradeoff for all-query batches).** Let `D` be a
rooted DAG with `V` vertices and `E` arcs. The input lists `q_b` queries
`(F_i,T_i)`, where `|F_i|<=2`, and `M=sum_i |T_i|` target incidences.
Put `S=V+E+q_b+M`. For every integer `tau>=1`, computing every query's
Boolean answer takes
\[
 \widetilde O\bigl(S+E\tau+(V+E)q_b/\tau\bigr)
 \quad\text{time},\qquad
 \widetilde O(S+V\tau)\quad\text{working words}.       \tag{3.2a}
\]
The algorithm is deterministic and combinatorial. Its output has one
entry per original query, indicating whether any of that query's targets
remains reachable. No depth, chain-partition or interval promise is required.
The bound includes kernel discovery and construction, all edge scans,
and aggregation over the original target lists. Taking the OR also
solves the existential version within these bounds.

*Proof.* Remove initially unreachable vertices, their target occurrences,
and their occurrences in failure sets. Record NO for queries failing
the root or having no remaining targets. A query with no failures and
a remaining target is YES. Ordinary dominators decide single failures.
If one failure dominates the other, removing the latter additionally
removes no root-reachable vertex, so this case reduces to a single
failure. Record every direct answer under its original query index and
continue. These operations cost `Õ(S)`, including topological ordering,
ordinary dominators and all listed targets.

There remain `q'<=q_b` unresolved queries with two nonroot,
dominator-incomparable failures, in an initially root-reachable DAG.
Retain their original indices. If `q'=0`, return the recorded vector.
We may use `min{tau,q'+1}` as the effective threshold, denoted `tau`
until the final bound. If this cap changes the supplied value, no vertex
can trigger a kernel, and the resulting `Õ(S+E q')` work is at most
`Õ(S+E tau)` for the supplied threshold.

**Testing a proposed anchor.** Fix a nonroot vertex `v`. Use the split
network of Theorem 3.1 with anchor `{v}`: protect every gate in
`Dom(v)` by capacity three, give other gates capacity one, and give
transit and sink arcs capacity three. There is no capacity-one cut,
since every single-vertex separator of `v` was protected. Three unit
augmenting searches either find a flow of value three or certify a
maximum flow of value two, in `O(V+E)` work. In the first case any
failure pair disjoint from `Dom(v)` leaves `v` reachable.

In the second case compute the two paths and residual labels
`lambda_1,lambda_2` of (3.1d), in `O(V+E)` time and space. A candidate
pair `F={a,b}` disjoint from `Dom(v)` can cut `v` only if its gates lie
on different flow paths. Otherwise one path survives. Orient such a
pair with `a` on `P_1` and `b` on `P_2`, and put
`alpha=pos_{P_1}(a^-)`, `beta=pos_{P_2}(b^-)`. It is a cut precisely when
\[
 \begin{split}
 \alpha&<\lambda_1(a^+),\qquad \beta<\lambda_2(a^+),\\
 \alpha&<\lambda_1(b^+),\qquad \beta<\lambda_2(b^+).
 \end{split}                                         \tag{3.2b}
\]
For necessity, the source-reachable side after deleting a proper pair
has outgoing capacity two. A maximum flow saturates those outgoing
arcs and has no flow entering that side. The side is residual-closed,
contains both cut tails and excludes both heads, proving (3.2b).

For sufficiency, let `W` be the union of the residual closures of the
two cut tails. Reverse path arcs put the source and every path position
before each tail in `W`. Under (3.2b), neither head is in `W`, and no
path position after a failed gate can be in `W`: reversing along that
path would reach its head. In particular the sink is outside `W`.
An original arc leaving `W` must have zero forward residual capacity.
Transit and protected arcs retain forward capacity because the flow
has value two. Every other saturated arc is a unit gate on a flow
path. A gate before a failed gate has its head in `W`; a gate after it
has its tail outside `W`. Thus the only possible outgoing gates are
the two failed gates. Removing them separates the source from `v`.
This proves the test. For a proper cut, equation (3.1e) then answers
any original target using two comparisons, whether or not that target
lies below or above `v`.

**Reverse propagation.** Keep an activity bit for each unresolved query.
Process vertices in reverse topological order. An active label `i` at
`w` certifies a suffix from `w` to an original target in `T_i` avoiding
`F_i`. At `v`, stream target incidences at `v` and the stored lists of
its outgoing neighbors. Timestamp marks deduplicate labels. Discard
inactive labels and labels for which a failure dominates `v`. At the
root, record YES and deactivate each remaining label. At any other
vertex, retain a list if fewer than `tau` distinct active candidates
survive.

When the `tau`-th candidate arrives, construct the kernel at `v` once.
Resolve the buffered candidates and every later streamed candidate with
that kernel. A value-three flow, or a pair failing (3.2b), gives a
surviving prefix to `v`; the certified suffix proves that query YES.
For a proper cut, inspect the query's **entire original target list**
using (3.1e), with initially unreachable targets already rejected during
normalization. Answer YES if a target survives, and NO otherwise.
Record either answer and deactivate the query permanently. After the
kernel completes, store an empty list at `v` and reuse its workspace.
Later candidates are resolved as they arrive; no unbounded bucket is
accumulated. At the end, record NO for every still-active query.

A kernel retires at least `tau` distinct previously active queries,
whether positive or negative. These retired sets are disjoint, so the
number of kernels is at most `floor(q'/tau)`. There is no additional
kernel terminated by a positive answer, since the computation continues.
No query is resolved by two kernels.

**Correctness.** Target seeding supplies the suffix invariant. Pulling a
child label extends it across an original edge; a failed current vertex
is discarded by reflexive domination. Discarding a label dominated by a
failure is safe because no surviving root prefix can reach that vertex.
Deduplication removes only a repeated occurrence of the same condition.
Retiring a different query changes no path fact about an active query.

Every recorded positive answer joins a surviving prefix and suffix or
checks an original target directly. A kernel records NO only after all
original targets fail, so every such negative answer is correct. The
direct normalization answers were established separately.

Suppose a successful query were still active at the end. Follow one of
its surviving root-to-target paths backwards. No failure dominates a
vertex of that path. At every light vertex its active label propagates
to the preceding vertex. At a heavy vertex the kernel would find a
surviving target and retire it positively. If none intervenes, its label
reaches the root and is answered YES there. Both alternatives contradict
its remaining active. Thus the final NO assignments are correct, and
the recorded vector gives every original answer.

**Total cost.** Every stored list has fewer than `tau` entries, including
entries that later become inactive. All edge-induced candidate
examinations, including duplicates and stale positive or negative labels,
total at most `E(tau-1)`. Base adjacency scans cost `O(V+E)` and target
seeding costs `O(M)`. A query enters a kernel's resolver at most once.
If its original target list is inspected, that scan retires it with a
positive or negative answer. All kernel target aggregation therefore
costs `O(M)`, in addition to the initial input and seeding passes.

Each of at most `floor(q'/tau)` kernels costs `O(V+E)`, including failed
augmenting searches, path decomposition, residual construction, SCCs and
label propagation. Candidate tests are constant-time after preprocessing.
Stored lists occupy at most `V(tau-1)` words. The graph, targets,
activity flags, timestamps, dominator structure and one reusable kernel
use `Õ(S)` other words. Original-index maps and the answer vector use
`O(q_b)` words, included in `S`. If the effective-threshold cap changed
the supplied value, there are no kernels and the earlier capped bound
applies. Otherwise these charges prove (3.2a). ∎

After normalization, `Resolve(i,K_v)` returns the exact query answer:
a surviving prefix to `v` supplies YES through the certified suffix;
a proper cut requires the complete original target-list test.

```
Record all direct normalization answers under their original indices.
Set Active[i] = true for every unresolved query; set List[v] = empty.
For v in reverse topological order:
    Buffer = empty; Heavy = false; start a new deduplication timestamp.
    Stream each ID i from targets at v and outgoing-neighbor lists:
        Skip an inactive ID or an ID already seen at this vertex.
        Mark the ID seen; skip it if one of its failures dominates v.
        If v is the root:
            Record answer[i] = YES; set Active[i] = false; continue.
        If Heavy:
            Record answer[i] = Resolve(i, K_v); set Active[i] = false.
        Otherwise:
            Append i to Buffer.
            If Buffer has tau IDs:
                Build K_v; set Heavy = true.
                For each j in Buffer:
                    Record answer[j] = Resolve(j, K_v); set Active[j] = false.
                Clear Buffer.
    Set List[v] = empty if Heavy, and otherwise retain Buffer unchanged.
Record NO for every still-active query.
Return the answer vector in original query order.
```

Historical lists are not rewritten when queries become inactive. Later
edge scans filter stale IDs using `Active`; this is why the proof counts
historical entries rather than only live labels. The output records a
Boolean per target set, not every individual target membership or a
reusable oracle for future queries.

For a nonempty batch the square-root threshold yields `Õ(S+(V+E)sqrt(q_b))` time and `Õ(S+V sqrt(q_b))` words. A logarithmic threshold yields near-linear workspace. The construction answers an offline list of queries during its backward scan.

## 3.3. Exact Sharing and Its Space Cost

Identical stored sets can share one immutable array. The following
bound states exactly when that standard representation saves space.

<a id="statement-3-3"></a>

**Proposition 3.3 (exact sharing of historical query sets).** In the
algorithm of Theorem 3.2, sort each retained light set and store equal
sets only once in a deterministic balanced dictionary. Let `Lambda`
be the sum of the cardinalities of all distinct nonempty sets retained
during that run. The time bound (3.2a) is preserved, with working space
`Õ(S+Lambda)`. Universally, `Lambda<=V(tau-1)`; a near-linear bound on
`Lambda` is not asserted.

*Proof.* At each light vertex, sort the fewer than `tau` retained query
IDs and look up their immutable tuple in a balanced search tree, ordered
by length and lexicographically. Compare actual IDs, without a
fingerprint-equality assumption. Store a pointer to the existing tuple
when present, and insert it otherwise. The stored tuple is the set at
that vertex's processing time. Later deactivation leaves it unchanged;
each parent still applies its own activity and domination filters.
Thus equality sharing preserves the suffix invariant and all retirement
rules, even when different parents use different filters.

There are at most `V` dictionary operations. Sorting costs
`O(tau log(tau+1))` per operation, and a dictionary search uses
`O(log(V+1))` comparisons, each of cost `O(tau)`. Their total cost is
`O(V tau(log(tau+1)+log(V+1)))`. We may cap the effective threshold at
`q_b+1`. In an initially reachable nontrivial graph `E>=V-1`, so this
work fits `Õ(S+E tau)`. The one-vertex case is decided in normalization.
Edge pulls still examine at most `E(tau-1)` entries; all other charges
are those of Theorem 3.2. Dictionary nodes and per-vertex pointers use
`O(V)` words, distinct tuples use `Lambda` words, and temporary buffers
use `O(min(q_b,tau))` words. Keeping every distinct tuple for the run
therefore gives the stated bound, without requiring garbage collection. ∎

Exact sharing helps repeated-set families. The static oracle in the accompanying article answers the batch with linear working space.

## References

- [ACPP+26] M. Ahi, K. Choudhary, S. Pande, Pushpraj, L. Saggi. Maximum-flow and minimum-cut sensitivity oracles for directed graphs. ITCS 2026. [Published paper](https://doi.org/10.4230/LIPIcs.ITCS.2026.5); [author version, Corollary 1.6 and Section 8](https://arxiv.org/html/2512.00153v1).
- [PQ79] J.-C. Picard, M. Queyranne. On the structure of all minimum cuts in a network and applications. Technical report EP-R-79-15, École Polytechnique de Montréal, 1979. [Institutional full text](https://publications.polymtl.ca/5993/1/EP-R-79-15_Picard.pdf), Theorem I.
