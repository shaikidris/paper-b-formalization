# Offline Reachability in Directed Acyclic Graphs under Vertex Failures

Idris Ali Shaik
Independent researcher (unaffiliated)
shaikidris@apache.org

**Version 1.1 draft, 2026-11-12.**

## Abstract

We study offline reachability in a directed acyclic graph: a common source and a list of queries are supplied, each pairing failed vertices with a target set, and we compute one Boolean answer per query. For at most two failures, let `V`, `E`, `q_b` and `M` count vertices, arcs, queries and target incidences, and put `S=V+E+q_b+M`. For every integer `tau>=1`, a deterministic combinatorial algorithm uses `Õ(S+E tau+(V+E)q_b/tau)` total time and `Õ(S+V tau)` working words, including discovery, edge scans and target aggregation. It propagates query labels backwards and charges residual-cut constructions to whole-query retirement. The square-root threshold gives `Õ(V^(3/2))` time on sparse linear-size batches. Exact sharing of identical historical sets preserves the time bound, but need not give near-linear space. Structural algorithms attain near-linear time and space for polylogarithmic depth or polylogarithmic reachability width, with the required chain partition constructed as part of the algorithm. Weighted cover selection also adapts the localized bound to the least deletion-region cost for fixed independent trees. A linear guarded-DAG representation connects the existential version to Boolean detection; larger-multiplicity reductions give conditional bounds under named triangle, clique and cycle hypotheses. Near-linear time on arbitrary two-failure batches, and near-linear space at the square-root-threshold time, remain open. Here `Õ` suppresses polylogarithmic factors.

## 1. Introduction

Suppose a directed acyclic graph has one source and a list of queries,
each consisting of failed vertices and target vertices. For each query,
does at least one target remain reachable? We compute
one Boolean answer per listed query. Running a search for every failure
set gives these answers, but pays repeatedly for the same graph. Our
algorithm shares work across queries by resolving and retiring them in
groups. Taking the OR of the answer vector also solves the existential
version used in our reductions.

Our main result is a deterministic combinatorial time–space tradeoff for
all listed queries with at most two failures each (Theorem 3.2). With `V` vertices, `E` arcs,
`q_b` queries, `M` target incidences and `S=V+E+q_b+M`, it gives
`Õ(S+E tau+(V+E)q_b/tau)` total time and `Õ(S+V tau)` working words for
every integer `tau>=1`. Here `Õ` hides polylogarithmic factors. For a
nonempty batch, taking `tau=ceil(sqrt(q_b))` gives
`Õ(S+(V+E)sqrt(q_b))` time. This is `Õ(V^(3/2))` on sparse batches with
linearly many queries and target incidences. The workspace at this
threshold can also be superlinear.

The proof has two steps. First, a residual network for a two-vertex cut
answers reachability at arbitrary original targets, even outside the
chosen cut's ancestor cone (Theorem 3.1). Second, we propagate query
labels backwards from their targets. At a vertex that receives many
active labels, we construct one residual network and resolve those
queries completely. A completed construction retires whole queries,
whether their answers are positive or negative, including their original
target lists. Thus different constructions
charge disjoint sets of queries, while short stored lists bound the
remaining edge scans. Proposition 3.3 quantifies the space saved when
identical historical lists share one immutable array.

All failure sets and target lists are supplied before the computation;
the result is a vector of target-set answers, rather than an online
oracle for future queries. The direct dual-failure oracle route of
[Cho16; Cho17, Theorem 3.2] takes `O(VE)` preprocessing and constant time
per target, giving `O(VE+S)` total work here. On sparse balanced inputs
our bound improves that displayed total-time guarantee. The oracle
handles general directed graphs and future individual-target queries,
and retains a smaller completed structure. These comparisons do not
assert dominance over every sensitivity algorithm or establish priority
for the exact batch bound.

Several structural conditions permit near-linear total time with
near-linear space. Theorem 3.1 recognizes a proper common cut anchor
for a whole batch. Theorem 4.3 bounds localized dominator work by DAG
depth, and Theorem 4.5 streams coordinates for a supplied partition into
reachability chains. Corollary 4.7 constructs a small partition when
the reachability width is small; Corollary 4.8 selects a deletion cover
within a factor two of the minimum weighted cost for the chosen
independent trees. These are sufficient conditions, not assumptions of
the threshold theorem.

For larger failure multiplicities, we give conditional bounds via
triangle, clique and directed-cycle reductions. A guarded DAG, whose
terminals carry labels and whose guards forbid labels, provides a linear
translation between labelled paths and offline failure batches
(Proposition 2.2). We track the labels, guards and shared layers in each
reduction. The conditional exclusions distinguish combinatorial from
general word-RAM algorithms and apply only in their stated parameter
regimes; they do not settle the two-failure near-linear-time question.
Known selector capacity bounds explain a limit of these reduction
methods. Guarded Boolean falsification and controller fault detection
provide related applications.

The paper follows the proof dependencies. Section 2 defines the problem
and its guarded representation. Section 3 proves the residual kernel,
threshold bound and space refinement. Section 4 gives the structural
algorithms, and Section 5 groups the conditional bounds by computational
model and failure multiplicity. Section 6 gives applications and the
remaining time and space questions; Section 7 describes the executable
checks. Appendices retain the baseline algorithms, canonical summaries,
weighted selector consequences, shared-output extension and complete
representation examples.

### 1.1. Relation to Reachability and Prior Work

The underlying reachability methods have established precedents.
Sensitivity one is handled by dominators [BGK+08]; the algebraic algorithm
is a fixed-source DAG specialization of the matrix-update method of
van den Brand and Saranurak [BS19]. Our batch contract differs
from an online sensitivity oracle: every query is available initially,
and the algorithm returns a Boolean for each query's target set. The
existential version requests only their OR. The linear reductions in
Proposition 2.2 preserve each individual answer as well as this OR.

Chakraborty, Chatterjee and Choudhary study oracles and preservers for
fixed arbitrary demand pairs and future failures [CCC22]. Here all
queries have one source and the failure/target associations are listed
in advance. Their worst-case arbitrary-pair preserver bounds therefore
do not imply a common-source batch lower bound; sparse constant-failure
single-source preservers already exist [BCR18]. Construction and total
listed-query work remain separate from retained preserver size.

The localized algorithm of Theorem 4.3 refines classical incremental
dominator methods. Ramalingam and Reps already process possibly affected vertices
in topological order, recomputing predecessor LCAs and charging incoming
edges [RR94, Sections 3.1 and 3.2.2]. Georgiadis et al. maintain dominators
and low-high orders in DAGs over a persistent deletion sequence
[GGIKL19]. The linear-time independent-tree construction used here is supplied by
Georgiadis and Tarjan [GT15]. Choudhary's sensitivity analysis already
uses the exclusive portions of independent-tree paths [Cho16, Section 4].
Theorem 4.3 combines these ingredients with output-sensitive enumeration
of two subtree differences, an implicit unchanged dominator tree, and
aggregate accounting for queries that each start from the same original
graph. Its quantitative contribution is the aggregate cost of these regions
and the resulting linear dependence on DAG depth. The qualitative
near-linear bound at polylogarithmic depth also follows from known
replacement-path covering [KP21]; Section 4.1 gives that comparison
alongside dual-failure oracles and fixed-target double dominators.

Last-to-reach chain coordinates and prefix aggregation appear explicitly
in Kuosmanen et al. [KPG+18, Section 3, Observation 1 and Lemma 2];
Kritikakis and Tollis give a modern ordinary-reachability index based on
chain decompositions [KT23, Sections 4.1--4.3]. Italiano, Karczmarz and
Parotsidis combine path reachability, dominators and orthogonal range
reporting for one failure outside a fixed directed path [IKP21,
Theorem 4.1 and Section 6]. Theorem 4.5 combines a cut at the later
failure with these standard types of coordinate and range operations.
Its complete listed-batch bound includes partition validation and
multi-target aggregation; processing one chain at a time avoids retaining
the full coordinate table. Corollary 4.7 composes this algorithm with
the classical greedy overlapping-path cover of [KPG+18, Lemma 1];
Corollary 4.8 uses the standard weighted-cover approximation [BE81].

The canonical summary in Lemma B.1 uses the classical immediate
double-vertex-dominator structure [TD15, Sections 5--6]. Its explicit
all-failure predicate permits replacement of predecessor sets. The
generic batch exponent also follows by applying the local preserver
construction of [BCR18] to sparse topological prefixes; Appendix B
gives the comparison, including construction costs. The shortcut
representation has two incoming arcs rather than the four retained
original arcs supplied by that preserver route. Priority for this
precise formulation is unestablished.

The residual-cut and flow-path labels in Theorems 3.1 and 3.2 use
classical machinery [PQ79; ACPP+26, Appendix A.2]. Theorem 3.2 adds
an amortized schedule for the listed all-query problem: a completed
kernel retires positive and negative queries, including all their original
targets. Its existential projection has the same asymptotic bound.
Exact array interning in Proposition 3.3 is a standard representation
technique; its bound depends on the distinct sets produced. Priority
for these precise combined bounds is unestablished. The stated results
concern total batch work, rather than the space or query time of an
online oracle.

The bounded number of failures associated with one label also appears in
the color-fault model [PP26]. There a failed color removes its entire
color class, and a vertex may carry a constant number of colors; our
explicit queries allow unrestricted overlap, and only listed targets
are tested. Their reachability-preserver size bound does
not supply the total batch-time bound asked for here. The output contract
and construction cost must both be retained in this comparison.

The balanced selector is the static guarded form of the binary-tree
deletion gadget of Abboud and Williams [AW14, Lemma 8.3]. Tuple layers
adapt the clique-to-matched-pairs construction of Dalirrooyfard et al.
[DJVW22, Sections 2.1.1 and 4.1]; their layered cycle construction also
supplies the general word-RAM lower bound. We use the combinatorial
triangle/BMM hypothesis in the form stated by Abboud, Safier, and
Wallheimer [ASW26, Conjecture 1]. The contribution of the reductions here
is their explicit guarded representation, its size and parameter regimes,
and the resulting existential-batch consequences.

The uniform selector capacity bound is the improved anti-isolation
lemma of Hoppenworth, Saranurak, and Wang [HSW25, Lemma 2.3], following the
fault-tolerant reachability preserver of Baswana, Choudhary, and Roditty
[BCR18]. We give a vertex-deletion proof and derive the weighted budget
and total-cost consequences. These are elementary consequences of the
known capacity theorem; their priority is unestablished.

The controller application needs only the exact reachable-set theorem
and the elementary guarded decision rule of [Sha26A, Theorems 4.1 and
5.1]. Section 6.2 states that interface explicitly. The graph algorithms
and reductions preceding it have proofs independent of the controller's
physical construction.

## 2. Problem and Representation

### 2.1. Offline Failure Queries

A *listed failure batch* consists of a DAG `D`, a source `r`, and all
queries `(F_i,T_i)` supplied together. Here `F_i` is a vertex-failure set
and `T_i` is a target-vertex set. Its answer vector has entry
\[
 A_i=[T_i\cap\operatorname{Reach}_{D-F_i}(r)\ne\varnothing].
\]
The *existential offline sensitivity-reachability* problem (OSR) asks
only for `OR_i A_i`. The algorithms of Sections 3 and 4 compute every
`A_i`; Proposition 2.2 and the conditional reductions use the existential
version. A query answer aggregates its target set and does not report
every individual target membership.

Reachability includes a length-zero path. The source or targets may fail;
if the source fails, that query answers NO. The size and sensitivity are
\[
S=|V(D)|+|E(D)|+\sum_i(|F_i|+|T_i|)+\text{number of queries},
\qquad \mu=\max_i|F_i|.
\]
For an empty family set `mu=0`; its answer vector is empty and its
existential answer is NO. An online oracle answers later queries after
preprocessing. We charge preprocessing in every comparison of total
batch time.

Throughout the algorithmic results the graph is a DAG. A topological
order and initial source reachability can be computed in linear time.
A vertex `a` *dominates* `v` if every source-to-`v` path contains `a`;
a vertex dominates itself. Dominators of initially reachable vertices
form a rooted tree. For any rooted tree `T`, write `Anc_T(v)` for the
ancestors of `v` and `T(v)` for the subtree rooted at `v`, both including
`v`. Write `Dom_D(v)` for the vertices that dominate `v` in `D`, or
`Dom(v)` when the graph is fixed. Thus `Dom_D(v)=Anc_T(v)` when `T`
is its dominator tree. Ancestry tests decide single-vertex failures.
We use ordinary dominator and lowest-common-ancestor preprocessing, with
its costs included in every total bound. Conditional word-RAM bounds use
logarithmic word size; the precise deterministic or randomized hypothesis
is stated beside each reduction. A combinatorial hypothesis excludes
fast algebraic matrix multiplication in the convention of its source.

### 2.2. Guarded DAGs

A *guarded DAG* has a declared label set `[n]={1,...,n}` and four kinds of
vertices: a zero vertex; a terminal labelled `i`, denoted `h_i`; an OR
vertex with a list of children; and a guard vertex with one child and a
set `B` of labels. Edges point from a vertex to its children. Terminals
and zero vertices are sinks. Different terminals may have the same
label, and internal subgraphs may be shared. An empty OR is zero. The
equivalent recursive syntax is

```
f ::= 0 | h_i | OR_j f_j | (f AND AND_{j in B} not h_j).
```

For a qualifier set `K subseteq [n]`, a terminal `h_i` is true exactly
when `i in K`. OR vertices take the disjunction of their children, and a
guard vertex is true exactly when its child is true and `B intersect K`
is empty. Thus every guard has one live child. There is no conjunction
of two independently evaluated subexpressions.

Let `V` and `E` be the numbers of stored vertices and child incidences,
and let `H=sum_v |B_v|` count guard memberships. For `q` specified output
roots `r_1,...,r_q`, the *counted incidence size* is

\[
G=n+V+E+H+q.
\]

All declared labels are counted, including unused labels. All stored
vertices and incidences are counted, including unobserved subgraphs.
Thus the padding used in the lower bounds is part of the representation.
Guard lists describe sets: listing one label twice at the same guard
does not create two failures. The input includes a topological order or
one is computed in `O(G)` time. Terminal multiplicities and shared
children are charged through this representation.

Fix a distinguished target label `t`. The required set `Q` is either
empty or `{t}`. Admissible qualifier sets are

\[
\mathcal K_Q=\{K\subseteq[n]:K\ne\varnothing,\ Q\subseteq K\}.
\]

Write `F_k(K)` for the value at root `r_k`, and set `c_k=F_k({t})`.
The *detection query* asks whether some `K in K_Q` and some output `k`
satisfy `F_k(K) != c_k`, and may also request such a witness `K`.
We call the reference values `c_k=0` and `c_k=1` *healthy zero* and
*healthy one*, following the controller application. For one healthy-zero
root, detection will be a reachability question. For a healthy-one root,
it instead asks for an admissible set that falsifies that root. With
several roots, detection is the OR of these separate questions; their
witnesses need not be the same.

For a healthy-zero root, first delete every guard whose set meets `Q`,
together with its incident edges. This is a common deletion independent
of the candidate label. If it deletes the root, every query for that root
fails. In the remaining graph, label `i` forbids precisely those guard
vertices whose sets contain `i`. Its *residual guard multiplicity* `k_i`
is their number, and `mu=max_{i!=t} k_i`, with maximum zero over an empty
candidate set. Its targets are all terminals labelled `i`.

Table 1 summarizes the parameters and their conventions.

| Parameter | Meaning and conventions |
|---|---|
| `G` | Counted size of the supplied guarded representation, including padding |
| `n`, `q` | Declared labels and output roots; both at most `G` |
| `Q` | Either no forced label or the forced target singleton `{t}` |
| `V`, `E` | Stored vertex and child-incidence counts in `G`; residual graph counts where explicitly stated in an algorithm |
| `k_i`, `l_i` | Failure and terminal counts for label `i` after the common deletion |
| `mu` | Maximum `k_i` after the common forced-target deletion |
| `h` | Maximum number of edges on a path in the initially reachable residual DAG |
| `C`, `Sigma(C)` | A query-pair cover and its cost, defined with the localized algorithm (Theorem 4.3) |
| `kappa` | Minimum number of reachability chains partitioning the retained DAG (Corollary 4.7) |
| `c(u)`, `OPT_c` | Deletion-region weight and minimum cover weight for fixed independent trees (Corollary 4.8) |
| `p`, `q_b` | Chains in a supplied reachability-chain partition and number of listed failure queries (Section 4.2) |
| `M`, `S` | Listed target incidences and total batch size; for at most two failures per query we use `S=V+E+q_b+M`, equivalent within a constant factor to the full incidence size above |
| `tau` | Threshold for retaining a query list (Section 3.2) |
| `Lambda` | Total cardinality of distinct retained historical sets (Section 3.3) |
| `w` | Bits per machine word; logarithmic for conditional word-RAM bounds |
| `omega` | Exponent of matrix multiplication; `Õ` suppresses polylogarithmic factors and arbitrarily small exponent slack where stated |
| `gamma`, `beta` | Fixed label-to-size and output-to-size exponents, independent of input size |

Table: Parameters and conventions.

### 2.3. Paths and the Linear Equivalence

The following observation supplies both the small witnesses and the
failure-query interpretation. It concerns a path's terminal label; other
labels on a qualifier set can only invalidate guards on that path.

<a id="statement-2-1"></a>

**Lemma 2.1 (a positive terminal and its forbidden vertices).** A guarded
root is true on `K` exactly when some path from that root ends at a
terminal `h_i` with `i in K` and every guard on the path has guard set
disjoint from `K`. If the root is healthy zero and `K in K_Q` makes it
true, then some `i!=t` makes it true on `Q union {i}`. Equivalently, after
the common deletion, an `i`-terminal is reachable while avoiding every
remaining guard containing `i`.

*Proof.* At a true OR vertex choose a true child; at a true guard take
its child. Acyclicity ends this process at a true terminal, since a zero
vertex cannot be true. The encountered guards are all disjoint from `K`.
Conversely, evaluating upwards along any such path proves the root true.
Retaining only `Q` and its terminal label keeps the terminal true and
cannot introduce an active guard. If that terminal label were `t`, the
same path would already make the root true on `{t}`, contrary to its
healthy-zero value. Removing guards meeting `Q` once, and guards
containing `i` for this candidate, states exactly the same path condition. ∎

The path lemma permits an exact translation in both directions. In
particular, the common deletion for a forced target must be performed
before listing label-specific failures, so its cost is paid once.

<a id="statement-2-2"></a>

**Proposition 2.2 (offline sensitivity reachability).** Single-output healthy-zero
detection and OSR reduce to each other in linear time.

1. A guarded DAG of size `G` with `n` labels and one healthy-zero root
   gives an OSR instance
   with `n-1` queries, size `O(G)`, and sensitivity equal to the maximum
   residual guard multiplicity over candidate labels `i!=t`. When `Q={t}`, first remove every guard vertex containing `t` and its incident
   edges. This common deletion is performed once, outside the query lists.
2. An OSR instance of size `S` with `q_b` queries gives a one-output guarded DAG with `q_b+2` labels, size `O(S)`, and guard multiplicity equal to
   the sensitivity. Its required set can be `Q={t}` or empty.

In both directions, query `i` succeeds exactly when the singleton (or
target-plus-singleton) qualifier set of label `i` changes the root value.

*Proof.* **Guarded DAG to OSR.** When `Q={t}`, form the guarded DAG with all
target guards deleted; otherwise retain the DAG. Let `r` be its root.
If the root was deleted, use a fresh isolated source, so every query
fails. For label `i!=t`, let:

- `F_i` be the remaining guard vertices containing `i`;
- `T_i` be the terminals of `i`.

By Lemma 2.1, a healthy-zero output detects exactly when
some label has a root-to-terminal path avoiding these guards.
Scan each remaining guard membership and terminal once to build the query
lists. Thus `sum_i |F_i|` is at most the original guard-incidence count,
and `sum_i |T_i|` is at most the terminal count. Copying the target guards
into every query would instead cost as much as `Theta(nG)` and is
unnecessary.

**OSR to guarded DAG.** Use one label for each query, together with distinct
labels `t,d`, and take `Q={t}` or empty. Give every vertex `v` an OR vertex over its successors.
Add an edge from each target `x` in `T_i` to the shared terminal of label
`i`. If `v` lies in some failure set, put a guard vertex with set
`{i : v in F_i}` above that OR vertex; all incoming edges use this guarded
entry, including the output entry when `v=r`. A path in the guarded DAG that avoids every
guard containing `i` is a path of `D` avoiding `F_i`, followed by one edge
into the terminal of `i`. Neither `t` nor the auxiliary label occurs in any guard or
terminal, so the healthy value is zero. For either choice of `Q`, `{t,i}` or `{i}`
detects exactly when query `i` succeeds. Each failure membership becomes
one guard incidence and each target membership one edge. Build these
inverse incidence lists by scanning the queries once, and process the
vertices in reverse topological order. This takes `O(S)` time and space;
scanning every query for every vertex is unnecessary. ∎

Several healthy-zero roots can first be joined by one OR root, at
`O(q)` additional size. This root is healthy zero and is true on a set
exactly when at least one original root is true on that set, so the
existential detection answer is preserved.

## 3. Two-Failure Batch Algorithms

The main construction uses one cut to answer targets throughout the
graph. We first prove the residual kernel together with an exact
common-anchor recognizer. The threshold algorithm then uses the kernel
at selected vertices without requiring a common anchor for the input
batch. It answers all queries, and its cost is controlled by retiring
both positive and negative queries. The common-anchor
recognizer is a companion result; the threshold proof uses the residual
kernel, not the recognizer. Section 4 gives independent structural
algorithms, and Section 5 gives conditional reductions in other
multiplicity regimes. Neither is an assumption of the threshold theorem.

### 3.1. A Shared Cut and Arbitrary Targets

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

### 3.2. The Threshold Algorithm

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

For `q_b>=1`, taking `tau=ceil(sqrt(q_b))` gives
`Õ(S+(V+E)sqrt(q_b))` time and `Õ(S+V sqrt(q_b))` words. In particular,
when `E,q_b,M=Theta(V)`, both are `Õ(V^(3/2))`. Taking
`tau=ceil(log(S+2))` instead gives near-linear space, while the term
`(V+E)q_b/log S` remains in time. Neither choice proves unrestricted
near-linear time. The schedule controls how many full kernels are built;
it does not assume cheap updates between unrelated residual graphs.

### 3.3. Exact Sharing and Its Space Cost

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

Exact sharing helps repeated-set families but leaves partial overlaps
uncompressed. The [representation examples](paper-b-representation-examples-v1.1-draft.md)
give a balanced switching family, for every power of two `m>=16`, with
`S=Theta(m^2)` and `Lambda=3m^2+m log_2 m`. For every power of two
`m>=2`, a common-block family of the same input order has
`Lambda>=m^2(2m+1)`. The latter is a limitation of flat-array equality
sharing, not a space lower bound for the Boolean batch problem. Maintaining
the square-root-threshold time bound with near-linear space on arbitrary
DAGs remains open.

## 4. Structural Algorithms

The threshold algorithm applies without a graph restriction. We now
consider two independent sources of additional structure: the regions
affected by a single deletion, and a supplied partition into reachability
chains. Their bounds can be near-linear even when the unrestricted
threshold bound is larger. We begin with the single-failure baseline.

<a id="statement-4-1"></a>

**Proposition 4.1 (one guard occurrence per label).** For a
healthy-zero output, if every label other than `t` occurs in at most one
remaining guard vertex after the common deletion, detection takes `O(G)` time and space. Together with the
linear healthy-one algorithm, this gives the same bound for either
healthy value under the stated guard condition.

*Proof.* When `Q={t}`, delete guard vertices containing `t`; return NO if this
deletes the root. Remove unreachable vertices and compute the dominator tree
from the root in linear time [BGK+08]. Group the terminals and guards by
label in the initial `O(G)` scan. Only labels `i!=t` need consideration:
`{t}` has the healthy value, for either choice of `Q`. Let `g_i` be the unique
remaining guard for candidate `i`, if any.

- Label `i` detects exactly when some `i`-terminal is reachable from the root
  without passing `g_i`.
- With no remaining `g_i`, any reachable `i`-terminal suffices. Otherwise a
  reachable terminal `l` avoids `g_i` on some path exactly when `g_i` does not
  dominate `l`.
- Dominance is an ancestor query in the dominator tree. Preorder and
  postorder numbers answer it in constant time.

The total over all terminals is `O(G)`, and one graph search supplies a
witness path if requested. The practical Lengauer–Tarjan algorithm [LT79]
has an inverse-Ackermann factor; the exact linear theoretical bound here
uses [BGK+08]. ∎

The single-output triangle and clique constructions use `Theta(log n)`
guards per ordinary label, all inside the selector. Proposition 4.1
shows that a single occurrence cannot realize their conditional hardness.

### 4.1. Localized Dominator Updates

Consider a listed OSR batch with sensitivity at most two. Remove vertices
initially unreachable from the source `r`, intersect every failure and
target set with the retained vertices, and answer NO to queries failing
`r`. These operations take `O(S)` time. Write `V,E` for the retained
vertex and edge counts and `h` for its maximum directed path length in
edges. Every remaining vertex is initially reachable. All subtrees below
include their roots, and paths in set expressions mean their vertex sets.

Let \(\mathcal D\) be the original dominator tree. Two *independent
spanning trees* \(B,R\), rooted at `r`, satisfy

\[
P_B(v)\cap P_R(v)=\operatorname{Dom}_D(v)
\]

for every vertex `v`. They and \(\mathcal D\) can be constructed in
`O(V+E)` time [BGK+08; GT15, Sections 2.3 and 4 of the author version].
For a non-root vertex `u`, define

\[
\begin{aligned}
\operatorname{Dead}(u)&=B(u)\cap R(u),\\
\operatorname{Fixed}(u)&=V(D)\setminus(B(u)\cup R(u)),\\
\Delta(u)&=B(u)\mathbin{\triangle}R(u).
\end{aligned}
\]

<a id="statement-4-2"></a>

**Lemma 4.2 (localization after one deletion).** The three sets above
partition the vertices. The dead set is exactly \(\mathcal D(u)\), the
vertices absent or unreachable after deleting `u`. Every other vertex
remains reachable. If \(z\in\operatorname{Fixed}(u)\), then
\(\operatorname{Dom}_{D-u}(z)=\operatorname{Dom}_D(z)\). The fixed set
is ancestor-closed in both dominator trees.

*Proof.* Membership in both subtrees means that both independent paths
contain `u`, which holds exactly when `u` dominates the vertex. Outside
their intersection, at least one of the two paths survives. For a fixed
vertex both paths survive. Deletion cannot remove an old dominator of a
surviving vertex, and every new dominator must lie on both surviving
paths. Hence

\[
\operatorname{Dom}_D(z)
\subseteq\operatorname{Dom}_{D-u}(z)
\subseteq P_B(z)\cap P_R(z)
=\operatorname{Dom}_D(z).
\]

Every old dominator `d` of a fixed vertex lies on both tree paths to it.
The corresponding prefixes to `d` also avoid `u`, so `d` is fixed.
Equality of the dominator sets proves closure in the updated tree too.
The partition follows from the elementary union, intersection, and
symmetric-difference identities, with `u` in the dead set. ∎

The lemma applies to general directed graphs. The algorithm that follows
uses acyclicity. Answer zero-failure queries by initial reachability and
one-failure queries by original dominator ancestry. Form an undirected
graph whose edges are the remaining two-element failure sets, and let
\(C\subseteq V(D)\setminus\{r\}\) be any vertex cover of it. Assign each
pair to one endpoint in `C`. Taking both endpoints of every edge in a
greedy maximal matching supplies a cover in `O(S)` time. Set

\[
\Sigma(C)=\sum_{u\in C}\sum_{v\in\Delta(u)}(1+\deg^-_D(v)).
\]

<a id="statement-4-3"></a>

**Theorem 4.3 (two-failure batch bound).** All Boolean answers of a listed
OSR batch of sensitivity at most two can be computed deterministically
and combinatorially in

\[
O\bigl((S+\Sigma(C))\log(V+2)\bigr)
\]

time and \(O(S+V\log(V+2))\) words of space, including preprocessing.
One witness path for a successful query takes an additional `O(V+E)`
time. Moreover,

\[
\Sigma(C)
=\sum_v(1+\deg^-_D(v))
  |C\cap(P_B(v)\mathbin{\triangle}P_R(v))|
\le (V+E)\min\{|C|,2h\}.
\]

Consequently the total time is \(\widetilde O(S+h(V+E))\), and is
\(\widetilde O(S)\) when `h` is polylogarithmic in `S`. By Proposition 2.2 this also gives \(\widetilde O((h+1)G)\) healthy-zero detection
when the residual guard multiplicity is at most two. The RAM word size
is logarithmic in the explicit input size.

*Proof.* We describe how to enumerate only the needed vertices, update
their dominators, and answer all queries assigned to that deletion.

**Reporting the difference.** Give both independent trees DFS preorder
intervals \(I_B(u)=[\operatorname{tin}_B(u),\operatorname{tout}_B(u))\)
and \(I_R(u)\). In `B` preorder, store the array of `R` preorder numbers.
Build a segment tree storing the minimum and maximum in each range;
build the symmetric structure in `R` preorder. These structures occupy
`O(V)` space and take `O(V)` time to construct.

To report \(B(u)\setminus R(u)\), restrict the index to \(I_B(u)\)
and report values below \(\operatorname{tin}_R(u)\), then values at
least \(\operatorname{tout}_R(u)\). Interchange the trees to report
\(R(u)\setminus B(u)\). The four outputs are disjoint. For a threshold
report, prune nodes outside the index interval and nodes whose stored
minimum or maximum excludes every answer. There are `O(log(V+2))`
boundary nodes. Every fully contained unpruned node has an output leaf
below it, so its work and that of its immediately pruned children can
be charged to root-to-output paths. Thus reporting `k` vertices costs
`O((k+1) log(V+2))` time. Sorting the resulting difference list by the
original topological ranks fits the same bound. Only one such list is
stored at a time.

**Updating the dominators.** Precompute depths, DFS intervals, and
binary-lifting ancestor tables in \(\mathcal D\), in `O(V log(V+2))`
time and space. The fixed vertices reuse their original ancestor tables:
Lemma 4.2 makes this an ancestor-closed unchanged tree. Represent it
implicitly, and allocate new rows only for the current \(\Delta(u)\).

For each \(v\in\Delta(u)\) in topological order, scan its incoming
edges and discard predecessors in \(\mathcal D(u)\). At least one
predecessor survives. In a DAG the strict dominators of a reachable
non-root vertex are the common dominators of its reachable predecessors:
every path ends with an incoming edge, and every path to a predecessor
extends to this vertex. Its immediate dominator is therefore the LCA of
those predecessors. This predecessor-LCA update is classical
[RR94, Section 3.1].

Every surviving predecessor is fixed or an earlier difference vertex.
Inductively, it and all its updated dominator ancestors are already
represented. A later topological vertex cannot dominate an earlier one,
so adding the current vertex changes none of the existing ancestor
chains. Compute its parent by binary-lifting LCAs, then install its new
depth and ancestor row. A row lookup uses the local row when installed
and the original row for a fixed vertex otherwise. It never enters a
dead or unprocessed vertex. This proves correctness and costs

\[
O\!\left(\sum_{v\in\Delta(u)}
        (1+\deg^-_D(v))\log(V+2)\right).
\]

A local-row pointer array is initialized once. Between deletions clear
only the entries in the previous difference list. Neither copying the
fixed tree nor resetting an array of length `V` is required per deletion.

**Answering the assigned queries.** For a pair \(\{u,y\}\) and target
`z`, first test membership in the original subtree \(\mathcal D(u)\).
If `z` lies there, it is unreachable. If `z` does not but `y` does,
`z` remains reachable: deleting an already unreachable vertex removes
no path to it. Otherwise both are reachable in `D-u`, and `z` survives
the second deletion exactly when `y` is not its ancestor in the updated
dominator tree. Binary lifting answers this in `O(log(V+2))` time.
These rules include a failed target and the length-zero path to `r`.
Take the OR over the listed targets for each query. All query work costs
`O(S log(V+2))`; a final traversal avoiding one successful failure set
recovers one witness path.

Summing the reporting and update costs over `C` proves the first time
bound, since \(|C|\le V\le S\). All static storage, input lists, and
one deletion's local rows use `O(S+V log(V+2))` words. Finally,

\[
v\in\Delta(u)\quad\Longleftrightarrow\quad
u\in P_B(v)\mathbin{\triangle}P_R(v).
\]

Interchanging sums gives the displayed identity for \(\Sigma(C)\).
Each tree path is a directed path of at most `h` edges. Both contain
the source, so their vertex-set symmetric difference has size at most
`2h`; its intersection with `C` also has size at most \(|C|\).
Summing \(1+\deg^-_D(v)\) over all vertices gives `V+E`. This proves
the depth bound. Proposition 2.2 supplies `S=O(G)` on the residual
healthy-zero graph, giving the stated detection consequence. ∎

The cost parameter can itself be computed without enumerating all
differences. Give vertex `v` weight \(a(v)=1+\deg^-_D(v)\), and let
\(W_T(u)\) be the total weight of subtree `u` in tree `T`. Three
bottom-up tree passes give

\[
\sum_{v\in\Delta(u)}a(v)
=W_B(u)+W_R(u)-2W_{\mathcal D}(u),
\qquad
\Sigma(C)=\sum_{u\in C}
  (W_B(u)+W_R(u)-2W_{\mathcal D}(u)),
\]

in `O(V+E)` time. This follows from the intersection identity in Lemma 4.2.
Corollary 4.8 uses these weights to choose a cover within a factor two
of the minimum cost for the fixed independent trees. A linear-size DAG with
two disjoint length-`k` branches and `k` common terminal successors
already has total difference size `Theta(k^2)` for the cover containing
all branch vertices. Thus this representation does not yield a
near-linear bound at arbitrary depth.

**Comparison with existing dominator algorithms.** Ramalingam--Reps
bound update work by the number of visited vertices and their incoming
edges [RR94]. Theorem 4.3 uses a particular sufficient region, reports
it without traversing newly unreachable subtrees, and bounds its total
cost across independent deletions of the original DAG. The `O(VE)`
total update bound of [GGIKL19] concerns a persistent edge-deletion
sequence; its monotone-depth amortization does not apply directly to
queries that reset to the original graph. Lemma 4.2 is an elementary
consequence of independent trees and deletion monotonicity. The
algorithmic refinement is the complete batch bound: the regions are
reported and processed without a full-tree reset, and their weighted
sizes are charged through `Sigma(C)`. The update rule and range-reporting
primitives retain their classical provenance.

Choudhary's dual-failure oracle gives constant-time pair-and-target
queries with linear oracle space [Cho16]; the detailed construction has
`O(VE)` preprocessing [Cho17, Theorem 3.2]. These are upper bounds, not
preprocessing lower bounds. For a fixed target, Teslenko and Dubrova's
linear-time double-vertex-dominator algorithm [TD15, Sections 8--9],
with the graph reversed and single dominators handled separately, gives
an `O(V+E)` preprocessing alternative. If `d_T` is the number of
distinct target vertices, applying it to each gives
`O(S+(V+E)d_T)` total time. Neither
baseline states Theorem 4.3's aggregate difference bound for a listed
multi-target batch.

Replacement-path covering supplies another comparison. The separating-family
argument of [DGR21, Lemma 5.3 in the full version] retains a short surviving
path while excluding the failed vertices. Instantiate the deterministic
Boolean hit-and-miss family of [KP21, Theorem 14 in the full version] with
path budget `max{2,h+1}` and failure budget two, after handling
zero-failure queries directly. Its family size and construction
time, followed by one source traversal and one scan of the listed queries
for each color class, give `Õ((h+1)^3 S)` total time. A surviving path has
at most `h+1` vertices and is separated from its failures by some family
member; every accepted traversal avoids the query's failures. This is a
direct application of the prior method, including its construction cost.
Thus near-linear time at polylogarithmic depth is already available by
covering. Theorem 4.3 gives the sharper `Õ(S+h(V+E))` dependence and the
more selective `Sigma(C)` bound, with near-linear working space at every
depth. These comparisons concern the specified constructions; priority
for the precise aggregate bound remains unestablished.

### 4.2. Streamed Chain Coordinates

The sum in Theorem 4.3 can be quadratic even when the batch has linear
size and distinct targets. Quadratic explicit dominator maintenance is
known for persistent edge-update sequences, including DAGs [GILS16,
Section 2]. The following example concerns independent vertex deletions
from one original graph and every choice of cover and independent trees.
It shows why avoiding that sum requires sharing more than individual
changed dominator parents.

<a id="statement-4-4"></a>

**Proposition 4.4 (quadratic explicit updates on an easy batch).** For
every `V>=12`, there is a rooted DAG with `V` vertices and `2V-3` edges
with at least `(V-3)(V-2)/2` distinct changed vertex-parent pairs across
single-vertex deletions. It admits a two-failure batch of size `S=Theta(V)`
with distinct singleton targets for which `Sigma(C)=Omega(V^2)` for every
cover `C` of the failure pairs and every pair of independent spanning
trees. Nevertheless, on this DAG every query with at most two failed
vertices is answered in constant time per target after linear
preprocessing.

*Proof.* Take vertices `0,...,V-1`, root `0`, and edges `j -> j+1` and
`j -> j+2` whenever their endpoints exist. The immediate dominator of
every non-root vertex is `0`. For a vertex at least `2`, the even and
odd routes from `0`, followed by a final one-step edge when necessary,
give two internally disjoint paths.

Delete `i`, where `1<=i<=V-3`. The only surviving edge crossing from
vertices below `i` to vertices above `i` is `(i-1,i+1)`. Thus `i+1`
dominates every surviving vertex above `i`. The suffix starting at
`i+1` has the same structure, so

\[
 \operatorname{idom}_{D-i}(x)=i+1\quad(x\ge i+2).
\]

The pairs `(x,i+1)` are distinct across deletions, giving

\[
 \sum_{i=1}^{V-3}(V-i-2)=\frac{(V-3)(V-2)}2.
\]

Put `k=floor(V/2)-2` and list the queries

\[
 F_i=\{i,i+1\},\qquad T_i=\{\lfloor V/2\rfloor+i\},
 \qquad 1\le i\le k.
\]

Their failure-pair graph is a path on `k+1` vertices. Every cover contains
at least `floor((k+1)/2)` of these vertices. For each such deletion `u`,
at least `V-u-2>=V-k-3` surviving vertices have changed immediate
dominators. Lemma 4.2 puts all of them in `Delta(u)`, regardless of the
chosen independent trees. Since every vertex weight in `Sigma(C)` is
at least one,

\[
 \Sigma(C)\ge
 \left\lfloor\frac{k+1}{2}\right\rfloor(V-k-3)=\Omega(V^2).
\]

For distinct failures `a<b`, a target `x` is reachable exactly when

\[
 a\ne0,\qquad x\notin\{a,b\},\qquad
 \neg(b=a+1\ \land\ b\le x).
\]

Each isolated failed vertex can be skipped by a two-step edge, whereas
two consecutive failures cannot be crossed. Failures after the target
do not affect it. With no failure every vertex is reachable; with one
failure only the deleted root or target prevents reachability. These
rules prove the query bound. ∎

This is a lower bound on the explicit update representation, not on
Boolean batch algorithms. A chain representation provides a different
way to share the graph across queries.

A *reachability-chain partition* divides the vertices into nonempty
sequences `C_1,...,C_p`, listed in topological order, such that consecutive
members of each sequence are reachable in the DAG. Connecting paths
need not be edges or be disjoint. A partition into vertex-disjoint
directed paths is a sufficient special case. Write `q_b` for the number
of listed failure queries, reserving `Q` for the forced label set.

<a id="statement-4-5"></a>

**Theorem 4.5 (streamed two-failure batches).** For a listed OSR batch of
sensitivity at most two, normalized as in Section 4.1, suppose a
partition of the retained DAG into \(p\) reachability chains is supplied.
All Boolean answers can be computed deterministically and
combinatorially in

\[
 O\!\left(S+(V+E)\log(V+2)+p(V+E+R_*)
             +q_{\mathrm b}p\log^2(V+2)\right)
\]

time and

\[
 O\!\left(S+(V+E)\log(V+2)\right)
\]

working words, including validation of the partition. Here \(R_*\) is
the total number of retained targets after the direct cases below have
been answered and at most one target per chain retained in each residual
query; in particular,

\[
 R_*\le \min\left\{\sum_i |T_i|,\ q_{\mathrm b}p\right\}.
\]

Thus the total bounds are \(\widetilde O(pS)\) time and
\(\widetilde O(S)\) space for every \(p\). A supplied partition with
\(p=\log^{O(1)}S\) gives near-linear time at arbitrary depth. One witness
path for a successful query takes an additional \(O(V+E)\) time.
The value \(p\) is the size of the supplied partition; a greedy
vertex-disjoint edge-path partition is available in \(O(V+E)\) time,
without a minimum-partition computation.

*Proof.* Check that the proposed lists partition the retained vertices
and follow topological order. Give every vertex its rank, chain
identifier, and zero-based chain position. The source has rank zero.
Remove duplicate
arcs, if any, by radix sorting their endpoint pairs in \(O(V+E)\) time,
retaining every distinct original arc. To obtain an edge-path partition
directly, scan the edges and select an edge whenever its tail has no
selected successor and its head no selected predecessor. Acyclicity
makes the selected components directed paths, which a linear traversal
lists.

Compute the ordinary dominator tree \(\mathcal D\). In a DAG, the
immediate dominator of a non-root vertex is the LCA of its predecessors
in the tree already constructed: its strict dominators are precisely
the common dominators of those predecessors. Topological order ensures
that later vertices cannot change an earlier vertex's dominators.
Binary lifting therefore constructs the tree in
\(O((V+E)\log(V+2))\) time and \(O(V\log(V+2))\) words. Retain its
Euler intervals \([\mathrm{tin}(x),\mathrm{tout}(x))\) and discard
the lifting table.

**The cut at the later failure.** Write the two distinct, non-root
failures as \(a<b\) in topological order. A target \(t<b\) survives
exactly when \(a\) does not dominate \(t\), because no path to \(t\)
visits \(b\). The target \(b\) is deleted. For \(t>b\), we claim

\[
 r\leadsto_{D-\{a,b\}}t
 \quad\Longleftrightarrow\quad
 \exists(u,w)\in E(D):
 \ u<b<w,\quad u\notin\mathcal D(a),\quad w\leadsto_D t.
\]

A surviving path has an edge crossing the position of \(b\). Its tail
\(u<b\) has a prefix avoiding \(a\), so \(a\) does not dominate \(u\).
Conversely, such a tail has an \(a\)-avoiding prefix, which also avoids
\(b\). After the crossing edge, every vertex on a path from \(w\) to
\(t\) has rank greater than \(b\), so that suffix avoids both failures.
Concatenation proves the claim.

Queries with no failure, a failed source, at most one failure, or no
targets are direct reachability or dominator tests. For two failures,
answer YES if an early target \(t<b\) survives; otherwise discard
targets at or before \(b\), leaving \(T^+\). If that list is empty,
answer NO. Within each chain retain only its latest target in \(T^+\).
If an earlier target in that chain survives, its connecting path to the
latest target
lies after \(b\), and so survives as well. The latest target was itself
in the original list, proving equivalence in both directions.
Timestamped arrays indexed by chain identifier form the retained lists
in \(O(S)\) total time. Use \(T^+\) for the retained list below. Write
\(r_i\) for its length and \(R_*=\sum_i r_i\); each \(r_i\le p\).

For a residual query, let

\[
 X_{b,T}=\{u:\exists(u,w)\in E(D),\ u<b<w,
                         \exists t\in T^+,\ w\leadsto_D t\}.
\]

The query succeeds exactly when this set has a member outside
\(\mathcal D(a)\). If it is nonempty, it suffices to find the minimum
and maximum of \(\mathrm{tin}(u)\) over \(u\in X_{b,T}\):
the minimum is below \(\mathrm{tin}(a)\), or the maximum is at least
\(\mathrm{tout}(a)\), exactly when such a member exists.
We compute these extrema one head chain at a time.

**One coordinate column.** For the current chain \(C_j\), compute

\[
 \lambda_j(t)=\max\{k:C_j[k]\leadsto_D t\},
\]

taking \(-1\) for an empty set and allowing length-zero paths.
Process vertices in topological order. At each vertex take the maximum
arriving value from its predecessors, and include its own position if
it lies on \(C_j\). Induction proves the displayed identity in
\(O(V+E)\) time and \(O(V)\) words. These are the reverse-direction
ordinary chain coordinates of [KT23, Sections 4.1--4.3].

The recurrence is exact even for a proposed ordered partition whose
chain property is not yet known. At \(C_j[k]\), \(k>0\), the maximum
arriving value before injecting \(k\) is at most \(k-1\). It equals
\(k-1\) exactly when \(C_j[k-1]\) reaches \(C_j[k]\). Check every such
equality during this pass; process every chain for validation even if
all query answers are already known.

For a valid chain, its vertices that reach any retained target form a
prefix ending at

\[
 A_j(T)=\max_{t\in T^+}\lambda_j(t).
\]

Consequently its eligible crossing-edge heads form the single interval
from the first chain position after \(b\) through \(A_j(T)\), or the
empty interval if these endpoints are reversed. Evaluating \(A_j(T)\)
costs \(O(r_i)\) for residual query \(i\).

**One original-edge index.** Group edges by the chain containing their
head. For the current \(C_j\), represent each edge \((u,w)\) by

\[
 \bigl(\operatorname{pos}_{C_j}(w),\ u,\ \mathrm{tin}(u)\bigr).
\]

We need the Euler extrema of triples whose head position lies in the
eligible interval and whose tail rank is less than \(b\).
Build a segment tree on the distinct head positions. At each node
sort the triples by tail rank and store prefix minima and maxima of
their Euler coordinates. Decompose a head interval into
\(O(\log(V+2))\) canonical nodes and binary-search the tail prefix
in each. One query costs \(O(\log^2(V+2))\).

If \(E_j\) edges have heads on \(C_j\), sorting and bottom-up merging
cost \(O(E_j\log(V+2))\) time and words. At any one head there are at
most \(V\) distinct incoming tails. Summing the index construction
over chains costs \(O(E\log(V+2))\). An empty range contributes NO.
Applying the Euler-interval test to each chain's nonempty range and
taking their OR answers the residual query.

We build, query, and discard each coordinate column and head index
before processing the next chain. The columns cost \(O(p(V+E))\);
target aggregation costs \(O(pR_*)\); range queries cost at most
\(O(q_{\mathrm b}p\log^2(V+2))\). The graph, queries, partition and
grouped edges use \(O(S)\) words. At most one \(V\)-entry column and
one \(O(E_j\log(V+2))\)-word index coexist. Together with dominator
preprocessing these give the stated bounds. A final graph search
avoiding a successful failure set constructs a witness path. ∎

The range-query overhead per residual query is
\(O(p\log^2(V+2))\), and target aggregation adds \(O(pr_i)\).
Singleton or bounded-size target lists therefore cost
\(\widetilde O(p)\) per query after the charged graph passes; arbitrary
lists can have \(r_i=p\). This is an offline batch computation, with
all target lists included in \(S\).

The edge indexes preserve transitive arcs. For \(0\to1\to2\) with an
additional edge \(0\to2\), deleting \(1\) leaves \(2\) reachable only
through that additional edge. A chain link may likewise cross a failure
elsewhere in the graph; the proof uses it as a safe suffix only when
both endpoints lie after \(b\).

<a id="statement-4-6"></a>

**Corollary 4.6 (Hamiltonian DAGs).** On a DAG with a directed Hamiltonian
path, a two-failure batch can be answered in
`O((V+E) log(V+2)+q_b log^2(V+2)+S)` time and
`O(S+(V+E) log(V+2))` words. The required path is recognizable in
`O(V+E)` time. This gives a near-linear algorithm on the family of
Proposition 4.4, despite its quadratic explicit-update cost.

*Proof.* A Hamiltonian path orders all vertices by reachability, so every
topological ordering has exactly that order and each consecutive pair is
an edge. Conversely, those edges in a topological ordering form a
Hamiltonian path. Check them by a graph scan and apply Theorem 4.5 with
`p=1`. The consecutive edges in Proposition 4.4 supply such a path. ∎

For residual guard multiplicity at most two, Proposition 2.2 and
Theorem 4.5 give healthy-zero detection in `Õ(pG)` time and `Õ(G)`
working words on a supplied partition of the residual graph.
Each terminal belongs to one channel's target list, so
all those lists together have size `O(G)`; the number of queries and
`V+E` are also `O(G)`. A successful path identifies its label and hence
the detecting set from Lemma 2.1. This complements the depth-dependent
bound of Theorem 4.3.

For unrestricted graphs, `p` may be `Theta(V)`, and the `p(V+E)` graph
passes can still take quadratic time on sparse inputs. The working
space stays near-linear for all `p`. The coordinate recurrence and
pathwise aggregation are classical [KPG+18; KT23]; the one-column
schedule is an offline loop interchange. The full guarantee combines
these with the later-failure cut, an index over original edges, and the
charged `pR_*` target work. It uses a supplied partition, without assuming
that a minimum partition can be obtained at no cost.

The fixed-path oracle of [IKP21, Theorem 4.1] is a close methodological
predecessor: it combines dominators and range reporting, but its single
failed vertex lies outside a fixed simple directed path. A supplied
reachability chain can have connecting paths through a failed vertex,
and the safe suffix used here depends on the later failure. Choudhary's
linear-space, constant-query oracle [Cho16; Cho17] also shows that low
retained oracle space is already available without a chain restriction.
The comparison here is the construction-inclusive `Õ(pS)` batch time
with `Õ(S)` working words. Priority for this precise combined guarantee
remains unestablished.

### 4.3. Constructing the Structural Parameters

The preceding bounds accept a chain partition or a failure-pair cover.
We now include the cost of choosing those objects. The constructions
use classical greedy path covering and weighted vertex cover; the
conclusions are consequences of Theorems 4.5 and 4.3, respectively.

Let `kappa` be the minimum number of reachability chains partitioning
the retained DAG, called its *reachability width*. Equivalently, it is
the minimum number of directed paths covering all vertices when paths
may overlap. Extend each chain by connecting paths to obtain such a
cover; conversely, assign every vertex to one covering path, whose
assigned subsequence is a reachability chain. This differs from the
minimum number of vertex-disjoint edge paths.

<a id="statement-4-7"></a>

**Corollary 4.7 (constructed width bound).** For a listed failure batch
of sensitivity at most two, let `kappa` be the reachability width of
the initially source-reachable retained DAG. All query answers can be
computed deterministically and combinatorially in `Õ(kappa S)` total
time and `Õ(S)` working words, including construction of a qualifying
chain partition. Neither `kappa` nor a partition is required as input.

*Proof.* Use the greedy overlapping-path construction of
[KPG+18, Lemma 1]. Mark vertices as uncovered. At each iteration assign
weight one to uncovered vertices and zero to covered vertices, and find
a directed path of maximum total weight. In reverse topological order,
compute each vertex's weight plus the largest value of an outgoing
neighbor, storing a maximizing successor. Starting at a largest-value
vertex and following these successors constructs such a path in
`O(V+E)` work. Assign its previously uncovered vertices, in path order,
to a new chain and mark them covered. The chain is nonempty, and its
consecutive vertices are connected along that path. Previously covered
vertices need not be stored again.

Fix a cover by `kappa` paths. If `U` vertices remain uncovered, some
cover path contains at least `U/kappa` of them. The greedy path covers
at least that many. Thus the number remaining decreases by a factor at
most `1-1/kappa`; for `kappa=1` one iteration suffices. In general
`O(kappa log(V+2))` iterations cover every vertex. The algorithm stops
when none remains, without using `kappa`.

The resulting `p=O(kappa log(V+2))` nonempty assigned subsequences
partition the vertices into reachability chains. Discovery costs
`O(kappa(V+E)log(V+2))` time and `O(V+E)` words: reuse the marks,
dynamic-programming rows and current path, and store every assigned
vertex once. Theorem 4.5 then computes every query answer in `Õ(pS)`
time and `Õ(S)` words, including validation and target aggregation.
Together these prove the stated bounds. ∎

This corollary gives near-linear total time at polylogarithmic width,
without a supplied partition or bounded-depth assumption. The width can
still be linear in `V`, so the unrestricted near-linear-time question
remains. The discovery mechanism is classical; its application here
includes the full streamed-query cost.

For the localized algorithm, fix the independent trees `B,R` and the
ordinary dominator tree \(\mathcal D\) of Section 4.1. Give each nonroot vertex
`u` the nonnegative deletion-region weight
\[
 c(u)=W_B(u)+W_R(u)-2W_{\mathcal D}(u)
     =\sum_{v\in\Delta(u)}(1+\deg^-_D(v)).
\]
Let `J` be the graph on nonroot vertices with one edge for every
remaining two-element failure set, and
let `OPT_c` be the minimum `sum_{u in C} c(u)` over vertex covers `C`
of `J`. These weights and this optimum refer to the fixed trees; no
optimization over independent-tree choices is asserted.

<a id="statement-4-8"></a>

**Corollary 4.8 (weighted deletion-cover selection).** All query answers
of the listed two-failure batch can be computed deterministically and
combinatorially in `O((S+OPT_c)log(V+2))` total time and
`O(S+V log(V+2))` working words. The algorithm constructs a cover of
weight at most `2 OPT_c` in `O(V+q_b)` additional time after the weights
are available; it does not require an optimum cover as input.

*Proof.* Compute the subtree weights by the three tree passes in
Section 4.1, costing `O(V+E)`. Apply the classical linear-time
weighted-cover approximation [BE81], with the following primal-dual
implementation. Initially set residual weight `rho(u)=c(u)`, select all
zero-weight vertices, and set all edge duals to zero. Process each edge
`uv` once. If already covered, skip it. Otherwise put
`delta=min{rho(u),rho(v)}`, increase its dual `y_uv` by `delta`, subtract
`delta` at both endpoints, and select every endpoint whose residual
becomes zero. This covers the edge. Duplicate listed edges cause only
additional constant-time covered-edge tests.

For every vertex, the sum of incident edge duals is at most its original
weight. Every selected vertex is tight, and all later incident edges
are skipped. Therefore the returned cover satisfies
\[
 \sum_{u\in C}c(u)
 =\sum_{u\in C}\sum_{e\ni u}y_e
 \le2\sum_e y_e
 \le2\,OPT_c.
\]
For the final inequality, any vertex cover contains an endpoint of each
edge, so its total weight is at least `sum_e y_e`. This also handles
zero weights. The residual arrays, selection flags and one pass over
the listed edges use `O(V+q_b)` time and space. All weights are at most
`V+E`, and their sums are polynomially bounded in the explicit input
size, so logarithmic-size words suffice.

Now `Sigma(C)=sum_{u in C}c(u)<=2 OPT_c`. Apply Theorem 4.3 with this
constructed cover, including its preprocessing and all original target
incidences. The weight and cover construction fit its `S` term, giving
the stated time and workspace. ∎

## 5. Conditional Bounds and Failure Multiplicity

These reductions concern the existential version at larger failure
multiplicities and specified label-to-size regimes. An all-query solver
also solves that version by taking the OR of its answer vector in
`O(q_b)` additional work; this cost is absorbed in the explicit input
term of the comparisons below. They do not give a superlinear lower bound for
the constant-two-failure problem of Section 3. We separate combinatorial
hypotheses from hypotheses for general word-RAM algorithms. The full
comparison table in Appendix A.4 records the assumptions for each bound.

### 5.1. Combinatorial Algorithms

A selector forces a path's starting entry to equal its terminal label
without copying the shared intermediate graph. Triangle layers establish
the first regime; tuple layers carry the same argument to every fixed
interior ratio of label count to size.

For a healthy-zero root, Lemma 2.1 reduces detection to finding a path
to a labelled terminal that never guards its label; when `Q={t}`, the
path must also avoid guards on the forced target. Sharing makes these separate
label reachability tests potentially expensive. A balanced selector can
enforce equality between a path's chosen start and its terminal label
while retaining shared intermediate layers.

We use the combinatorial triangle detection conjecture, equivalently the
combinatorial Boolean matrix multiplication conjecture [ASW26, Conjecture 1]:
no combinatorial algorithm detects a triangle in a `p`-vertex graph in
`O(p^{3-delta})` time for any fixed `delta>0`. The combinatorial restriction
is part of this hypothesis; it excludes fast algebraic matrix multiplication.
We use its deterministic version on a word RAM with logarithmic word size.
A randomized consequence requires the corresponding randomized hypothesis.

<a id="statement-5-1"></a>

**Theorem 5.1 (single-output triangle reduction).** A tripartite graph with
`p>=1` vertices in each part and `m` edges can be transformed in
`O(m+p log(p+1))` time into a guarded DAG with one
healthy-zero output, `Q={t}`, `n=p+2` labels and
`G=O(m+p log(p+1))`. Detection is possible exactly when the graph contains
a triangle. Consequently, under the combinatorial triangle conjecture,
there is no combinatorial `O(G^{3/2-epsilon})` detection algorithm for any
fixed `epsilon>0`. In the regime `G=Theta(n^2)`, the exponent matches
the `O(nG)` upper bound.

*Proof.* Let the parts be `A,B,C`, and use labels `A union {t,d}` with
target `t`, an unused auxiliary label `d`, and `Q={t}`. Store the following three
OR layers once, taking an empty OR to be zero:

\[
 C_c(h)=\bigvee_{a:\,ca\in E}h_a,\qquad
 B_b(h)=\bigvee_{c:\,bc\in E}C_c(h),\qquad
 D_a(h)=\bigvee_{b:\,ab\in E}B_b(h).
\]

For an ordinary singleton `{i}`, `D_a({i})=1` exactly when there is a
three-edge path `a -> b -> c -> i`. In particular, `D_i({i})=1` exactly
when `i` belongs to a triangle. Merely OR-ing all `D_a` would lose the
equality between the start and the terminal label.

Construct a balanced binary tree whose leaves are the members of `A`.
For a leaf set `I`, define `T_{ {a} }=D_a`. At an internal split
`I=L disjoint-union R`, with child sizes differing by at most one, define

\[
 T_I=
 \left(T_L\wedge\bigwedge_{j\in R}\neg h_j\right)
 \vee
 \left(T_R\wedge\bigwedge_{j\in L}\neg h_j\right),
 \qquad F=T_A.
\]

Each guarded conjunction in the selector has exactly one live child. Along the
selector branch ending at `a`, the sibling sets partition `A minus {a}`.
Distributing OR over the guards therefore gives the exact identity

\[
 F(h)=\bigvee_{a\in A}
       \left(D_a(h)\wedge\bigwedge_{j\in A\setminus\{a\}}\neg h_j\right).
\]

For the active ordinary set `S`, this is zero when `S` is empty because
all ordinary terminals are zero. It is also zero when `|S|>=2`, since every
term has an active guard. When `S={i}`, only its matching term can survive,
and `F(S)=D_i({i})`. Neither `t` nor `d` occurs in these expressions. Thus
`F({t})=0`, and detection is equivalent to a triangle through some `i`.
The admissible set `{t,i}` detects; the auxiliary label need not be selected.

The OR layers use `3p` vertices and `m` child incidences. The selector adds
`3(p-1)` vertices and `4(p-1)` live edges. Each label is guarded once per
ancestor in the balanced tree, at most `ceil(log_2 p)` times. Including
all input vertices and the single output incidence gives
`G=O(m+p log(p+1))`, with the same construction time. No layer is copied
when several starts use it.

Ordinary triangle detection reduces to this tripartite problem by taking
three copies of the vertex set and inserting each source adjacency between
each consecutive pair of parts. A tripartite triangle corresponds to three
pairwise adjacent source vertices; without source self-loops they are
distinct. Here `m=O(p^2)` and `G=O(p^2)`. For
`0<epsilon<1/2`, a detector with the stated running time would decide the
source problem in `O(p^2+p^{3-2epsilon})`, contradicting the conjecture.
Larger fixed savings imply one in this range.

The same contradiction holds on the promise `G=Theta(n^2)`: add disjoint
fresh sets of `p` vertices to each part, place a complete bipartite graph
between the fresh `A` and `B` sets, and leave the fresh `C` set isolated.
This adds no triangle, doubles the part size, and makes the edge count
`Theta(p^2)`. Theorem A.1 runs in `O(nG)=O(G^{3/2})` on this regime. ∎

The balanced selector is a static form of the binary-tree deletion gadget
of Abboud and Williams [AW14, Lemma 8.3]. In their reduction from triangle
detection to decremental reachability, stage `x` deletes the sibling edges
along the root path of `x`. Here the guards on those sibling branches
contain the label instead. Proposition 2.2 makes the correspondence
exact. Their fixed-source-and-sink construction uses two selector trees;
our varying terminal label needs only the source-side selector. The
logarithmic-sensitivity BMM bound for the dynamic setting is also recorded
in [HLNV17, Table 2]; Proposition 2.2 concerns the fully listed
existential batch.

This bound rules out a near-linear **combinatorial** algorithm under the
stated conjecture. It does not exclude unrestricted algebraic algorithms
or establish a quadratic bound in `G` for a single output. The bitset
bound is `O(G ceil(n/w))`; with logarithmic words its savings are compatible
with the conditional exponent. Uniform combinatorial bounds
`O(n^{1-epsilon}G)` or `O(nG^{1-epsilon})` are also excluded by the same
dense instances.

The construction never uses equal part sizes: with parts `A,B,C` of any
sizes, the same guarded DAG has `n=|A|+2` labels and
`G=O(m+|B|+|C|+|A| log(|A|+1))`, and detects exactly the triangles.
Unequal parts determine the dependence on both parameters when the guarded DAG
is large relative to the number of labels.

**Consequence for the dense instances of Theorem 5.1.** On the padded
promise `G=Theta(p^2)`, these have `V=O(p)` vertices,
`k_i<=ceil(log_2 p)` and `l_i=1`. Proposition A.3 gives `Õ(p^omega)`, which is
`Õ((nG)^{omega/3})`. This beats `O(nG)=Theta(p^3)` and matches the matrix-multiplication
bound for dense triangle detection. On that class, single-output detection is
therefore no harder than dense triangle detection, up to polylogarithmic
factors.

<a id="statement-5-2"></a>

**Theorem 5.2 (triangle-only bound when `n <= G <= n^2`).** Under the
combinatorial triangle conjecture, for every fixed `epsilon>0` there is
no combinatorial single-output detection algorithm with running time
`O(G^{3/2-epsilon})` throughout the regime `n <= G <= n^2`.
The reduction uses one healthy-zero root and `Q={t}`; unused-label
padding lets the label count range from `Theta(sqrt G)` to `Theta(G)`.

*Proof.* Start with the dense padded triangle instances of Theorem 5.1,
with `p` vertices per part, `p+2` labels, and size `Theta(p^2)`. Add unused
labels until the declared count is any prescribed `n` between `Cp` and
`p^2`, for a sufficiently large fixed constant `C`. These labels do not
occur at a terminal or guard, so they preserve the detection answer.
They add `O(n)` to the stored size, which remains `G=Theta(p^2)`.
Choose `C` large enough that `G<=n^2` throughout this range; `n<=G`
holds because all declared labels count in `G`. Construction takes
`O(p^2+n)=O(p^2)` time. A detector
with the stated bound would therefore decide triangle detection in
`O(p^2+p^{3-2epsilon})` time. For `0<epsilon<1/2` this is truly subcubic;
larger savings imply one in that range. ∎

For `n <= G <= n^2` the triangle bound `G^{3/2}` lies below `O(nG)` by the
factor `n/sqrt G`. Triangle instances cannot close this gap. A sparse
tripartite graph with `m` edges and part `A` of size `n>sqrt m` already
admits an `O(m^{3/2})` combinatorial triangle algorithm, which is below
`nm`. Larger cliques do close it. The key ingredient is the construction of
[DJVW22, Sections 2.1.1 and 4.1] for `n`-pairs shortest paths: vertices indexed by
tuples of vertices, so that one path carries several coordinates at once.
The selector of Theorem 5.1 turns their matched-pairs question into a
single guarded output, and unequal parts make the bound proportional to `nG`.

We use the combinatorial `k`-Clique hypothesis [DJVW22, Hypothesis 1]: for
each fixed `k>=3`, no combinatorial algorithm detects a `k`-clique in an
`N`-vertex graph in `O(N^{k-delta})` time for a fixed `delta>0`. The case
`k=3` is the combinatorial triangle conjecture used above.
The lower bounds concern deterministic algorithms on logarithmic-size
words; randomized versions require the corresponding randomized hypotheses.

<a id="statement-5-3"></a>

**Theorem 5.3 (fixed polynomial regimes).** Fix an integer `c>=1` and put
`k=2c+1`. Consider a `k`-partite graph whose first `c` parts have `a`
vertices and whose other `c+1` parts have `b>=a` vertices. In `O(b^{c+1})`
time it becomes a guarded DAG with:

- one healthy-zero output with `Q={t}`;
- `n=a^c+2` labels and `G=Theta(b^{c+1})`.

Detection is possible exactly when the graph contains a `k`-clique.

Consequently, fix `gamma` with `0<gamma<=c/(c+1)` and `epsilon>0`. Under
the combinatorial `k`-Clique hypothesis, no combinatorial algorithm decides
detection in `O((nG)^{1-epsilon})` time on instances with `n=Theta(G^gamma)`.
Taking `c=ceil(gamma/(1-gamma))` covers every fixed `0<gamma<1`. Hence
`O(nG)` is optimal up to `(nG)^{o(1)}` factors for combinatorial
algorithms in these fixed polynomial regimes.

*Proof.* Empty source parts give NO immediately; assume `1<=a<=b`.
Use the tuple labels together with distinct target `t` and auxiliary `d`.

**Layers.** Index the positions `0,...,k-1` cyclically. Window
`W_s` consists of positions `s,...,s+c-1`, for `s=0,...,k`; window `W_k`
equals `W_0`. Layer `s` has one OR vertex per tuple in the product of the
parts on `W_s`. A vertex `x` at layer `s` has child `y` at layer `s+1` when
two conditions hold:

- `x` and `y` agree on their `c-1` shared positions;
- the `c+1` vertices they cover are pairwise adjacent.

Layer `k` consists of the labelled terminals, one per tuple `tau` on `W_0`.

**Selector.** Apply the balanced selector of Theorem 5.1 over these
labels, with `D_tau` the layer-0 vertex of `tau`. As there,

\[
 F(h)=\bigvee_{\tau}\Bigl(D_\tau(h)\wedge
       \bigwedge_{\tau'\ne\tau}\neg h_{\tau'}\Bigr).
\]

- If two or more tuple labels are active, every term has an active guard.
- If no tuple label is active, every terminal is false.
- If `K` meets the tuple labels exactly in `{tau}`, then `F(K)=1` exactly when
  a path leaves the layer-0 vertex of `tau` and ends at the terminal of `tau`.

**Paths are cliques.** Such a path assigns one vertex to every position.
Consecutive windows agree on their shared positions, and each position lies
in a run of `c` consecutive windows. For the run that crosses from position
`k-1` to position `0`, agreement comes from identifying the final window
with the starting tuple. Two positions at cyclic distance at most `c` lie in
a common covered `(c+1)`-window. Because `k=2c+1`, every pair of positions
is within that distance. Hence the vertices on the path form a `k`-clique.
Conversely, a `k`-clique gives such a path for its first `c` vertices.

**Detection.** No tuple label is active at `{t}`, so the healthy value is zero.
The admissible set `{t,tau}` is a witness.

**Size.** Enumerate each covered `(c+1)`-tuple once, check its constant
number of adjacencies, and emit its transition if they all hold. Each
layer has at most `b^c` vertices and `b^{c+1}` candidate transitions; enumerating
all pairs of layer vertices is unnecessary. The selector adds
`O(a^c log(a+1))=O(b^{c+1})` guard incidences for fixed `c`.
Retain an unobserved chain of `b^{c+1}` binary OR vertices, starting at `h_t`
and OR-ing its predecessor with `h_d` at each step. This makes
`G=Theta(b^{c+1})` without changing any answer. The auxiliary label `d` is distinct from the target and tuple labels.
All vertices of this chain count in `G`, although the observed root does not
reach it.

**Bound.** Let `a=ceil(b^alpha)` with a fixed `0<alpha<=1`. Take a balanced
`k`-partite instance with `b` vertices per part, and partition each of its
first `c` parts into blocks of `a` vertices, padding the last block with
isolated vertices. This gives `O((b/a)^c)` instances
of the stated shape, and the graph has a `k`-clique exactly when one of
them does. Each instance has `nG=Theta(a^c b^{c+1})`. Suppose a detector ran
in `O((nG)^{1-epsilon})`. Adding the `O(b^{c+1})` construction cost, it
would detect `k`-cliques in time

\[
 O\!\left((b/a)^c\bigl((a^c b^{c+1})^{1-\epsilon}+b^{c+1}\bigr)\right)
 = O\!\left(b^{k-\epsilon(\alpha c+c+1)}+b^{k-\alpha c}\right),
\]

which contradicts the hypothesis. Finally,
`n=Theta(a^c)=Theta(G^{alpha c/(c+1)})`, so `gamma=alpha c/(c+1)` ranges
over all of `(0,c/(c+1)]`. A general `k`-clique instance is made balanced
`k`-partite by taking `k` vertex copies and copying adjacencies between
distinct parts. With no self-loops, a partite clique uses distinct source
vertices. This costs `O(b^2)` for fixed `k` and preserves the hypothesis. ∎

**Remark (fixed powers with `G >= n^2`).** For every fixed real
`rho>=2`, Theorem 5.3 with `c=1` and `gamma=1/rho` rules out a
combinatorial `O((nG)^{1-epsilon})` detector on `G=Theta(n^rho)` for
every fixed `epsilon>0`. Here `k=3`, so only the combinatorial triangle
conjecture is needed.

For `c=1`, Theorem 5.3 is the triangle construction with unequal parts.
For each fixed `c>=1`, its balanced tuple graph also gives a conditional
density bound for the existential batch problem. Before adding the binary
padding chain, it has `V=Theta(b^c)` vertices, at most `O(b^{c+1})` edges,
and `Theta(V)` queries with `O(log V)` failures each. Add a disjoint
directed complete bipartite graph with part sizes `b^c` and `b`. Then
`m=Theta(b^{c+1})=Theta(V^{1+1/c})`, the query lists total `O(V log V)`,
and all answers are preserved. An `O((Vm)^{1-epsilon})` combinatorial
batch algorithm would solve `(2c+1)`-Clique in
`O(b^{(2c+1)(1-epsilon)}+b^{c+1})`, contradicting its hypothesis.
[AW14, Lemmas 8.1–8.3] already studies variable edge counts and sparse
triangle consequences; priority for this particular clique-based density
consequence is unestablished.

### 5.2. General Word-RAM Algorithms

The combinatorial restriction excludes fast matrix multiplication. Two
other hypotheses address algorithms that may use it: algebraic clique
optimality gives a partial bound at certain fixed ratios, and directed
cycle hardness gives a quadratic exponent near the largest declared
label counts.

The algebraic clique hypothesis `F=omega` [ABV15, Section 1] asserts that
there is no constant `F'<omega` such that, for every sufficiently large
fixed integer `s`, `3s`-Clique on `p` vertices can be decided in
`O(p^{F' s})` time. This is the large-clique formulation used in the
next argument, with deterministic word-RAM algorithms throughout.

<a id="statement-5-4"></a>

**Proposition 5.4 (balanced algebraic transfer).** Assume the
deterministic algebraic clique hypothesis `F=omega`. For every fixed
integer `c>=2` and every fixed `epsilon>0`, no deterministic word-RAM
algorithm with logarithmic word size decides single-output detection in
`O((nG)^{omega/3-epsilon})` time on the balanced instances of Theorem 5.3
with `n=Theta(G^{c/(c+1)})`. These instances have one healthy-zero root
and `Q={t}`.

*Proof.* Put `k=2c+1` and take `a=b` in Theorem 5.3. Then
`n=Theta(b^c)`, `G=Theta(b^{c+1})`, and `nG=Theta(b^k)`. A detector with
the stated time would solve balanced `k`-partite Clique in
`O(b^tau)` time, including construction, where

\[
\tau=\max\{k\omega/3-k\epsilon,\ c+1\}.
\]

Since `c>=2` and `omega>=2`,

\[
c+1<2k/3\le k\omega/3,
\qquad \tau<k\omega/3.
\]

Choose a fixed real `F'` with `3tau/k<F'<omega`, and choose a fixed
integer `s_0` large enough that `3s_0>=k` and
`tau/s_0<F'-3tau/k`. For each fixed integer `s>=s_0`, partition the
`3s` positions of a clique into `k` nonempty blocks of size at most
`r=ceil(3s/k)`. Given a graph on `p` vertices, create one part per block
whose vertices are internally complete tuples of distinct source
vertices assigned to that block. Join two tuples exactly when every
cross pair is adjacent in the source graph. Source self-loops are
absent, so a tuple selection forming a `k`-clique uses `3s` distinct
vertices and is equivalent to a source `3s`-clique.

Every part has at most `p^r` tuples. Pad smaller parts with isolated
vertices to the common size `b=p^r`, preserving the answer. Tuple and
edge construction costs `O_s(p^{2r})`; it is dominated by `O_s(p^{tau r})`
because `tau>=c+1>=3`. Applying the balanced detector therefore gives
a `3s`-Clique algorithm with exponent

\[
\tau\lceil3s/k\rceil
\le (3\tau/k)s+\tau
<F's
\qquad(s\ge s_0).
\]

The same fixed `F'<omega` works for every sufficiently large fixed `s`,
contradicting `F=omega`. No divisibility condition on `k` is used. ∎

For `c=1`, the construction exponent is two and need not be strictly
below `k omega/3` when `omega=2`; this argument makes no claim at that
boundary. Randomized lower bounds require the randomized form of the
source hypothesis.

Directed cycle detection supplies a conditional exponent bound that includes
algebraic algorithms at the top of the label-count range. We use the
`k`-Cycle Hypothesis [DJVW22, Hypothesis 6] on a word RAM
with logarithmic word size: for every `epsilon>0` there is a constant `k`
such that no algorithm detects a directed `k`-cycle in an `m`-edge graph in
`O(m^{2-epsilon})` time. It includes algebraic word-RAM algorithms. We state
the deterministic consequence; bounded-error randomized consequences require
the corresponding randomized hypothesis and error amplification.

<a id="statement-5-5"></a>

**Theorem 5.5 (quadratic exponent for general word-RAM algorithms).** Assume
the deterministic `k`-Cycle Hypothesis. Then for every fixed `epsilon>0`,
no deterministic word-RAM algorithm with logarithmic word size decides
single-output detection in `O(G^{2-epsilon})` time. This holds with `Q={t}`, one healthy-zero output,
guard multiplicity `O(log n)`, and
`n=Theta(G)` after adding unused labels. Consequently:

1. on the padded promise `n=Theta(G)`, the worst-case exponent two is
   optimal in this model; this promise lies within `n=G^{1-o(1)}`;
2. no algorithm in this model runs in `O((nG)^{1-epsilon})` on all instances.
   In particular there is no uniform algebraic saving of a fixed power
   from `nG`. Logarithmic and other subpolynomial savings remain possible.

*Proof.* Let `H` be a directed graph with `v` vertices and `m` arcs. Remove
isolated vertices, so `v<=2m`; a graph with no arcs is answered directly.

**Colourings.** By colour-coding [AYZ95], there is a family of
`2^{O(k)} log(v+1)` colourings of the vertices with `k` colours such that
every `k`-set receives distinct colours under one of them. Trying the
`(k-1)!` cyclic orders of the colours for each, some colouring gives the
vertices of a fixed `k`-cycle the colours `0,1,...,k-1` in cyclic order.

**Guarded DAG for one colouring.** This is the layered construction of
[DJVW22, Theorem C.3], closed by the selector. Use the colour-0 vertices
as ordinary labels, add distinct labels `t,d`, and set `Q={t}`.

- Each vertex gets an OR vertex.
- An arc `u->v` with `colour(v)=colour(u)+1<k` becomes an edge between
  their vertices.
- An arc `u->v` with `colour(u)=k-1` and `colour(v)=0` becomes an edge from
  the vertex of `u` to the terminal of label `v`.
- The labels are the colour-0 vertices. Apply the balanced selector of
  Theorem 5.1 with `D_v` the vertex of `v`.

As in Theorem 5.1, only a single active ordinary label `v` can make the output
true, and then exactly when a path leaves the vertex of `v` and ends at the
terminal of `v`. Such a path visits colours `0,...,k-1` once each, so its
vertices are distinct and form a `k`-cycle. Conversely a `k`-cycle coloured
in cyclic order gives the path. The healthy value is zero.

**Size and time.** Bucket vertices by colour and scan arcs once to build
adjacency lists. Each arc is used at most once, and the selector adds
`O(v log(v+1))` guard incidences, so the construction and its size are
`O(m+v log(v+1))=O(m log(m+1))`. Empty colour classes can be rejected directly.
For the nonempty instances, add as many unused declared label inputs as
the unpadded guarded DAG size. They preserve the output function and admissibility: restricting an
admissible set to the original labels still retains `t`. The resulting instance has `n=Theta(G)` with only a constant
factor increase in `G`.

It suffices to consider `0<epsilon<1`. An `O(G^{2-epsilon})` detector on
this padded promise, applied to all `2^{O(k)}(k-1)! log(v+1)` colourings,
including their construction, yields `O_k(m^{2-epsilon/2})` time for every
fixed `k`, absorbing logarithmic factors. Choose the fixed `k` supplied by
the hypothesis for `epsilon/2`; this contradicts it. The algorithm for each
such `k` is uniform in the source graph size. Since `n<=G`, a uniform
`O((nG)^{1-epsilon})` detector would likewise save a fixed power of `G`. ∎

A non-target label is *essential on the admissible domain* if two
sets in `K_Q` differing only in that label have different root values.
The next promise removes unused-label padding on YES instances while
retaining NO instances.

<a id="statement-5-6"></a>

**Corollary 5.6 (essentiality on admissible sets).** Under the same
deterministic `k`-Cycle Hypothesis, no `O(G^{2-epsilon})` word-RAM detector
exists even on the following two-sided promise: `n=Theta(G)`, and the
guarded DAG is either undetectable or every non-target label coordinate
is essential on `K_Q` with `Q={t}`. Guard multiplicity remains
`O(log n)`.

*Proof.* Before unused-label padding, write `F` for the cycle-selector
output, `A` for its ordinary labels and `d` for its auxiliary label. It ignores
the target and auxiliary label and is true exactly on ordinary sets `{a}` whose
label belongs to a correctly coloured source cycle. Add a set `Z` of
fresh labels of size equal to the unpadded representation size `G_0`,
and use the guarded output

\[
 \widehat F=F\wedge\neg h_d\wedge\bigwedge_{z\in Z}\neg h_z.
\]

Its label count and size are both `Theta(G_0)`. The detecting set
`{t,a}` preserves every YES-instance; every detecting set still gives a
source cycle. On a YES-instance fix this set. Removing `a` kills its
positive path; adding another ordinary label blocks the selector;
adding `d` or a fresh label blocks the root guard. These comparisons
stay in the admissible domain and differ in exactly the tested coordinate.
Every non-target coordinate is therefore essential. Each fresh label and
the auxiliary label `d` has one guard occurrence; ordinary-label
multiplicities are unchanged. The size and
colour-coding argument of Theorem 5.5 applies. ∎

The NO branch is necessary: an undetectable single output is constant on
the admissible domain and has no essential coordinates there. Requiring
positive essentiality on this domain even on NO-instances would remove every NO
instance. Essentiality on the full Boolean cube is a weaker condition:
`F OR (not h_t AND OR_{i!=t} h_i)` makes every label essential there
when `F` ignores `t,d`, while its added term vanishes throughout the
domain `K_Q` with `Q={t}`. Corollary 5.6 uses essentiality
on the admissible domain.

In the terms of Proposition 2.2, Theorem 5.5 says that a batch of `n`
single-source reachability queries with `O(log n)` vertex failures each
has no `O(m^{2-epsilon})` total-time algorithm in the same model on a
sparse padded promise with `n=Theta(m)`. Add a disjoint matching with
`Theta(G)` arcs and use its unreachable endpoints as targets of the unused
queries. Both the vertex and edge counts are then `Theta(G)`; the total
failure-list size is `O(G)`. All these representation costs are
included. This is a worst-case conditional exponent bound, not a claim
that every batch is hard. Proposition A.3 remains compatible because its
cost also depends on the vertex count `V`, which can be `Theta(G)` here.

### 5.3. Failure Multiplicity and Selector Capacity

The reductions place guards in selectors. We first trade guard
multiplicity for copied layers, then use the known anti-isolation bound
to determine exact selector budgets. These statements leave the general
total-time algorithmic question separate.

<a id="statement-5-7"></a>

**Proposition 5.7 (multiplicity–size trade-off).** Let `s>=0` and `0<=h<=s` be integers, and put `p=2^s`. A tripartite graph with `p` vertices per part becomes, in
`O(2^h p^2)` time, a one-output guarded DAG with:

- `n=p+2` labels;
- every ordinary label in exactly `mu=s-h` guard vertices;
- `G=Theta(2^h p^2)`.

Detection is possible exactly when the graph contains a triangle.
Consequently, fix `0<lambda<=1`. Under the combinatorial triangle
conjecture, no combinatorial algorithm decides detection in
`O((2^mu G)^{1-epsilon})` time on instances with guard multiplicity
`mu=lambda log_2 n+O(1)`.

*Proof.* **Copies.** Split each label `a in A` into its top `h` bits
`hi(a)` and its remaining `s-h` bits. Create `2^h` copies of the `B` and
`C` layers of Theorem 5.1. In copy `H`, the vertex `C_c` lists only the
terminals `h_a` with `ca in E` and `hi(a)=H`. Let `D_a` be the OR of the copy
`hi(a)` vertices `B_b` with `ab in E`.

**Selectors.** Inside each copy, apply the balanced selector of Theorem 5.1 to the `2^{s-h}` labels with that top value, and OR the `2^h`
selector roots.

**Correctness.** A path from `D_a` can end only at a terminal `h_{a*}` with
`hi(a*)=hi(a)`. The selector of that copy forbids every other active
label of the copy, so `a*=a`. Hence `F(K)=1` exactly when some active
`a` lies in a triangle and no other label with the same top bits is
active. Detection therefore holds exactly when a triangle exists, with
witness `{t,a}`. Each label lies in one selector of depth `s-h`.

**Size.** Add `p` dummy vertices to each of `B` and `C`, with all edges
from dummy `B` to dummy `C`, no edges from `A` to dummy `B`, and no
edges from dummy `C` to `A`. This adds no triangle or label. Copying
these layers retains `Theta(2^h p^2)` edges even when the original graph
is empty. All other vertices, edges and `p(s-h)` guard incidences fit within
the same bound. Thus `2^mu G=Theta(p^3)`. A detector running in
`O((2^mu G)^{1-epsilon})` would detect triangles in
`O(p^{3-3epsilon}+2^h p^2)`. Take `mu=floor(lambda s)` and `h=s-mu`;
construction takes `O(p^{3-lambda})`. Both terms are truly subcubic for
fixed positive `epsilon,lambda`. Padding an arbitrary source graph to a
power-of-two part size changes sizes by at most a constant factor. ∎

At `mu=s` this is Theorem 5.1; at `mu=0` the instance has no guards and
size `Theta(p^3)`. Proposition 5.7 excludes a fixed exponent saving from
`2^mu G` on these instances when `mu=lambda log_2 n+O(1)` with fixed
`0<lambda<=1`. It does not give a matching upper bound, exclude
logarithmic savings, or give a superlinear lower bound for constant `mu`.

A *selector* for `n>=1` entries is a finite directed graph with a root,
a disjoint set of internal vertices, and distinct terminal sinks `E_1,...,E_n`, together with sets
`C_1,...,C_n` of internal vertices, such that deleting `C_j` leaves exactly
`E_j` reachable among the terminals. Its *multiplicity* is `max_j |C_j|`.
In a guarded DAG, `C_j` is the set of guard vertices containing label
`j`. Let `N(mu)` be the maximum number of entries selectable with
multiplicity at most `mu`.

For every finite directed graph with a designated source and integer
`k>=1`, there is a subgraph preserving source reachability after every
set of at most `k` edge failures, with indegree at most `2^k` at every
vertex [BCR18, Theorem 2]. The per-vertex bound is the input used below.

The upper bound in Proposition 5.8 is not new. For arc deletions it is
the improved anti-isolation lemma of [HSW25, Lemma 2.3], which sharpens
the bound `(mu+1)4^{mu+1}` of [PW18, Lemma 4.3] using the cut structure of
[BCR18]. We give the short derivation from the preserver theorem because
it covers the vertex form and terminal conventions used here.

<a id="statement-5-8"></a>

**Proposition 5.8 (exact selector capacity).** For every integer `mu>=0`,

\[
 N(\mu)=2^\mu.
\]

The upper bound holds for arbitrary finite directed selectors, including
selectors with cycles.

*Proof.* With no deletions at most one terminal can be individually
selected, and a root-to-terminal edge attains this bound. For `mu>=1`,
split each internal vertex `v` into `v_in -> v_out`, redirecting its
incoming and outgoing arcs. Keep the root and terminals unsplit. Each
cut `C_j` becomes at most `mu` failed split edges.

Add a fresh sink `z` and precisely the arcs `E_j -> z`. The preserver
theorem gives a subgraph `H` with indegree at `z` at most `2^mu`.
Every terminal arc must remain in `H`: after the failures for `C_j`, the
original graph reaches `z`, and any surviving path to it enters from
its only reachable terminal `E_j`. A subgraph cannot make another
terminal reachable. Hence all `n` arcs remain and `n<=2^mu`.

A complete binary tree of height `mu` attains equality. Subdivide each
child arc by an internal guard vertex. For a selected leaf, delete the
sibling-branch guard at each level. These `mu` internal deletions isolate
that leaf without deleting a terminal. ∎

The weighted budgets and minimum total guard cost that follow from this
capacity bound are proved in Theorem C.1. They constrain the selector
construction, rather than the two-failure algorithm.

## 6. Applications and Open Questions

### 6.1. Shared Boolean Outputs

Guarded expressions also support falsification queries on nonempty label
sets. A single healthy-one output has a linear-time dual-Horn algorithm
(Theorem A.1). With many outputs sharing a subgraph, the listed Hitting
Set Conjecture instead excludes a fixed saving from a quadratic exponent
(Theorem D.1). Corollary D.2 combines this with the clique regimes.
Appendix D gives the complete reduction; this falsification contract is
distinct from the reachability contract of Section 3.

### 6.2. Priority-Controller Fault Detection

The graph problem models controller detection through an exact interface.
The imported results are [Sha26A, Theorem 4.1] and [Sha26A, Theorem 5.1];
no other controller result is used here. We state the interface so that
the role of the physical circuit is explicit.

The controller has `n` eligibility channels, `b>=1` request buses, a
target channel `t`, and a nonempty set of drivers distinct from `t`.
Its bridge fault has drive value zero or one. For drive zero there is no
detecting input. The cited interface also distinguishes two cases by
the first-bus selector flag, one Boolean signal in each circuit copy:
if these flags agree on the same primary input, the qualifier vectors
are equal; if they differ under drive one, the
healthy eligibility set is `{t}`, and the faulty eligibility sets range
over exactly

\[
\{K\subseteq[n]:t\in K\}\quad(b=1),\qquad
\{K\subseteq[n]:K\ne\varnothing\}\quad(b\ge2).
\]

Every such set has an explicit primary-input realization. Thus with
supplied guarded outputs the physical detection question is exactly the
graph detection query with `Q={t}` for one bus and `Q` empty for two or
more buses. A graph witness `K` becomes a primary test input by that
realization. The imported decision rule gives `O((n+q)G)` graph work;
writing a primary test or full native-CNF model adds `O(N)` time and
storage, where `N` counts native variables and literal occurrences.
Theorem A.1 proves the graph decision rule locally.

For a native CNF, *supplied circuit roles* means gate and wire annotations
identifying the healthy and faulty copies, primary inputs, channel and
bus indices, target and driver labels, and guarded decoder roots. These
annotations have `O(N)` size and allow the encoded circuit and its
outputs to be read directly. Recovering them from an unannotated CNF is
not part of this transfer.

<a id="statement-6-1"></a>

**Corollary 6.1 (controller and native-encoding transfer).** All graph
algorithms in this paper apply to supplied guarded controller outputs. The
triangle, clique, Hitting Set, multiplicity, and directed-cycle lower
bounds hold with one bus, one driver, and the output polarity specified
in each theorem. Their stated exponent exclusions also hold in native
size `N` with circuit roles supplied. The tuple and nearly linear label
promises can be retained with `N=Theta(G)`.

*Proof.* In each reduction choose its designated auxiliary label as the single
driver and use a drive-one fault. The ordinary detecting sets `{t,i}`,
the Hitting Set sets `{t} union B_j`, and every other admissible witness
are realized by the imported reachable-set theorem. The driver may be
ineligible; the physical image imposes no requirement that it be selected.
Conversely every physical detecting input yields an admissible graph
witness, so every reduction preserves both YES and NO answers. The
essentiality comparisons in Corollary 5.6 remain in the reachable one-bus
image and differ in exactly the tested eligibility coordinate.

For native CNFs, realize every OR by a binary tree and every guard by a
chain of binary guarded ANDs. Use the complete Tseitin clauses for each
gate, specifying both directions of its Boolean equality, and retain
shared nodes within each healthy or faulty copy. The one-bus selector,
drive interface, and output-difference OR tree add `O(n+q)` gates. Every
binary gate contributes only a constant number of variables and literal
occurrences. Hence `N=O(G)`, with roles known, and a topological evaluation
lifts a graph witness to the native variables in `O(N)` time. For the
Hitting Set construction, the shared subgraph `U` is copied once in each
circuit copy and then referenced by all output roots; this gives
`N=O(d+r+s+sum_i|A_i|+sum_j(d-|B_j|))`.

For the fixed tuple regimes, retain the unobserved chain of `b^{c+1}`
binary OR gates used in Theorem 5.3. Encode it with complete unsimplified
gate blocks. Every gate has a fresh native variable in each circuit
copy, so `N=Theta(G)`, preserving the claimed label-to-size ratio. For
the cycle reduction, an additional unobserved binary chain of the
unpadded representation size, if needed, gives the same constant-factor
size relation after label padding. The fresh labels guarded at the root
in Corollary 5.6 preserve its essentiality argument; unobserved chain
gates do not change that root. The trade-off construction's stored OR
incidences likewise become binary gates of total size `Theta(G)`.
All transformations are linear in their output representations. They
therefore preserve the source-time contradictions, including their
construction costs. ∎

### 6.3. Remaining Time and Space Questions

For a fixed interior ratio
`n=Theta(G^gamma)`, `0<gamma<1`, the combinatorial hypotheses exclude a
fixed exponent saving from `nG`, while general word-RAM algorithms have
the smaller algebraic lower bound in the balanced regimes
`gamma=c/(c+1)`, for every integer `c>=2`, of Proposition 5.4. The gap
to the `O(nG)` upper bound remains. The cycle theorem
settles the quadratic worst-case exponent on its declared
`n=Theta(G)` promise and does not settle those fixed interior ratios.

<a id="statement-6-2"></a>

**Question 6.2 (sensitivity-parameterized detection).** Can healthy-zero
detection be solved combinatorially in `Õ(2^mu G)` total time, including
preprocessing, where `mu` is the maximum candidate-label multiplicity
after the common forced-target deletion? Equivalently, can the
existential DAG batch problem be solved in `Õ(2^mu S)` time?

Graph search and ordinary dominators give linear time at multiplicities
zero and one. For two failures, depth, a constructed small-width chain partition,
a supplied chain partition, or a recognized common cut anchor can yield
near-linear time. The unrestricted
threshold bound remains larger. Canonical summaries give an equivalent
list of constant-size equality questions (Proposition B.3), but their
joint discovery cost is not bounded near-linearly. Neither a compact
oracle nor the selector capacity theorem supplies the missing total-time
algorithm.

There is also a distinct space question for the threshold algorithm:
can its `Õ(S+(V+E)sqrt(q_b))` time be retained with `Õ(S)` working words
on arbitrary DAGs? A logarithmic threshold gives near-linear space with
a larger time bound. Exact historical-set sharing preserves the
square-root-threshold time, but Proposition 3.3 only gives
`Õ(S+Lambda)` words. The representation examples show both linear
payload on a repeated-set family and `Theta(S^(3/2))` payload for
full-array sharing on a partial-overlap family. These are statements
about that representation, not all-algorithm space lower bounds.
A different representation must account for equality discovery,
filtering, reconstruction and enumeration within the same time bound.

## 7. Executable Checks

The implementations are checked against exhaustive qualifier-set search
or ordinary breadth-first search on finite DAGs. A standalone checker
implements the definitions and Algorithm 1 without importing project
modules. The two-failure prototypes separately test localized dominator
updates and the streamed last-failure construction, including multiple
targets, failed sources, empty queries and invalid chain partitions.

The [validation supplement](paper-b-validation-v1.1-draft.md) gives the exact test
populations, recorded results, source hashes and replay commands. The
localized prototype tests the supplied-independent-tree kernel; its test
driver finds those trees by finite search. The streamed prototype
records live coordinate entries and graph visits separately, so its
storage checks also expose the full graph passes in the time bound.
The two-surrogate prototype checks topological replacement and streamed
residual queries against independent deletion BFS. A separate checker
tests canonical uniqueness, composition and the listed-query equality.
The common-anchor checker tests every nonempty failure-pair batch on
every initially source-reachable ordered DAG through five vertices,
then larger seeded instances. It compares the intersection, exact
recognition and every target membership with independent BFS. Scaled
crossing-pair and skip-DAG controls record all kernel edge visits and a
normalization pass budget; a rejected-group control remains unresolved
by the kernel. Sorting and LCA costs are charged separately in the proof.
The threshold checker tests the proposed-anchor eligibility predicate,
arbitrary-target residual answers, and the complete existential scheduler
on initially reachable, topologically numbered DAGs. It counts completed
kernels, every pulled entry and all target examinations. The exact-sharing
checker adds deterministic dictionary checks, repeated-set families,
partial-overlap controls, and an original target outside the chosen
anchor's cut. The validation supplement states these prototypes' input
preconditions separately from the theorem's general normalization step.
These are logical counters, not measurements of process memory. All
recorded comparisons pass. The finite checks concern implementations and
small instances; the proofs establish the asymptotic bounds, conditional
on the named hypotheses where applicable.

The all-query threshold implementation is separately compared with deletion
reachability on complete answer vectors. Constructed-width checks validate
the generated chain partitions before using the streamed solver, and
weighted-cover checks compare the returned cover with exact small optima.
Their populations and source identities are in the validation supplement;
these are finite implementation checks, not proofs of the asymptotic bounds.

## A. Baseline Algorithms and Bound Comparison

The following algorithms supply the comparison points used in the main
text. Their different output contracts and machine models are retained
in the final table.

### A.1. Dual-Horn Falsification and the Baseline

For healthy-one roots, use a different description. Introduce an activity
variable `a_v` for each nonterminal vertex; a terminal's activity is its
label variable `h_i`. A *dual-Horn* clause has at most one negative literal.
The following clauses are dual-Horn:

```
not a_u OR a_v                         for every child u of an OR vertex v;
not a_u OR OR_{j in B} h_j OR a_v       for guard v with child u and set B;
not a_v                               for a zero vertex v;
not a_root;  OR_i h_i;  h_t if Q={t}.
```

**Algorithm 1 (DETECT).**

```
input : a guarded DAG with roots F_1,...,F_q, labels [n], target t, Q
output: YES with admissible K changing an output, or NO

1  Evaluate c_k = F_k({t}) for every output.
2  For each i != t, if at least one c_k is zero:
3      Evaluate all roots on Q union {i}.
4      If some healthy-zero root is true, return this set.
5  For each k with c_k = 1:
6      Construct the dual-Horn system above for root k.
7      If it has a greatest model M, return {i : M(h_i)=1}.
8  Return NO.
```

<a id="statement-A-1"></a>

**Theorem A.1 (baseline decision and witness).** Algorithm 1 decides the
detection query and constructs a qualifier-set witness in `O((n+q)G)`
time and `O(G)` working words. A single healthy-one output takes `O(G)`
time.

*Proof.* Lemma 2.1 proves the healthy-zero part. For a healthy-one output,
the dual-Horn system projects exactly to admissible `h` with root value
zero. If evaluation gives zero, assigning each activity its evaluated
value satisfies every clause. Conversely, under any model, topological
induction shows that every vertex evaluated true has true activity:
this holds at terminals, follows from the child implication at OR
vertices, and follows from the guard clause when all guard labels are
false. The root unit therefore forces evaluated root zero. The positive
clause imposes nonemptiness, and the target unit imposes `Q` when needed.
Dual-Horn satisfiability and its greatest model are found in linear time
by downward propagation from the all-true assignment [DG84]. There are
at most `n-1` graph evaluations and `q` such passes, with reusable linear
working arrays. If the only output is healthy one, the evaluation loop
is skipped. ∎

### A.2. Blocked Bitsets

<a id="statement-A-2"></a>

**Proposition A.2 (bitset supports).** For a shared guarded DAG, the
healthy-zero part of Algorithm 1 can be performed in
`O(G ceil(n/w))` word operations and `O(G)` working words, where a
machine word contains `w` bits. The healthy-one part still costs at most
`O(qG)` time and uses the same linear working space.

*Proof.* Define the support `S_v` of each vertex by

```
S_0 = empty;       S_{h_i} = {i};
S_OR = union of child supports;
S_guard = S_child minus B,
          or empty if Q={t} and t belongs to B.
```

A surviving index describes a path to a terminal whose guards avoid that
index and, when needed, the target. At a healthy-zero root, any true path
on `{i,t}` must end at `h_i`: a path ending at `h_t` would already be true
at the healthy singleton. Thus a nonempty support is equivalent to a
detecting small set for this root. When `Q` is empty, use the singleton
directly. Scan the healthy-zero root supports and return any surviving
index; if none survives, apply the dual-Horn rule to the healthy-one roots.

Compute these supports in blocks to obtain the stated space bound.
Split the labels into `ceil(n/w)` blocks of at most `w` labels, and bucket
the guard incidences by block once, in `O(G)` time and space. During this
scan also mark the guard vertices meeting `Q`, so their supports are zero
in every block. Run one bottom-up pass per block, keeping a single word
per vertex for that block's labels. A pass costs `O(V+E)` plus the guard
incidences in its block; scanning the output roots costs `O(q)` per pass.
Summing gives `O(G ceil(n/w))` word operations. The buckets, flags,
topological order, and one word per vertex occupy `O(G)` words, and the
working arrays are reused for the dual-Horn computations. Bit operations
are charged by word length, without treating an arbitrary-length integer
as one constant-time operation. ∎

### A.3. Algebraic Updates

<a id="statement-A-3"></a>

**Proposition A.3 (algebraic healthy-zero algorithm).** For one
healthy-zero output, delete guard vertices containing `t` when `Q={t}`, returning NO if the root is deleted. Let `V` be the remaining vertex
count, `k_i` the number of remaining guard vertices containing label `i`,
`l_i` its number of terminals, and `kbar_i=max(1,k_i)`. Detection is decided
by a Monte Carlo algorithm with one-sided error in

\[
 \tilde O\!\Bigl(G+V^{\omega}
       +\sum_{i\ne t}\min\{G,\;\bar k_i^2+\bar k_i l_i\}\Bigr)
\]

time and `O(G+V^2)` words of space. A positive answer is always correct
and comes with a qualifier-set witness. A healthy-one output is handled
separately in `O(G)` time by its greatest-model computation.

*Proof.* This is a fixed-source DAG specialization of the matrix-update
method in [BS19, Theorem 1.2 and Section 4.2]. Reading the graph and guard
lists costs `O(G)`. Order the remaining vertices topologically, assign
independent uniform field weights to its edges, and let `W` be the weighted
adjacency matrix. Compute `R=(I-W)^{-1}`. Since `W` is strictly upper
triangular, `R=I+W+...+W^{V-1}` is defined for every weight assignment;
each entry is its path-sum polynomial.

For a candidate label `i!=t`, let `S_i` be its guard vertices. If the root
lies in `S_i`, this label has no witness. Otherwise the matrix on the
undeleted vertices satisfies the exact block-inverse identity

\[
 R^{\setminus S_i}_{r,l}
   =R_{r,l}-R_{r,S_i}(R_{S_i,S_i})^{-1}R_{S_i,l}.
\]

The principal matrix `R_{S_i,S_i}` is unit upper triangular and hence
always invertible. All terminal queries have the same root `r`. There are two
ways to check label `i`:

- **Algebraic route.** With `S_i=(s_1,...,s_k)` in topological order,
  solve `a R_{S_i,S_i}=R_{r,S_i}` directly. Its unit upper triangular
  matrix gives `a_j=R_{r,s_j}-sum_{u<j} a_u R_{s_u,s_j}`. This computes
  the correction row in `O(kbar_i^2)` field operations, without forming
  the inverse. Each terminal then needs one dot product in `O(kbar_i)` operations.
- **Search route.** When this costs more than `G`, search the DAG after
  deleting `S_i` in `O(G)` time instead.

A surviving path contributes a distinct edge monomial with coefficient
one, so its path-sum polynomial is nonzero and has degree at most `V-1`.
Without a path the polynomial is identically zero. A field of size at
least `(G+2)^4` and the Schwartz–Zippel bound give inverse-polynomial
failure probability simultaneously over the at most `V` terminal queries.
Field elements have `O(log G)` bits; the displayed bound suppresses their
arithmetic factors and arbitrarily small slack in the matrix-multiplication
exponent. Every nonzero answer is a true path. One `O(G)` search retrieves
it, yielding `{t,i}` when `Q={t}` or `{i}` when `Q` is empty, and can check
the witness directly. Label `t` itself cannot witness a healthy-zero
output, since its singleton is the healthy input. Matrix storage is
`O(V^2)` words, and each correction row can be discarded after its label.
This proves the stated costs and error direction. ∎

The bound can be compared with the deterministic `O(nG)` algorithm and
the cheaper one used. Although `V<=G` gives a coarse bound in `n,G`, this
does not give a uniform improvement over `O(nG)` when `V` is large.

### A.4. Complete Bound Comparison

The algorithmic upper bounds in Table 2 are unconditional, with the stated
error guarantee for the Monte Carlo algorithm. Every conditional exclusion
means that no fixed positive saving `epsilon` exists in the stated model
and parameter regime. The two output polarities have different rows.

| Query and regime | Bound | Model or hypothesis | Result |
|---|---|---|---|
| All healthy-zero roots together | `O(G ceil(n/w))` time, `O(G)` working words | Deterministic word operations | Proposition A.2 |
| One healthy-zero root, `mu<=1` | `O(G)` time and space | Deterministic | Proposition 4.1 |
| Listed OSR batch, `mu<=2` | `O((S+Sigma(C)) log(V+2))` time, `O(S+V log(V+2))` words; `Sigma(C)<=(V+E) min{|C|,2h}` | Deterministic combinatorial | Theorem 4.3 |
| Listed OSR batch, `mu<=2`, supplied `p`-chain partition | `Õ(pS)` time, `Õ(S)` words; near-linear time for polylogarithmic `p`, at arbitrary depth | Deterministic combinatorial | Theorem 4.5 |
| Listed failure batch, `mu<=2`, reachability width `kappa` | `Õ(kappa S)` time, `Õ(S)` words, including chain discovery | Deterministic combinatorial; classical greedy cover | Corollary 4.7 |
| Listed failure batch, `mu<=2`, fixed independent trees | `O((S+OPT_c) log(V+2))` time, `O(S+V log(V+2))` words | Deterministic combinatorial; weighted cover constructed within factor two | Corollary 4.8 |
| Listed OSR batch, `mu<=2`, unrestricted DAG | `Õ(S+V^2)` time, `Õ(S)` words | Deterministic combinatorial; exponent also follows from classical local preservers | Theorem B.2 |
| Listed two-failure batch with a proper common anchor | `Õ(S)` time and words, including recognition and arbitrary target lists | Deterministic combinatorial | Theorem 3.1 |
| Unrestricted all-query two-failure batch, `tau>=1` | `Õ(S+E tau+(V+E)q_b/tau)` time, `Õ(S+V tau)` words | Deterministic combinatorial; all discovery and target aggregation included | Theorem 3.2 |
| Same threshold algorithm with exact set sharing | Same time, `Õ(S+Lambda)` words; `Lambda` can be superlinear | Deterministic exact equality; representation-dependent space | Proposition 3.3 |
| One healthy-zero root, residual `V,k_i,l_i` | `Õ(G+V^omega+sum_{i!=t} min{G,kbar_i^2+kbar_i l_i})` | Monte Carlo, one-sided error; `kbar_i=max(1,k_i)` | Proposition A.3 |
| One healthy-zero root, each fixed `0<gamma<1`, `n=Theta(G^gamma)` | No `O((nG)^{1-epsilon})` | Combinatorial `k`-Clique, with fixed `k` selected by `gamma` | Theorem 5.3 |
| Shared healthy-one roots, unrestricted `q` | No `O(G^{2-epsilon})` | Listed Hitting Set; deterministic word RAM | Theorem D.1 |
| Shared roots, fixed `n=G^{gamma+o(1)}`, `q=G^{beta+o(1)}`, `gamma,beta in (0,1)` | No `O(((n+q)G)^{1-epsilon})` | Combinatorial clique and listed Hitting Set | Corollary D.2 |
| One healthy-zero root, `n=Theta(G^{c/(c+1)})` | No `O((nG)^{omega/3-epsilon})` | Algebraic clique conjecture (Section 5.2); every fixed integer `c>=2` | Proposition 5.4 |
| One healthy-zero root, declared `n=Theta(G)`, `mu=O(log n)` | No `O(G^{2-epsilon})` | Deterministic `k`-Cycle; general word RAM | Theorem 5.5 |
| One healthy-zero root, `mu=lambda log_2 n+O(1)`, fixed `0<lambda<=1` | No `O((2^mu G)^{1-epsilon})` | Combinatorial triangle | Proposition 5.7 |

Table: Algorithmic bounds, parameter regimes and required hypotheses. The result column identifies each supporting statement.

Conditional word-RAM bounds use logarithmic word size. A *combinatorial*
algorithm is understood in the convention of the corresponding source
hypothesis, excluding fast algebraic matrix multiplication. Unless a
randomized algorithm is expressly stated, the conditional consequences
use deterministic hypotheses; randomized consequences require the
corresponding randomized hypotheses. The algebraic upper bound thus
coexists with combinatorial lower bounds. The exact hypotheses are stated
beside their reductions in Section 5 and Appendix D.

## B. Canonical Summaries and Sparse Shortcuts

The algorithms of Section 4 exploit depth or a supplied chain partition.
A different reduction bounds the number of incoming arcs while retaining
the original vertices and their failure identities. It uses classical
farthest minimum cuts and immediate double-vertex dominators
[BCR18, Sections 3--4; TD15, Sections 5--6]. We state the resulting summary
property explicitly, including failures of the summarized vertices.

Let `q_b` be the number of listed queries and `M=sum_i |T_i|`.
Let `D` be the retained rooted DAG, and allow every set `F` of at most
two vertices, including the root. For a set `P` of vertices define
\[
 \Phi_P(F)=[P\cap\operatorname{Reach}_{D-F}(r)\ne\varnothing].
\]
A summary is *reduced* if it has at most two members and neither member
of a pair dominates the other. Its members may lie outside `P`.

<a id="statement-B-1"></a>

**Lemma B.1 (canonical two-vertex summary).** Every `P` has a unique
reduced summary `C(P)` satisfying \(\Phi_{C(P)}(F)=\Phi_P(F)\) for every
`|F|<=2`. With the ordinary dominator tree available, it can be found
in `O(V+E+|P|)` time using constant-time tree-LCA queries.

*Proof.* Set `C(empty)=empty`. Otherwise let `d` be the dominator-tree
LCA of `P`. Every root-to-`P` path contains `d`. If `d` belongs to `P`,
then `{d}` is an exact summary, including when `d` fails.

Suppose `d` is not in `P`. Protect `d`, make vertices of `P` deletable,
and find the minimum number `lambda` of other vertices separating `d`
from all of `P`. There is no one-vertex separator: such a vertex would
be a common dominator of `P` strictly below `d`. If `lambda>=3`, two
failures cannot disconnect all of `P` while leaving `d` reachable, so
`{d}` is again exact.

If `lambda=2`, choose the farthest minimum separator `C`, whose
source-reachable side is inclusion-maximal. The existence of this
maximum side is the usual minimum-cut lattice property after vertex
splitting. Every vertex of `C` lies on a `d`-to-`P` path and is dominated
by `d`: a path reaching it without `d`, followed by the suffix to `P`,
would contradict that `d` dominates `P`. Acyclicity ensures this suffix
does not return to `d`.

If no member of `C` is reachable after failures `F`, no member of `P`
is reachable, since every root-to-`P` path meets `C`. Conversely suppose
`P` is unreachable. If `d` is unreachable, so is `C`. Otherwise the at
most two failures form a minimum `d`-to-`P` separator. Its reachable
side is contained in that of the farthest separator, so its deletion
also makes every member of `C` unreachable. These inclusions can be
read in the vertex-split network, where a failed vertex removes its
unit-capacity gate edge. This proves equality of the two predicates.
The separator is reduced: if one member dominated the other, deleting
that member alone would separate `P`.

For uniqueness, suppose distinct reduced sets `X,Y` have equal
predicates. Choose the earliest vertex `x` of their symmetric difference
in a topological order, taking `x` in `X`. At `F=Y`, vertex `x` must be
unreachable. Every vertex of `Y` outside `X` occurs later than `x`, so
all paths to `x` meet `X intersect Y`. That intersection has at most
one member. An empty intersection contradicts initial reachability;
a singleton would dominate `x`, contradicting that `X` is reduced.
Thus `X=Y`.

For construction, split each deletable vertex with a capacity-one
edge, give the protected source and transit edges capacity three, and
connect the split exits of the ports to a protected sink. Stop after
three unit augmentations. If only two are possible, reverse residual
reachability from the sink identifies the farthest minimum cut. There
are `O(V+E+|P|)` network entries and at most three graph scans for
augmentation, plus the final residual scan. The LCA computation costs
`O(|P|)` with a static constant-time LCA index. ∎

The cut argument is a vertex-failure formulation of the classical
immediate-double-dominator structure; uniqueness alone is not claimed
as new. The full failure predicate makes the summary suitable for
replacement inside a topological computation.

<a id="statement-B-2"></a>

**Theorem B.2 (same-vertex sparsification and a generic batch bound).**
A rooted DAG has a DAG `H` on the same reachable vertices, with at most
two incoming arcs per nonroot vertex, such that root reachability after
every set of at most two vertex failures agrees in `D` and `H`.
The arcs of `H` may be shortcuts. It can be constructed in
`O(V^2+(V+E)log(V+2))` time and `O(S+V log(V+2))` working words.
Every query in a listed two-failure batch can then be answered in
`Õ(S+V^2)` total time and `Õ(S)` working words, including all target
incidences.

*Proof.* Process the vertices in a topological order, starting with `r`.
For the next vertex `v`, let `P_v` be its original predecessors. Compute
`C(P_v)` in the already constructed prefix of `H`, and add the arcs
`x->v` for its at most two members `x`. All such vertices precede `v`.
For any failures `F`, a surviving `v` is reachable exactly when at least
one predecessor is reachable. Lemma B.1 and induction on the prefix
therefore preserve its reachability; a failed `v` is absent in both
graphs. This holds simultaneously for every `F` with `|F|<=2`.

Single-failure preservation implies that the ordinary dominator tree
of a prefix is unchanged. It can be obtained from the original DAG;
later vertices cannot occur on a path to a prefix vertex. Each prefix
has at most `2V` arcs. Thus its bounded-flow computation scans `O(V)`
network entries, in addition to reading `P_v`. Summing over at most
`V` vertices gives `O(V^2+E)` work for the cut computations. Computing
ordinary dominators by predecessor LCAs in topological order, with
binary lifting, takes `O((V+E)log(V+2))` time and `O(V log(V+2))`
words. The same index can serve the port LCAs, adding `O(E log(V+2))`
work. Only one flow network is retained at a time.

Group the queries with two distinct nonroot failures by their earlier
failed vertex `a`. In `H-a`, compute the reachable vertices and their
dominator tree. The second failure `b` disconnects a surviving target
`t` exactly when `b` dominates `t` in this residual graph. Euler intervals
answer this test in constant time. Each residual graph has `O(V)` arcs,
so one group's preprocessing takes `O(V log(V+2))` time; there are at
most `V` groups. Stream the residual trees. Queries with zero or one
failure use the original reachability and dominator data; queries
failing the source are NO. Targets equal to `a` are absent, and targets
equal to `b` are rejected by reflexive dominance; empty target lists give NO. Each listed target is inspected
at most once in its query's group, for `O(q_b+M)` aggregation, where
`M=sum_i |T_i|`. Reading, sorting and grouping cost `Õ(S)`. An original-
graph search after a positive answer retrieves a witness if needed. ∎

The generic `Õ(S+V^2)` exponent also follows from classical preserver
machinery. Apply the local `k=2` incoming-edge reduction of [BCR18,
Algorithm 1 and Section 3.1] to each new vertex of a topological
prefix, splitting vertices into gate edges and including the local
algorithm's linear-time degree normalization. It keeps at most four
incoming original arcs. Before insertion the prefix has `O(V)` arcs;
adding the new predecessor list gives `O(V+|P_v|)` entries. Thus the
local calls cost `O(V^2+E)` in total. The edge-failure guarantee includes the gate edges
representing failed vertices; a failed new vertex is absent regardless
of its retained incoming arcs. Topological induction gives a
same-vertex original-edge subgraph, after which the same streamed
dominator evaluation applies. Theorem B.2 gives two incoming arcs by
allowing shortcuts; its batch exponent is not claimed as a separation
from this classical construction.

<a id="statement-B-3"></a>

**Proposition B.3 (listed queries as summary equalities).** Canonical
summaries satisfy, for vertex sets `P_1,P_2`,
\[
 C(P_1\cup P_2)=C(C(P_1)\cup C(P_2)).
\]
For every `|F|<=2` and target set `T`,
\[
 T\cap\operatorname{Reach}_{D-F}(r)=\varnothing
 \quad\Longleftrightarrow\quad C(F\cup T)=C(F).
\]
Consequently a listed batch reduces in `O(S)` bookkeeping to at most
`M` nonadaptive summary computations on sets of at most three vertices,
followed by `O(q_b+M)` comparisons and Boolean aggregation. Ordinary
dominator preprocessing suffices to compute all the right-hand summaries
`C(F)`.

*Proof.* The predicates of a union and of the union of its summaries
agree under every allowed failure set. Uniqueness in Lemma B.1 gives
the first identity. If `T` is dead under `F`, every root-to-`t` path,
for `t` in `T`, meets `F`. Under any other failures `X`, a surviving
path to `t` therefore supplies a surviving member of `F`. Thus
`Phi_T(X)` implies `Phi_F(X)`, proving equality of the union predicates
and hence of their canonical summaries. Conversely evaluate that
equality at `X=F`: no member of `F` survives, so no target survives.
The empty sets and a failed root obey the same argument.

For each original incidence `(F,t)`, request `C(F union {t})` and compare
it with `C(F)`. The query is YES iff at least one comparison differs.
The requests are determined by the input before any answers are known.
For a two-element `F`, its canonical summary is the pair itself unless
one member dominates the other, in which case keep only the dominating
member. Euler ancestry therefore computes `C(F)` in constant time. ∎

This formulation combines cut discovery and residual membership in one
operation; it does not make that operation cheap. Applying Lemma B.1
separately to the `M` listed triples costs `O(M(V+E))` after ordinary
dominator preprocessing. A near-linear algorithm for the listed
summary equalities would suffice for Question 6.2 at multiplicity two;
it need not compute full summaries for unlisted sets. Neither a
constant summary size nor memoization alone bounds the necessary edge
scans. The generic bound of Theorem B.2 remains quadratic on sparse
DAGs and is incomparable with the parameter-dependent bounds of
Theorems 4.3 and 4.5.

## C. Weighted Selector Budgets

Proposition 5.8 bounds the number of terminals isolated by a uniform
failure budget. Attaching private binary trees converts that uniform
bound into the following weighted form.

<a id="statement-C-1"></a>

**Theorem C.1 (Kraft inequality and optimal guard cost).** Every selector
satisfies

\[
 \sum_{j=1}^{n}2^{-|C_j|}\le 1.
\]

The minimum maximum multiplicity is `ceil(log_2 n)`. With
`h=floor(log_2 n)`, the exact minimum total incidence cost is

\[
 \min\sum_j |C_j|=n(h+2)-2^{h+1}.
\]

Nonnegative integer budgets `c_1,...,c_n` are simultaneously achievable
with `|C_j|<=c_j` exactly when `sum_j 2^{-c_j}<=1`.

*Proof.* Set `c_j=|C_j|` and `K=max_j c_j`. Attach at `E_j` a private
complete binary selector of depth `K-c_j`, replacing that terminal by
`2^{K-c_j}` new terminals. To isolate one of them, delete `C_j` and the
sibling-branch guards on its private path. The two sets are disjoint and
have total size `K`. Every other original terminal, and every terminal
attached to it, is unreachable. Subdivision keeps terminal sinks out of
the cut sets; depth zero leaves the original terminal in place.

The enlarged selector has `sum_j 2^{K-c_j}` terminals and multiplicity
at most `K`. Proposition 5.8 bounds this sum by `2^K`, proving Kraft
after division. This finite counting construction is not claimed to have
polynomial size in binary-encoded budgets.

The maximum-multiplicity bound follows directly and a balanced tree
attains it. For the total cost, for every nonnegative integer `c`,

\[
 2^{-c}\ge 2^{-h}\left(1+\frac{h-c}{2}\right).
\]

Equality holds at `c=h,h+1`. At `c>=h+2` the right side is nonpositive;
at `c<h`, use `2^{h-c}>=1+(h-c)/2`. Summing and applying Kraft gives
`sum_j c_j >= n(h+2)-2^{h+1}`. Start with `2^h` leaves at depth `h` and
split `n-2^h` of them into sibling pairs. This attains the bound.

For the budget vector, necessity follows from Kraft and `|C_j|<=c_j`.
For sufficiency, sort budgets increasingly and allocate consecutive
dyadic intervals of lengths `2^{-c_j}` in `[0,1)`. Earlier endpoints are
multiples of each later length, and the total length prevents overflow.
Their binary words form a prefix-free code. Its prefix tree, with child
arcs subdivided by guards, isolates each entry using at most `c_j`
sibling deletions. The one-entry zero-budget case uses a direct edge. ∎

DAG sharing cannot improve optimal maximum multiplicity or total guard
incidences over the binary selector tree. Thus the balanced selectors in
the triangle and clique reductions are optimal in these measures. The
capacity bound is known [HSW25, Lemma 2.3] and is a corollary of [BCR18].
The weighted inequality, budget characterization and cost formula are
elementary consequences of it; their priority is unestablished.

These are capacity and cost statements. They do not supply Question 6.2's `Õ(2^mu G)` algorithm for arbitrary sensitivity batches.

In a deletion selector that can isolate each of `n` entries, Proposition 5.8 forces the worst-case deletion budget to be at least `ceil(log_2 n)`;
the sibling deletions in [AW14, Lemma 8.3] attain this order, so this
selection technique alone cannot use a constant deletion budget for
unbounded `n`. A single inserted edge from an otherwise isolated source
can instead choose any specified entry [AW14, Lemma 8.2; HLNV17,
Appendix A.6 and Table 2]; this difference concerns these selection
gadgets and does not rule out other constant-deletion reductions.

## D. Shared-Output Falsification

For a healthy-one root, a witness falsifies the output on an admissible
set. Sharing one such computation across many roots leads to a Hitting
Set reduction. This supplies the output-count part of the joint bound.

The separate greatest-model computations have a conditional barrier
to a uniform saving in the exponent when output roots share subgraphs. The source problem is *listed
Hitting Set*: given two nonempty lists `A_1,...,A_r` and `B_1,...,B_s` of
subsets of `[d]`, decide whether some listed `B_j` intersects every `A_i`.
The candidates are supplied explicitly; this is distinct from finding a
minimum hitting set among all subsets.

We use the Hitting Set Conjecture of [AVWW16, Section 1.2]: there is no
fixed `delta>0` such that, for every constant `c>=1`, the problem with
`r=s=m` and `d=ceil(c log_2 m)` admits `O(m^{2-delta})` time.
We state the consequence for deterministic word-RAM algorithms with
logarithmic word size. A randomized consequence requires the corresponding
randomized conjecture.

<a id="statement-D-1"></a>

**Theorem D.1 (conditional quadratic exponent).** Assuming the Hitting Set
Conjecture, for every fixed `epsilon>0` there is no `O(G^{2-epsilon})`-time
algorithm for detection on explicitly supplied guarded DAGs. This holds with `Q={t}` and only healthy-one outputs. Together with Theorem A.1,
the worst-case exponent in guarded DAG size is therefore two under this
conjecture; the available upper bound uses `O(G)` working space.

*Proof.* Use labels `t,p,1,...,d`, target `t`, an unused auxiliary label `p`, and
`Q={t}`. Define one shared guarded subgraph and `s`
output roots by

\[
 U(h)=\bigvee_{i=1}^{r}
       \left(h_t\wedge\bigwedge_{u\in A_i}\neg h_u\right),
 \qquad
 F_j(h)=U(h)\vee\bigvee_{u\in[d]\setminus B_j}h_u.
\]

Each term has one live child `h_t` and only negative label guards.
The vertex `U` is stored once and referenced by every output. Since `r>=1`,
every healthy value `F_j({t})` is one, including when a requirement is empty.
An admissible qualifier set is any set containing `t`. Write its
coordinate part as `S=K intersect [d]`; the auxiliary label is irrelevant to the guarded DAG. Directly from the displayed formula,

\[
 F_j(K)=0
 \quad\Longleftrightarrow\quad
 S\subseteq B_j
 \ \text{and}\
 (\forall i)\ S\cap A_i\ne\varnothing.
\]

If such an `S` exists, then `B_j` itself intersects every requirement.
Conversely, when `B_j` intersects every requirement, choose
the admissible set `K={t} union B_j`. Thus detection is
equivalent to the listed Hitting Set decision. An empty requirement makes
every output impossible to falsify; an empty candidate cannot hit a
nonempty list of requirements. Both cases obey the same equivalence.

The construction has `n=d+2`, `q=s`, and

\[
 G=O\!\left(d+r+s+\sum_i|A_i|
                    +\sum_j(d-|B_j|)\right)
   =O((r+s)(d+1)).
\]

All repeated guard and output incidences are charged. Construction is
linear in the dense source representation plus this output size.
For `r=s=m` and `d=ceil(c log_2 m)`, we have `G=O_c(m log m)`.
If the claimed faster detector existed, choose without loss of generality
`0<epsilon<=1`; source decision would take
`O_c(m log m+(m log m)^{2-epsilon})`, which is
`O_c(m^{2-epsilon/2})`. The exponent saving is independent of `c`, contrary
to the conjecture.

Finally `n,q<=G`, so Theorem A.1 gives the asserted `O(G^2)` time and
`O(G)` working-space upper bound. ∎

This is a worst-case exponent statement. It permits logarithmic savings
and gives no space lower bound or average-case bound. A single healthy-one output still has a linear-time decision algorithm. Copying `U` separately for all outputs expands the representation
by as much as `Theta(rs d)`; that loses the reduction's small shared size.
Section 5.1 gives the distinct combinatorial barrier for one healthy-zero
output, and Section 5.2 considers general word-RAM algorithms.
The joint dependence on `n`, `q` and `G` is not characterized by Theorem D.1.

<a id="statement-D-2"></a>

**Corollary D.2 (joint bounds).** Fix reals `gamma,beta` in `(0,1)`.
Fix also `epsilon>0`. Consider shared guarded DAGs with `n=G^{gamma+o(1)}` labels and
`q=G^{beta+o(1)}` outputs. Assume the combinatorial `k`-Clique hypothesis
for `k=2ceil(gamma/(1-gamma))+1` and the Hitting Set Conjecture. Then no
combinatorial algorithm decides detection in `O(((n+q)G)^{1-epsilon})`
time. Theorem A.1's `O((n+q)G)` is therefore combinatorially optimal up to
`((n+q)G)^{o(1)}` factors in every such regime.

*Proof.* Since `(n+q)G<=2max(n,q)G`, it suffices to handle the larger term.

- **If `gamma>=beta`:** take instances of Theorem 5.3 and add constant
  zero outputs until `q=Theta(G^beta)`, choosing `q=Theta(n)` when the
  exponents are equal. Their `O(q)` cost is `o(G)`, so the parameter
  exponents are unchanged and `((n+q)G)=Theta(nG)`.
- **If `beta>gamma`:** start with a balanced `m`-by-`m` listed Hitting
  Set instance on `d=ceil(C log_2 m)` coordinates for fixed `C`.
  Partition the candidates into blocks of `s=ceil(m^beta)`, padding with
  repeated candidates if needed. For each block use all `r=m`
  requirements in Theorem D.1 and add unused labels to reach
  `n=Theta(m^gamma)`. The actual guarded DAG size is between `Omega(m)` and
  `O_C(m log m)`, which suffices for `G=m^{1+o(1)}`. Thus
  `q=G^{beta+o(1)}` and `n=G^{gamma+o(1)}`.
  Constructing every block takes `m^{2-beta+o(1)}` time. The supposed
  detector takes `m^{2-epsilon(1+beta)+o(1)}` over all blocks. Their sum
  is truly subquadratic, with an exponent saving independent of `C`,
  contradicting the Hitting Set Conjecture. ∎

## Declarations

**Funding.** No external funding was received for this research.

**Competing interests.** The author declares no competing interests.

**AI assistance.** OpenAI Codex and ChatGPT assisted with mathematical exploration and manuscript preparation. The author reviewed the AI-assisted material and takes full responsibility for the manuscript.

## References

- [ABV15] A. Abboud, A. Backurs, V. Vassilevska Williams. If the current clique algorithms are optimal, so is Valiant's parser. FOCS 2015; SIAM J. Comput. 47(6), 2018. [Author paper, Section 1](https://arxiv.org/abs/1504.01431).
- [ACPP+26] M. Ahi, K. Choudhary, S. Pande, Pushpraj, L. Saggi. Maximum-flow and minimum-cut sensitivity oracles for directed graphs. ITCS 2026. [Published paper](https://doi.org/10.4230/LIPIcs.ITCS.2026.5); [author version, Corollary 1.6 and Section 8](https://arxiv.org/html/2512.00153v1).
- [ASW26] A. Abboud, R. Safier, N. Wallheimer. Triangle Detection in H-Free Graphs. ITCS 2026, LIPIcs 362, 1:1–1:19. [Published paper, Conjecture 1](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2026.1).
- [AVWW16] A. Abboud, V. Vassilevska Williams, J. Wang. Approximation and Fixed Parameter Subquadratic Algorithms for Radius and Diameter in Sparse Graphs. SODA 2016, 377–391. [DOI](https://doi.org/10.1137/1.9781611974331.ch28); [author paper, Section 1.2](https://people.csail.mit.edu/virgi/dirRad.pdf).
- [AW14] A. Abboud, V. Vassilevska Williams. Popular conjectures imply strong lower bounds for dynamic problems. FOCS 2014. [Author paper, Lemma 8.3](https://arxiv.org/abs/1402.0054).
- [AYZ95] N. Alon, R. Yuster, U. Zwick. Color-coding. Journal of the ACM 42(4), 844–856, 1995.
- [BCR18] S. Baswana, K. Choudhary, L. Roditty. Fault-Tolerant Subgraph for Single-Source Reachability: General and Optimal. SIAM J. Comput. 47(1), 80–95, 2018. [Author paper, Theorem 2](https://web.iitd.ac.in/~keerti/Papers/k-ftrs.pdf); [DOI](https://doi.org/10.1137/16M1087643).
- [BE81] R. Bar-Yehuda, S. Even. A Linear-Time Approximation Algorithm for the Weighted Vertex Cover Problem. Journal of Algorithms 2(2), 198–203, 1981. [DOI](https://doi.org/10.1016/0196-6774(81)90020-1); [author bibliography and paper](https://csaws.cs.technion.ac.il/~reuven/lr-papers.html).
- [BGK+08] A. L. Buchsbaum, L. Georgiadis, H. Kaplan, A. Rogers, R. E. Tarjan, J. R. Westbrook. Linear-time algorithms for dominators and other path-evaluation problems. SIAM J. Comput. 38(4), 1533–1573, 2008. [Publisher article](https://doi.org/10.1137/070693217).
- [BS19] J. van den Brand, T. Saranurak. Sensitive distance and reachability oracles for large batch updates. FOCS 2019, 424–435. [Author paper, Theorem 1.2](https://arxiv.org/abs/1907.07982).
- [CCC22] D. Chakraborty, K. Chatterjee, K. Choudhary. Pairwise Reachability Oracles and Preservers Under Failures. ICALP 2022, LIPIcs 229, 35:1–35:16. [Published paper](https://doi.org/10.4230/LIPIcs.ICALP.2022.35).
- [Cho16] K. Choudhary. An optimal dual fault tolerant reachability oracle. ICALP 2016, 130:1–130:13. [Published paper](https://doi.org/10.4230/LIPIcs.ICALP.2016.130).
- [Cho17] K. Choudhary. Compact and Efficient Fault Tolerant Structures for Directed Graphs. PhD thesis, IIT Kanpur, August 2017. [Author thesis, Sections 3.4.1 and 3.5, Theorem 3.2](https://www.cse.iitk.ac.in/users/keerti/papers/thesis.pdf).
- [DG84] W. Dowling, J. Gallier. Linear-time algorithms for testing the satisfiability of propositional Horn formulae. J. Logic Programming 1(3), 1984.
- [DGR21] R. Duan, Y. Gu, H. Ren. Approximate Distance Oracles Subject to Multiple Vertex Failures. SODA 2021, 2497–2516. [Published paper](https://doi.org/10.1137/1.9781611976465.148); [full author version, Lemma 5.3 and Remark 5.4](https://arxiv.org/pdf/2002.06812v2).
- [DJVW22] M. Dalirrooyfard, C. Jin, V. Vassilevska Williams, N. Wein. Approximation algorithms and hardness for n-pairs shortest paths and all-nodes shortest cycles. FOCS 2022. [Author paper, Hypothesis 1 and Sections 2.1.1 and 4.1](https://arxiv.org/abs/2204.03076).
- [GGIKL19] L. Georgiadis, K. Giannis, G. F. Italiano, A. Karanasiou, L. Laura. Dynamic Dominators and Low-High Orders in DAGs. ESA 2019, LIPIcs 144, 50:1–50:18. [Published paper, Sections 3--4](https://doi.org/10.4230/LIPIcs.ESA.2019.50).
- [GILS16] L. Georgiadis, G. F. Italiano, L. Laura, F. Santaroni. An Experimental Study of Dynamic Dominators. arXiv:1604.02711, 2016; preliminary version, ESA 2012. [Full author version, Section 2 and Figures 1–2](https://arxiv.org/pdf/1604.02711v1).
- [GT15] L. Georgiadis, R. E. Tarjan. Dominator Tree Certification and Divergent Spanning Trees. ACM Transactions on Algorithms 12(1), 11:1–11:42, 2015. [DOI](https://doi.org/10.1145/2764913); [author version, Sections 2.3 and 4, under the title *Dominator Tree Certification and Independent Spanning Trees*](https://arxiv.org/abs/1210.8303).
- [HLNV17] M. Henzinger, A. Lincoln, S. Neumann, V. Vassilevska Williams. Conditional hardness for sensitivity problems. ITCS 2017, LIPIcs 67. [Author paper, Theorem 5 and Table 2](https://arxiv.org/abs/1703.01638).
- [HSW25] G. Hoppenworth, T. Saranurak, B. Wang. Near-Optimal Fault-Tolerant Strong Connectivity Preservers. FOCS 2025. [Published paper](https://doi.org/10.1109/FOCS63196.2025.00085); [author version, Lemma 2.3 (improved anti-isolation) and Section 6.1](https://arxiv.org/abs/2510.02562).
- [IKP21] G. F. Italiano, A. Karczmarz, N. Parotsidis. Planar Reachability Under Single Vertex or Edge Failures. arXiv:2101.02574, 2021. [Full author version, Theorem 4.1 and Section 6](https://arxiv.org/pdf/2101.02574v1).
- [KP21] Karthik C. S., M. Parter. Deterministic Replacement Path Covering. SODA 2021, 704–723. [Published paper](https://doi.org/10.1137/1.9781611976465.44); [full author version, Definition 13 and Theorem 14](https://arxiv.org/pdf/2008.05421v2).
- [KPG+18] A. Kuosmanen, T. Paavilainen, T. Gagie, R. Chikhi, A. Tomescu, V. Mäkinen. Using Minimum Path Cover to Boost Dynamic Programming on DAGs: Co-Linear Chaining Extended. arXiv:1705.08754v3, 2018. [Author version, Lemma 1 and Section 3, Observation 1 and Lemma 2](https://arxiv.org/pdf/1705.08754v3).
- [KT23] G. Kritikakis, I. G. Tollis. Fast Reachability Using DAG Decomposition. SEA 2023, LIPIcs 265, 2:1–2:17. [Published paper, Sections 4.1--4.3](https://doi.org/10.4230/LIPIcs.SEA.2023.2).
- [LT79] T. Lengauer, R. E. Tarjan. A fast algorithm for finding dominators in a flowgraph. ACM TOPLAS 1(1), 121–141, 1979.
- [PQ79] J.-C. Picard, M. Queyranne. On the structure of all minimum cuts in a network and applications. Technical report EP-R-79-15, École Polytechnique de Montréal, 1979. [Institutional full text](https://publications.polymtl.ca/5993/1/EP-R-79-15_Picard.pdf), Theorem I.
- [PP26] M. Parter, A. Petruschka. Color Fault-Tolerant Distance Preservers: Optimal Size in Conditionally Optimal Time. ICALP 2026, LIPIcs 374, 146:1–146:21. [Published paper](https://doi.org/10.4230/LIPIcs.ICALP.2026.146); [full author version, Definition 1.1 and Appendix A.3](https://arxiv.org/html/2504.17868v2).
- [PW18] M. Pilipczuk, M. Wahlström. Directed Multicut is W[1]-hard, Even for Four Terminal Pairs. ACM Transactions on Computation Theory 10(3), Article 13, 2018. [Author paper, Lemma 4.3 (anti-isolation, attributed to Marx)](https://pure.royalholloway.ac.uk/ws/files/29935159/dir_cuts.pdf). [Publication](https://doi.org/10.1145/3201775).
- [RR94] G. Ramalingam, T. Reps. An Incremental Algorithm for Maintaining the Dominator Tree of a Reducible Flowgraph. POPL 1994, 287–296. [DOI](https://doi.org/10.1145/174675.177905); [author paper, Sections 3.1 and 3.2.2](https://research.cs.wisc.edu/wpis/papers/popl94.pdf).
- [Sha26A] I. A. Shaik. Polynomial Fault Detection Without Bounded Width: Exact Reachable Sets in Priority Controllers. Version 1.1, 2026. [Released article, Theorems 4.1 and 5.1](https://doi.org/10.5281/zenodo.23589156).
- [TD15] M. Teslenko, E. Dubrova. A Linear-Time Algorithm for Finding All Double-Vertex Dominators of a Given Vertex. arXiv:1503.04994, 2015. [Author paper, Sections 8--9](https://arxiv.org/abs/1503.04994).
