# Exact set sharing in two-failure batches

This supplement gives two all-size examples for
[Proposition 3.3 of Paper B](paper-b-guarded-reachability-v1.1-draft.md#statement-3-3).
The input is a rooted DAG and a list of queries `(F_i,T_i)` with two
failed vertices per query. Write `S=V+E+q_b+M`, where `M` counts target
incidences. The threshold algorithm returns one Boolean answer per query.
Its exact-sharing variant retains one immutable array for each distinct
historical light set; `Lambda` is their total cardinality.

Both examples have only negative queries. They isolate representation
costs: no conclusion about the space needed by every algorithm follows.
Their constructors and full-solver checks are included in the
[validation supplement](paper-b-validation-v1.1-draft.md).

## A repeated-set switching family

Let `m>=16` be a power of two, put `d=log_2 m`, and use threshold
`tau=2m+2`. Start with root `r` and `q_b=m^2+2m` consecutive layers of
two vertices. Join the root to both vertices of the first layer, and
put all four arcs between consecutive layers. Query `i` fails the two
vertices of layer `i`.

After these layers place `m+1` switching levels, each with vertices
`(ell,x)` for `x in {0,...,m-1}`. Both vertices of the last failure layer
feed every vertex of level zero. Between levels `ell` and `ell+1`, put
arcs from `(ell,x)` to both `(ell+1,x)` and
`(ell+1,x xor 2^(ell mod d))`. Also attach `m^2` distinct singleton
terminal vertices directly to both vertices of the last failure layer.

For the first `m` queries use all `m` vertices of the final switching
level as targets. Call their IDs the common block `C`. The next `m`
queries each target one different final-level vertex; call their IDs
private. Each of the last `m^2` queries targets one different singleton
terminal. The counts are
\[
\begin{split}
 V&=4m^2+5m+1,\quad E=8m^2+10m-2,\\
 q_b&=m^2+2m,\quad M=2m^2+m,\quad S=15m^2+18m-1.
\end{split}
\]
Every query's failure layer separates all its targets from the root.
Neither vertex of any failure pair alone dominates a switching vertex.
At a final-level vertex the stored set is `C` plus its one private ID.
At distance `a<=d` from that level, the reachable private IDs form a
subcube of size `2^a`; exactly `m/2^a` distinct sets occur, each of size
`m+2^a`. The `a` consecutive switch dimensions are distinct, which
proves this assertion by induction. At every greater distance all
private IDs are reachable, so the same full set of `2m` IDs repeats.
All these sets are light.

The total payload of distinct switching sets is consequently
\[
 \sum_{a=0}^d \frac{m}{2^a}(m+2^a)=2m^2+md.
\]
The separate singleton terminals add `m^2` words. The first processed
vertex of the final failure layer reaches the threshold and resolves
all queries except its own layer's query; that query is discarded by
the domination test at both vertices of its layer. All preceding
failure-layer lists are empty. Thus
\[
 \Lambda=3m^2+m\log_2m=O(S).
\]
There are exactly `m^2+2m-1` distinct nonempty arrays. The dictionary
discovers their equalities by comparing IDs; no switching-coordinate
recognizer is supplied. Proposition 3.3 gives `Õ(m^3)` total time and
`Õ(S)` words, including equality discovery and the residual kernel.

## Distinct arrays with a large common block

Use the same failure layers and threshold, with any power of two
`m>=2`. Both vertices of the final failure layer feed `m^2` consumer
vertices. Merge those consumers through a binary convergence tree into
one hub. From the hub branch through a binary tree to `m` base terminals.
Each consumer also has its own distinct singleton terminal child.

Use the same query pattern: `m` common IDs target all base terminals,
`m` private IDs each target one base terminal, and `m^2` further IDs
`e_i` target the consumers' individual singleton terminals. Every
consumer has precisely the historical set
\[
 H_0\cup\{e_i\},\qquad |H_0|=2m.
\]
All queries are still active while these lists are built: each
nonterminal below the failure layers has fewer than `tau` candidates,
and a single failure does not dominate it. The consumers' `m^2` sets
are therefore distinct, light, and of size `2m+1`. The graph counts are
\[
\begin{split}
 V&=5m^2+6m-2,\quad E=9m^2+10m-6,\\
 q_b&=m^2+2m,\quad M=2m^2+m,\quad S=17m^2+19m-8.
\end{split}
\]
It follows that
\[
 \Lambda\ge m^2(2m+1)=\Theta(S^{3/2}).
\]
The last failure layer precedes every consumer, so all consumer arrays
are simultaneously available before that layer is processed in the
reverse-topological schedule. Reclaiming arrays after their last parent
uses them does not remove this peak in that schedule.

A shared common-block view can represent these particular sets compactly.
The example only refutes a universal near-linear payload bound for
full-array equality sharing. It leaves other representations, schedules
and Boolean algorithms unrestricted.
