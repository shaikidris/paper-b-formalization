# Priority-controller papers

This directory contains three companion manuscripts on controller
reachability, guarded graph queries, and factor representations. Their
shared controller framework is described in the
[long technical manuscript](../../controller-family-paper-draft.md); each
article also contains standalone statements identified in its own map.
The [SATLIB audit](../../satlib-structure-paper-draft.md) is a separate
companion.

| Article | Main question | Source draft |
|---|---|---|
| A: controller detection | Which eligibility sets can a fault produce, and when does that image admit polynomial detection? | [Polynomial Fault Detection Without Bounded Width: Exact Reachable Sets in Priority Controllers](paper-a-controller-detection.md) |
| B: guarded reachability | How do shared paths, failure multiplicity, and label count affect algorithms and conditional time bounds? | [Offline Reachability in Directed Acyclic Graphs under Vertex Failures](paper-b-guarded-reachability-v1.1-draft.md) |
| C: factor representations | Which interaction graphs and shared interfaces guarantee tractability for explicit and compact guarded factors? | [Explicit and Compact Guarded Factors: Interaction Graphs and Shared Interfaces](paper-c-factor-structure.md) |

The [statement map](../../evidence/controller-paper-a-final-repairs-20261014/statement-map.md)
accounts for all 63 numbered items of the technical manuscript and identifies
the additional local statements used to make the companions self-contained.
Paper A has 41 numbered items, the Paper B v1.1 draft has 32, and Paper C has 13. Paper B's
[concordance](../../evidence/controller-paper-b-v1.1-20261112/statement-map.json)
also records its dominator and streamed-chain algorithms, the explicit-update
obstruction, the Hamiltonian-DAG consequence, canonical summaries, sparse
shortcuts, the recognized common-anchor algorithm, the unrestricted
threshold tradeoff, and exact sharing of historical query sets. These counts include
examples, remarks and open questions; they are not counts
of new theorems. Rendered page counts are not asserted for these source
manuscripts.

Paper B cites the released version 1.1 of Paper A by its public DOI;
its application uses Theorems 4.1 and 5.1 of that version.

## Reading order and dependencies

Paper A supplies the physical image and witness-realization theorem
(Theorem 4.1) and the guarded decision rule (Theorem 5.1). It includes the
controller model, gate extensions, related optimization and counting
questions, and native recognition and proof arguments. Recognition,
complete native resolution arguments, and detailed validation appear in
its appendices. Its experimental comparisons report that the standard
SAT solvers were faster on the generated decision panels.

Paper B can be read independently as a graph paper. It defines counted
incidence size and a listed batch of reachability queries under vertex
failures. Its algorithms return every query's Boolean answer; its
guarded-detection reductions use the existential projection. It proves
the graph algorithms locally and separates
combinatorial from general word-RAM lower bounds. Its assumptions table
states the hypothesis and parameter regime for each exclusion. The
multi-root falsification question uses a separate Hitting Set reduction.
The controller interpretation appears in Section 6.2 and imports only the
specified interface from A.

Paper C defines factor satisfiability in Section 2: find a nonempty true set
containing the forced set and satisfying every factor. It proceeds from
explicit term compatibility to compact-factor obstructions and interface
algorithms, then proves the graph-class criteria. Its comparison
section distinguishes classical CSP transfers, sparse-intersection
projection, succinct-relation representations, and the particular local
head-choice and degree arguments. Controller detection is an application
of the satisfiability algorithms and a separate one-factor zero test.
Reading B is not a prerequisite for C.

## Attribution and mathematical boundaries

In B, the selector capacity bound is known prior work. The weighted
consequences are elementary and have unestablished priority. The
two-failure algorithms give near-linear total time either on
polylogarithmic-depth DAGs or, at arbitrary depth, with a supplied
polylogarithmic reachability-chain partition or polylogarithmic
reachability width. The width corollary includes chain discovery.
A weighted-cover approximation also gives the localized bound
`O((S+OPT_c) log(V+2))` for fixed independent trees. The streamed chain
algorithm uses near-linear working space for every chain count; full
graph passes and multi-target aggregation remain in its time bound.
A generic two-failure algorithm takes `Õ(S+V^2)` total time and
near-linear working space. Its two-vertex summaries use classical
double-dominator structure, and the exponent also follows by applying
classical local preservers to sparse topological prefixes. The exact
summary-equality formulation leaves collective cut discovery open.
A further algorithm recognizes a proper common anchor for all failure
pairs and answers arbitrary targets in near-linear total time. It uses
classical residual-cut and path-rank machinery; its recognition, graph
passes and target aggregation are included in the bound. The total
construction cost is bounded by a threshold schedule for arbitrary
batches, returning all query Booleans: `Õ(S+E tau+(V+E)q_b/tau)`
time and `Õ(S+V tau)` words.
The square-root threshold yields `Õ(V^(3/2))` time on sparse balanced
batches. Exact sharing gives `Õ(S+Lambda)` words at the same time bound,
where `Lambda` counts distinct retained-set payload. It can be superlinear;
near-linear space at that time remains open. Near-linear total time
without a structural restriction also remains open.
These algorithms use classical independent-tree, dominator-update, and
chain-coordinate methods. Known replacement-path covering already implies
near-linear time at polylogarithmic depth. The localized algorithm refines
the depth dependence through its weighted `Sigma(C)` bound. The chain
algorithm's contribution is the complete batch construction using the
later-failure cut and an index over original edges; streaming individual
coordinate columns is a standard implementation technique. Priority for
these precise combined bounds remains unestablished. The constant-sensitivity
question without depth or chain restrictions and general-algorithm
exponents at fixed interior label-to-size ratios remain open. Conditional bounds
retain their named hypotheses and algorithm models. The balanced algebraic
clique transfer covers every integer `c>=2` at ratio `n=Theta(G^(c/(c+1)))`.

In C, tree-CSP, 2-SAT, dual encoding, projection, and the binary-CSP
graph-class lower bound are attributed to their sources. The compact
classification concerns the specified syntactic signed graph, including
false branches, and a supplied factor representation. It does not
classify graphs after semantic simplification or combined graph-and-language
restrictions. Its graph-class necessity is conditional on ETH; its fixed
forbidden-minor alternatives are stated separately without ETH. On
subgraph-closed classes with unbounded degree, the direct star reduction
gives NP-hardness without false-branch padding.

The [focused Paper B novelty assessment](../../evidence/controller-paper-b-novelty-20261110/review.md)
compares preprocessing, target contracts, structural parameters and space
against the closest inspected primary sources. It distinguishes the two
complete algorithmic bounds from their classical ingredients and from
consequences already supplied by replacement-path covering.

Paper B's [dominator literature comparison and verification](../../evidence/controller-paper-b-dominator-integration-20261110/review.md)
identifies the classical ingredients, the exact batch bound, and the
validation scope. The [streamed-chain integration record](../../evidence/controller-paper-b-streaming-integration-20261110/review.md)
records the last-failure reduction, complete time and space accounting,
and executable checks.
The [companion review](../../evidence/controller-papers-bc-revision-20261011/review.md)
and [structural literature comparison](../../evidence/controller-papers-bc-20261011/review.md)
cover the other transfers. These focused comparisons support attribution
and positioning, not an exhaustive priority determination. None of the
articles separates P from NP.

## Source integrity and reproducibility

Paper A is assembled from a pinned source and an explicit editorial ledger:

```sh
python3 -B evidence/controller-paper-a-review-repairs-20261024/assemble_paper_a.py
python3 -B evidence/controller-paper-a-review-repairs-20261024/verify_papers.py
```

The [verification record](../../evidence/controller-paper-a-review-repairs-20261024/verification.json)
checks all 41 statement/proof blocks under the declared numbering and citation
substitutions, reference resolution, notation parsing, coverage accounting and
protected artifacts. The [statement concordance](../../evidence/controller-paper-a-review-repairs-20261024/statement-map.json)
connects the manuscript numbering to the formalization records. These checks
preserve mathematical text; they do not extend the recorded formal coverage.

The [experiment and native-proof replay supplement](../../submissions/paper-a-replay-20261024/package/README.md)
provides the exact source snapshots, generated inputs and raw results for the
35-controller scaling panel, the six-size expander panel and the native proof
compiler suite. Its commands run in a separate pinned Python environment.
The [Lean repository](https://github.com/shaikidris/priority-controller-phase1)
provides the formal source and verification contracts.

The technical master has SHA-256
`98d2d76c50fecf6e9d32b149614c8bd65c3b8b784a1d209e41c54c32f128524e`.
Its exact copy is `evidence/controller-paper-split-20261010/combined-source.md`.
The current Paper B source is an unpublished **v1.1 draft**. Its
all-query threshold theorem, constructed-width corollary and weighted-cover
corollary are assembled from a pinned source and amendment ledger:

```sh
python3 -B evidence/controller-paper-b-v1.1-20261112/assemble_revision.py --write
python3 -B evidence/controller-paper-b-v1.1-20261112/assemble_revision.py --check
python3 -B paper-b-formalization/plan.py validate
```

The [verification record](../../evidence/controller-paper-b-v1.1-20261112/verification.json)
binds all 32 numbered items, declared block changes, references and
protected artifacts. The [formalization tracker](../../paper-b-formalization/README.md)
uses this draft's vector-output contract and keeps mathematical proof
coverage separate from Lean acceptance. The
[validation supplement](paper-b-validation-v1.1-draft.md) and
[representation examples](paper-b-representation-examples-v1.1-draft.md)
state their exact test and storage scopes.

The [published v1.0 source](paper-b-guarded-reachability.md) and
[Zenodo record](https://doi.org/10.5281/zenodo.24142496) remain the public
baseline. Its PDF is not a render of the v1.1 draft. No v1.1 PDF or
publication is claimed by these source checks.
Paper C's assembler remains in
`evidence/controller-papers-bc-revision-20261011/`.

Paper A's source is a draft. The released version 1.1 is separately archived
at [Zenodo](https://doi.org/10.5281/zenodo.23589156). Its files and the technical
master remain unchanged by the current source assembly.
