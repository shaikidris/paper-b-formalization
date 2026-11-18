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
| B: graph reachability | How quickly can a single-source index for any two vertex failures be constructed on a DAG? | [Near-Linear Preprocessing for Reachability After Two Vertex Failures in Directed Acyclic Graphs](paper-b-two-failure-reachability-v1.3-draft.md) |
| C: factor representations | Which interaction graphs and shared interfaces guarantee tractability for explicit and compact guarded factors? | [Explicit and Compact Guarded Factors: Interaction Graphs and Shared Interfaces](paper-c-factor-structure.md) |

The [statement map](../../evidence/controller-paper-a-final-repairs-20261014/statement-map.md)
accounts for all 63 numbered items of the technical manuscript and identifies
the additional local statements used to make the companions self-contained.
Paper A has 41 numbered items and Paper C has 13. Paper B has nine proof-bearing statements and one open question. The [published-edition coverage map](../../paper-b-formalization/COVERAGE.md) and the [v1.3 formalization addendum](../../evidence/paper-b-log-shave-20261118/formalization-v1.3.md) identify the proof obligations for each edition. The [v1.1 concordance](../../evidence/controller-paper-b-v1.1-20261112/statement-map.json) covers the earlier, extended manuscript.

The controller interpretation in Paper B uses the physical reachable sets and primary-input realizations given by Theorem 4.1 of Paper A. [Paper A, v1.1](https://doi.org/10.5281/zenodo.23589156)

## Reading order and dependencies

Paper A supplies the physical image and witness-realization theorem
(Theorem 4.1) and the guarded decision rule (Theorem 5.1). It includes the
controller model, gate extensions, related optimization and counting
questions, and native recognition and proof arguments. Recognition,
complete native resolution arguments, and detailed validation appear in
its appendices. Its experimental comparisons report that the standard
SAT solvers were faster on the generated decision panels.

Paper B is a standalone graph paper. Theorem 1.1 builds one index for a fixed source before the failures and target are known. Sections 2–5 prove the sibling reduction, pair forest, exit transfer, and the index bounds. Corollary 1.2 returns one Boolean per target list, and Section 6 derives the healthy-zero decoder application and states the higher-sensitivity question. The [threshold companion](paper-b-threshold-companion-v1.2.md) contains the full offline threshold proof, common-anchor recognition and exact historical-set sharing.

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

The Paper B v1.3 draft gives deterministic \(O((n+m)L^2)\) preprocessing, \(O(L)\) queries and \(O(n)\) retained words for arbitrary DAGs with at most two failed vertices, where \(L=\lceil\log_2(n+2)\rceil\). Choudhary's oracle for general digraphs gives constant query time and linear retained space after O(mn) preprocessing. The [structural comparison](../../evidence/paper-b-space-20261118/exit-transfer-literature-and-paper-b.md) documents antecedents of the derived graph and cut forest. The [full-text comparison with the 2006 paper](../../evidence/paper-b-v12-adversarial-20261118/novelty.md) identifies which dominator chains its algorithm takes as input and what its query-time bound covers. The [extended v1.1 draft](paper-b-guarded-reachability-v1.1-draft.md) preserves the localized, width, weighted-cover, sparsification and higher-multiplicity results. A separate [directed-graph result](../../evidence/paper-b-space-20261118/directed-proof.md) covers cycles with an offline square-root bound.

In C, tree-CSP, 2-SAT, dual encoding, projection, and the binary-CSP
graph-class lower bound are attributed to their sources. The compact
classification concerns the specified syntactic signed graph, including
false branches, and a supplied factor representation. It does not
classify graphs after semantic simplification or combined graph-and-language
restrictions. Its graph-class necessity is conditional on ETH; its fixed
forbidden-minor alternatives are stated separately without ETH. On
subgraph-closed classes with unbounded degree, the direct star reduction
gives NP-hardness without false-branch padding.

The [exit-transfer proof review](../../evidence/paper-b-space-20261118/exit-transfer-adversarial-review.md) records the set-level test and an independent oracle comparison. The [earlier comparison](../../evidence/controller-paper-b-novelty-20261110/review.md) covers the localized and streamed-chain algorithms in the extended draft.
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
The active Paper B source is the [v1.3 draft](paper-b-two-failure-reachability-v1.3-draft.md). Its [proof and replay](../../evidence/paper-b-log-shave-20261118/proof.md) cover the preorder summaries and skew-binary jumps. The [published v1.2 source](../../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md) and its [edition checks](../../evidence/controller-paper-b-v1.2-20261118/README.md) are separately identifiable. From the project root run:

~~~sh
python3 -B evidence/paper-b-log-shave-20261118/replay.py
python3 -B evidence/controller-paper-b-v1.2-20261118/check_revision.py
python3 -B paper-b-formalization/plan.py validate
python3 -B paper-b-formalization/test_plan.py
~~~

The [v1.2 formalization tracker](../../paper-b-formalization/README.md) selects Theorems 1.1 and 4.1 against the [published edition](https://doi.org/10.5281/zenodo.24339761). The draft's sharper resource bounds have separate Lean obligations. The [published v1.0](https://doi.org/10.5281/zenodo.24142496) and the [archived v1.1 source](paper-b-guarded-reachability-v1.1-draft.md) retain their original version identities.

Paper C's assembler remains in
`evidence/controller-papers-bc-revision-20261011/`.

Paper A's source is a draft. The released version 1.1 is separately archived
at [Zenodo](https://doi.org/10.5281/zenodo.23589156). Its files and the technical
master remain unchanged by the current source assembly.
