# Validation supplement: Guarded Reachability

This supplement describes the executable checks accompanying
[Offline Reachability in Directed Acyclic Graphs under Vertex Failures](paper-b-guarded-reachability-v1.1-draft.md).
The core graph checks use standard-library Python. The clique-regime
checker also runs a native-CNF comparison and requires the `python-sat`
package with MiniSat22 and Glucose4. Recorded comparisons test finite
instances and implementation invariants; they do not certify the asymptotic
bounds, the source hypotheses, or novelty.

## All-query and constructed-parameter checks

The [revision checker](../../evidence/controller-paper-b-v1.1-20261112/check_revision.py)
compares complete original-index answer vectors with independent deletion
reachability. Its [recorded run](../../evidence/controller-paper-b-v1.1-20261112/revision-checks.json)
reports **2,779,741 answer comparisons across 7,999 threshold runs**.
It enumerates all 1,099 ordered simple DAGs through five vertices; on each,
a canonical batch contains every failure set of size at most two and every
target subset, and five thresholds are tested. The population also includes
500 seeded random batches with arbitrary sources and duplicate incidences,
each at five thresholds, and four named branch controls. This is not an
enumeration of every possible query batch.

The vector implementation records normalization positives, root arrivals,
positive and negative kernel retirements, and final active negatives.
Checks compare the entire answer vector and test measured historical-list
edge pulls, once-per-query target scans and completed-kernel counts against
the proof's accounting bounds. They exercise the published residual-kernel
implementation; they are not a BFS replacement for that kernel.

For Corollary 4.7, the same checker constructs greedy reachability-chain
partitions on all 1,099 ordered DAGs through five vertices and compares
against an independent exact minimum chain-partition computation. It checks
coverage, chain validity, assigned-vertex storage and actual discovery
vertex/edge visits. After source normalization, the generated partitions
are supplied to the streamed solver for **536,036 complete query-answer
comparisons** against deletion reachability. The test distinguishes
reachability-chain width from minimum vertex-disjoint edge-path count.

For Corollary 4.8, **5,922 weighted-cover instances** are checked against
exact optimum by subset enumeration. These comprise every undirected graph
on zero through four vertices with vertex weights in `{0,1,2}`, plus
500 seeded random graphs through nine vertices with weights from zero to
seven and duplicate listed edges. The checks verify coverage, nonnegative
residual weights, feasible edge duals, tight selected vertices and the
factor-two bound, including zero optimum. These tests use arbitrary
nonnegative weights; the correspondence with fixed-tree deletion-region
costs is proved in Corollary 4.8 and separately checked by the localized
prototype described below.

Replay from the project root using ordinary Python, without `-O`, because
these audit implementations use assertions. The command writes only the
revision's finite-check report:

```sh
python3 -B evidence/controller-paper-b-v1.1-20261112/check_revision.py
```

The report binds the checker and its imported implementation dependencies
to their source hashes. Principal source and result identities are:

| Artifact | SHA-256 |
|---|---|
| [check_revision.py](../../evidence/controller-paper-b-v1.1-20261112/check_revision.py) | `c41ac4c59385d3aed8eb69f73e0f8ca676f423c565133e4b174e530a50946ebe` |
| [all_answers.py](../../evidence/controller-paper-b-independent-assessment-20261112/all_answers.py) | `1853b4509cf42605d2c5b1f70165c8cad0a2af605dcb0ea67349d96cdf844549` |
| [check_all_answers.py](../../evidence/controller-paper-b-independent-assessment-20261112/check_all_answers.py) | `543ca657d229a0604d1c157e04c9533f147952a7dcd11f35b305973bc7b055c1` |
| [source-lock.json](../../evidence/controller-paper-b-independent-assessment-20261112/source-lock.json) | `1e43048fbdd1de052c455f7fbe87acd5604554194404b05d88a873d9e6a4e4c2` |
| [threshold_kernel.py](../../evidence/controller-paper-b-threshold-integration-20261111/threshold_kernel.py) | `419c8a3f0dfd1c642cb61ee699d73d0ea5cf8c4fd9530c29010ef16bdf7d1804` |
| [dominator_tree.py](../../evidence/controller-paper-b-threshold-integration-20261111/dominator_tree.py) | `2ccf7071a46fe1c57dd7d3b88d63d7e8d27f5b6a6c7938a0e652159ca1019ba5` |
| [check_last_failure_streaming.py](../../experiments/c432-family/check_last_failure_streaming.py) | `88b48b7a5c6091f013c86118bfe71c6a05b360eb445ec7f1b1ee4e81ef0035d0` |
| [check_shared_path_failure_batches.py](../../experiments/c432-family/check_shared_path_failure_batches.py) | `b86940079eabd1f0d5b3fc0403e836616d5b0efeb7f9ac5354109937eb894c66` |
| [revision-checks.json](../../evidence/controller-paper-b-v1.1-20261112/revision-checks.json) | `17d602b9011360f11779a1f43cce409dfd9712c6e914ccfd83b6c5f664d41bea` |

These finite checks do not establish asymptotic bounds, literature priority, or Lean certification.

## Test populations and scope

The accompanying [independent checker](../../experiments/c432-family/check_papers_bc_standalone.py)
implements the printed definitions without importing a project module.
Its Paper B component generates 700 small guarded DAG instances with a
fixed seed and compares exhaustive search over admissible qualifier sets
with Lemma 2.1 and Algorithm 1 for both choices of `Q`; it also
checks that each healthy-one greatest model is the union of all
admissible falsifying sets. The same executable contains finite checks
for the companion factor-structure article. The [recorded run](../../evidence/controller-papers-bc-revision-20261011/standalone-check/report.json)
reports PASS for all 700 Paper B instances.

The [localized dominator prototype](../../evidence/controller-localized-dominator-review-20261110/check_localized_dominators.py)
implements Theorem 4.3's difference reporting, implicit ancestor tables,
and two-failure query rules. The [finite-check record](../../evidence/controller-localized-dominator-review-20261110/check-results.json)
covers all 33,867 topologically numbered DAGs through six vertices
(10,106 initially source-reachable cases), all 2,372 independent-tree
pairs on reachable DAGs through five vertices, and 300 additional random
graphs. It reports 2,273,850 pair-target comparisons and 9,000 multi-target
queries without a mismatch. Tests also check the exact cost identity,
an empty-difference chain, and a sparse quadratic-difference example.
The test driver finds independent trees by finite search and does not
implement the fast preprocessing of [Georgiadis and Tarjan](https://doi.org/10.1145/2764913). These checks validate the
supplied-tree kernel; the asymptotic guarantee is proved in Theorem 4.3.

The [streamed-chain prototype](../../experiments/c432-family/check_last_failure_streaming.py)
implements Theorem 4.5's ordinary dominator construction, last-failure
cut, column validation, head-edge range index, and target aggregation.
Its [finite-check record](../../evidence/controller-last-failure-streaming-20261110/check-results.json)
reports 6,738,438 query comparisons against independent BFS: all 33,867
ordered DAGs through six vertices, all 460 valid graph/chain-partition
instances through four vertices, 300 seeded random DAGs, and named
regression cases. The tests include every target subset through four
vertices. At five and six vertices they use singleton, empty, full and
selected duplicate-target lists. They reject all 91 invalid partitions
of the enumerated initially source-reachable graphs. They also check the cut identity
directly 14,386 times. High-chain-count examples record the live coordinate
column and graph visits separately: storage is streamed even when the
number of visits is quadratic. These counters measure logical entries,
not process memory or solver performance.

Additional scripts cover the [failure-batch equivalence](../../experiments/c432-family/check_sensitivity_equivalence.py),
[single-output algorithms](../../experiments/c432-family/check_single_output_algorithms.py),
[blocked bitsets](../../experiments/c432-family/check_batched_bitset_supports.py),
[triangle construction with unequal parts](../../experiments/c432-family/check_unbalanced_triangle_selector.py),
[tuple windows](../../experiments/c432-family/check_clique_window_selector.py),
[clique parameter regimes](../../experiments/c432-family/check_clique_regime_reduction.py),
and [cycle selectors](../../experiments/c432-family/check_cycle_selector_reduction.py).
From the repository root, the independent checker can be rerun with
standard-library Python and without writing an evidence report:

```sh
python3 -S -O -B experiments/c432-family/check_papers_bc_standalone.py
```

Its explicit failure checks remain active under `-O`.

## Replaying the two-failure prototypes

Run these commands from the project root. Their output paths are new replay
reports; the recorded input evidence remains separate.

```sh
python3 -S -O -B evidence/controller-localized-dominator-review-20261110/check_localized_dominators.py --output localized-dominator-replay.json
python3 -S -O -B experiments/c432-family/check_last_failure_streaming.py --output streamed-chain-replay.json
```

The defaults enumerate ordered DAGs through six vertices and include 300
seeded random instances. The localized suite additionally enumerates
independent-tree pairs through five vertices; the streamed suite enumerates
chain partitions through four vertices. These implementation checks use
explicit failure conditions that remain active under Python's `-O` option.

## Exact source identifiers

The following SHA-256 hashes bind the three principal programs and their
recorded results. Linked paths are relative to this source distribution.

| Artifact | SHA-256 |
|---|---|
| [check_papers_bc_standalone.py](../../experiments/c432-family/check_papers_bc_standalone.py) | `6d6fc27bc55b95898aa7212b37d811b0e81902adb224a4dbe36784e50efdfdf0` |
| [report.json](../../evidence/controller-papers-bc-revision-20261011/standalone-check/report.json) | `20959dae9f4a47c6d70fdde46eed2dc774f93ed6b449e0d26b0df45ccefb6d0e` |
| [check_localized_dominators.py](../../evidence/controller-localized-dominator-review-20261110/check_localized_dominators.py) | `2ad195d3813ac14d1bc987288faab3e0900085e2c2d459a84df71537b06824dd` |
| [check-results.json](../../evidence/controller-localized-dominator-review-20261110/check-results.json) | `db11036de554c09f3d660e4fc0a945ab3f19d61054d5851fc28fdab9a0e34617` |
| [check_last_failure_streaming.py](../../experiments/c432-family/check_last_failure_streaming.py) | `88b48b7a5c6091f013c86118bfe71c6a05b360eb445ec7f1b1ee4e81ef0035d0` |
| [check-results.json](../../evidence/controller-last-failure-streaming-20261110/check-results.json) | `1d4bd902e97129e2a19247dd3cf36fff09edd9a21a7d052f0fc31c769801233e` |

## Canonical summaries and sparse shortcuts

The [two-surrogate solver](../../evidence/controller-paper-b-two-surrogate-integration-20261111/two_surrogate_solver.py)
implements Theorem B.2, including input normalization, graph construction,
residual dominator grouping and aggregation. Its [BFS comparison](../../evidence/controller-paper-b-two-surrogate-integration-20261111/verify_two_surrogate_solver.py)
reports **33,932 graphs and 6,630,854 queries** without a mismatch in the
[recorded replay](../../evidence/controller-paper-b-two-surrogate-integration-20261111/two-surrogate-solver-checks.json).
The population contains all ordered DAGs through six vertices, 64 seeded
larger DAGs with permuted labels and roots, and boundary cases including
failed roots, initially unreachable vertices, duplicate targets and edges,
empty lists, and cycle rejection.

The [canonical-summary checker](../../evidence/controller-paper-b-two-surrogate-integration-20261111/check_canonical_summaries.py)
reports **389 source-reachable DAGs, 13,113 port sets, 190,250 query-equality
checks and 28,820 composition checks**. It also checks the research
identity for intersections of pair-dead regions 196,328 times; Theorem 3.1 uses that identity in its sorted discovery procedure. Its [recorded replay](../../evidence/controller-paper-b-two-surrogate-integration-20261111/canonical-summary-checks.json)
exhausts ordered source-reachable DAGs through five vertices and all target
subsets there, then checks 48 seeded larger DAGs with selected sets.
The proofs in Appendix B establish the universal statements.

Replay from the project root using normal Python, without `-O`: the
copied structural helpers retain assertion-based checks. These commands
write the named replay reports in the evidence directory.

```sh
python3 -B evidence/controller-paper-b-two-surrogate-integration-20261111/verify_two_surrogate_solver.py
python3 -B evidence/controller-paper-b-two-surrogate-integration-20261111/check_canonical_summaries.py
```

The exact source and result hashes are:

| Artifact | SHA-256 |
|---|---|
| [two_surrogate_solver.py](../../evidence/controller-paper-b-two-surrogate-integration-20261111/two_surrogate_solver.py) | `77b6e3d29bfeb8b6f44e3c8140ebc7ba503ff4b1588a2f11e7127038631a90b3` |
| [local_isolation_flow.py](../../evidence/controller-paper-b-two-surrogate-integration-20261111/local_isolation_flow.py) | `7ae6620f47e874b8017dfde5708942adfd8c6d4affe4f8a0c9e115f15645495c` |
| [verify_two_surrogate_solver.py](../../evidence/controller-paper-b-two-surrogate-integration-20261111/verify_two_surrogate_solver.py) | `272e5af1ac095923c6d8efcca539e19e8e136e7b3847cc63155ab3a3917eaaad` |
| [two-surrogate-solver-checks.json](../../evidence/controller-paper-b-two-surrogate-integration-20261111/two-surrogate-solver-checks.json) | `710f04a99e2186dfede9207581153f92145275025ac4056ccf6296d4ef537577` |
| [verify_two_surrogates.py](../../evidence/controller-paper-b-two-surrogate-integration-20261111/verify_two_surrogates.py) | `0ecafe0c63e71be0e1341284f49b27c9e4fef5322d4d210c6d596d0a410ba8d9` |
| [verify_discovery_reductions.py](../../evidence/controller-paper-b-two-surrogate-integration-20261111/verify_discovery_reductions.py) | `747160c73efd41d28014c0212860b1d163ae85b2cc43c3c48bc67b8660332e3a` |
| [check_canonical_summaries.py](../../evidence/controller-paper-b-two-surrogate-integration-20261111/check_canonical_summaries.py) | `e9a2f667559cf44adab6be6d4e642a9fdca74bd12ba8c988d4d0421320f0ef5f` |
| [canonical-summary-checks.json](../../evidence/controller-paper-b-two-surrogate-integration-20261111/canonical-summary-checks.json) | `9e523783d4893f2c925c3a827f699962b2a2a21bcd538f9df7110064c46b04af` |

## Recognized common-anchor batches

The [shared-anchor prototype](../../evidence/controller-paper-b-two-surrogate-integration-20261111/common_anchor_solver.py)
implements Theorem 3.1's sorted intersection, exact recognizer, bounded
flow, two residual labels per vertex and target aggregation. A rejected
query remains `None`; rejection is not an unreachable answer.

The [independent BFS audit](../../evidence/controller-paper-b-two-surrogate-integration-20261111/check_common_anchor.py)
checks all initially source-reachable ordered DAGs through five vertices
and every nonempty subset of their distinct nonroot failure pairs, plus
80 seeded larger DAGs. The [recorded result](../../evidence/controller-paper-b-two-surrogate-integration-20261111/common-anchor-checks.json)
reports **421 graphs, 20,955 batch recognitions, 66,899 running-intersection
checks, 17,753 accepted-kernel target memberships and 5,021 wrapper
answers**, without a mismatch. It also checks invalid inputs, relabelled
roots, unreachable components, duplicate entries and empty lists.

Crossing-pair, skip-DAG and rejected-group controls run at six sizes up
to parameter 512. The counters expose graph visits in discovery, flow,
decomposition, SCCs, labels and target evaluation. Normalization is
charged a conservative five-input-pass budget; sorting comparisons and
binary-lifting table work are accounted for in the theorem, not measured
by those edge counters. Every edge is visited at most once by the
resurrection stage. The finite checks do not establish novelty or replace
the all-size proof.

Replay from the project root with normal Python:

```sh
python3 -B evidence/controller-paper-b-two-surrogate-integration-20261111/check_common_anchor.py
```

| Artifact | SHA-256 |
|---|---|
| [common_anchor_solver.py](../../evidence/controller-paper-b-two-surrogate-integration-20261111/common_anchor_solver.py) | `055ddc0582ba1f6250e515895850ab4096d56ccce3e159eb559f0dc87f98b712` |
| [check_common_anchor.py](../../evidence/controller-paper-b-two-surrogate-integration-20261111/check_common_anchor.py) | `e27217711827c3546d8a812300c2d18267227b2726ef190533c8e8545f969da2` |
| [common-anchor-checks.json](../../evidence/controller-paper-b-two-surrogate-integration-20261111/common-anchor-checks.json) | `3cfdca400a7c132ecf565a2f170b0a8f7c188367f30f17eafe1f191aa1760f5f` |

## Threshold processing and exact historical-set sharing

The [threshold prototype](../../evidence/controller-paper-b-threshold-integration-20261111/threshold_solver.py)
checks the existential projection of Theorem 3.2 after initial reachability normalization and
topological renumbering. Its input is a nonempty predecessor-list DAG
with root 0, every vertex initially reachable, and every predecessor
smaller than its child. It handles empty target lists, failed roots,
zero or one failure, comparable failures and repeated target incidences
within that domain. The theorem includes the general-input normalization
cost; this prototype does not expose a general-graph normalization API.

Its [independent deletion-reachability checker](../../evidence/controller-paper-b-threshold-integration-20261111/check_threshold.py)
passes **3,525 batches**, including all **341** initially source-reachable
ordered DAGs through five vertices and **200** seeded larger DAGs.
It separately compares **3,213** proper-cut eligibility tests and **518**
arbitrary-target kernel answers with direct reachability. The run exercises
value-three flow, a noncut pair, and a surviving original target outside
the anchor's cut. The [recorded report](../../evidence/controller-paper-b-threshold-integration-20261111/threshold-checks.json)
counts normalization, residual construction, augmenting searches, SCC
passes, label propagation, edge pulls, stale and duplicate candidates,
and complete original-target scans. The checker verifies the ownership
and candidate-count inequalities used in the proof.

The [exact-sharing prototype](../../evidence/controller-paper-b-threshold-integration-20261111/interned_threshold.py)
has the same input preconditions and kernel. It stores sorted immutable
arrays in a deterministic AVL dictionary, comparing actual IDs. Its
[checker](../../evidence/controller-paper-b-threshold-integration-20261111/check_interning.py) passes **3,207 batches**:
the same 341 exhaustive graphs, 120 seeded larger graphs, an off-anchor
target regression, two switching-family sizes and four partial-overlap
sizes. It also audits 1,500 dictionary insertions. At switching parameter
`m=32`, distinct arrays contain 3,232 IDs versus 64,480 retained IDs
without sharing. On the partial-overlap control at `m=32`, distinct
arrays contain 69,792 IDs for input size 18,008. These finite counts
illustrate the all-size proofs in the
[representation supplement](paper-b-representation-examples-v1.1-draft.md).
The [sharing report](../../evidence/controller-paper-b-threshold-integration-20261111/interning-checks.json) records all cases.

Replay with assertions enabled; each command writes its named JSON report:

```sh
python3 -B evidence/controller-paper-b-threshold-integration-20261111/check_threshold.py
python3 -B evidence/controller-paper-b-threshold-integration-20261111/check_interning.py
```

The listed threshold and exact-sharing files form a self-contained
standard-library replay package. The following hashes identify the
programs and recorded results.
The counters measure logical work and payload, not process memory.
Finite replay does not establish a universal asymptotic bound, novelty,
or proof-assistant certification.

| Artifact | SHA-256 |
|---|---|
| [dominator_tree.py](../../evidence/controller-paper-b-threshold-integration-20261111/dominator_tree.py) | `2ccf7071a46fe1c57dd7d3b88d63d7e8d27f5b6a6c7938a0e652159ca1019ba5` |
| [threshold_solver.py](../../evidence/controller-paper-b-threshold-integration-20261111/threshold_solver.py) | `7a94de5e3e05ef2d76f99dfc0b1bf6495c3a3028ec3dd9b7b053925ec777aa1e` |
| [threshold_kernel.py](../../evidence/controller-paper-b-threshold-integration-20261111/threshold_kernel.py) | `419c8a3f0dfd1c642cb61ee699d73d0ea5cf8c4fd9530c29010ef16bdf7d1804` |
| [check_threshold.py](../../evidence/controller-paper-b-threshold-integration-20261111/check_threshold.py) | `31b597f3db7ace13923aba4171a51d34ec5a5d16846ec0b2521489fa50c45c24` |
| [threshold-checks.json](../../evidence/controller-paper-b-threshold-integration-20261111/threshold-checks.json) | `45feac032e379bddd722e3744e8f52d3157f7d4e129f9f4854229e398cdc44d1` |
| [exact_pool.py](../../evidence/controller-paper-b-threshold-integration-20261111/exact_pool.py) | `8b0630cc221a62b4486df1bc7460cf300e984769a55d595439a78ad6d863fd94` |
| [interned_threshold.py](../../evidence/controller-paper-b-threshold-integration-20261111/interned_threshold.py) | `4b33b260ad9d93c3db914f2b6fd8b60a257bdef32861e390688ba58a672d9a43` |
| [representation_families.py](../../evidence/controller-paper-b-threshold-integration-20261111/representation_families.py) | `ed884cd0bace8a25e62bd1bea473249dc712c04c76bae7599d9621301ec4ba70` |
| [check_interning.py](../../evidence/controller-paper-b-threshold-integration-20261111/check_interning.py) | `f481976e6ccbdb2ddbb10ac37e00c7c69665589913af05048ab0035f26177be8` |
| [interning-checks.json](../../evidence/controller-paper-b-threshold-integration-20261111/interning-checks.json) | `cd40372b5677d5da1376c20093aac87925d9b1c169ed98fdfaa0d7f24c3b22db` |
