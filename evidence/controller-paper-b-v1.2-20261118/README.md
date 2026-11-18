# Paper B v1.2 edition review

The [main paper](../../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md) treats a static single-source reachability index on arbitrary DAGs. Its construction takes the graph and source before any failure pair or target is available. Theorem 1.1 gives its bounds. Theorem 4.1 proves the underlying equality of the original exit-tail sets. Each coordinate has a target-independent fresh contribution and a possible shared-endpoint contribution. The LCA compression in Section 5 follows the set theorem.

## Edition and scope

| Text | Extent | Contents |
|---|---:|---|
| [v1.2 main manuscript](../../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md) | 5,232 words | Six numbered sections, nine results and one open question. The 168-word abstract states the online graph interface, the four resource bounds and the exit-transfer idea. |
| [Threshold companion](../../papers/controller/paper-b-threshold-companion-v1.2.md) | 3,845 words | The earlier common-anchor theorem, all-query threshold theorem and exact-sharing proposition, including their full proofs. |
| [Extended v1.1 draft](../../papers/controller/paper-b-guarded-reachability-v1.1-draft.md) | 23,387 words | Historical text with the structural refinements, larger-sensitivity reductions and representation examples. |

Counts use whitespace-delimited Markdown tokens, including formulas and references. The companion's three blocks are byte-identical to the v1.1 blocks. The [published v1.0](https://doi.org/10.5281/zenodo.24142496) and the archived v1.1 source keep their own hashes in the [source lock](../../paper-b-formalization/sources/source-lock.json). The source lock also pins the manuscript, its companion and the mathematical evidence for this draft.

The oracle theorem replaces the offline threshold bound for unrestricted two-failure DAG batches. The common-anchor result retains its separate recognition output and its sharper bound in its special case. The main text ends with a supplied healthy-zero decoder application and the open higher-sensitivity question. The [closest-source comparison](../paper-b-space-20261118/exit-transfer-literature-and-paper-b.md) covers Choudhary's general-digraph oracle, the derived graph and the earlier two-cut representations. The precise preprocessing assumptions of the 2006 common-double-dominator paper still require a full-text check before an absolute priority claim. The main paper compares explicit guarantees.

## Checks

A first-reader review followed the six sections in order. It led to an initially reachable target in the opening, an explicit Boolean interpretation of target lists, a qualification on which two-predecessor keys are sorted, and the terminal and detection conventions in the decoder application. The final abstract explicitly distinguishes the exit sets in Theorem 4.1 from the two LCA summaries sufficient for a reachability query. Choudhary's ICALP paper provided the exposition comparison. [Primary paper](https://doi.org/10.4230/LIPIcs.ICALP.2016.130)

The [independent set and oracle checks](../paper-b-space-20261118/exit-transfer-review-checks.json) count 42,232 set identities across 191,294 flat DAGs, and 421,402 oracle answers against direct deletion for every source and target on all 1,099 ordered simple DAGs through five vertices. Both contributions were necessary in 20,052 tested coordinates. The [edition check record](edition-checks.json) records a successful replay of both checkers against their archived outputs. The [earlier implementation replay](../paper-b-space-20261118/dag-exit-checks.json) also compares singleton, repeated-list and expanded-block inputs. These are finite checks. The working-space and time analysis is in Sections 3–5.

The [active tracker](../../paper-b-formalization/DASHBOARD.md) maps nine proof-bearing statements and Question 6.2, and binds the deferred proof of Theorem 1.1 separately from the proof of Corollary 1.2. Its 25 work packages include nine open core obligations and two downstream obligations. Zero v1.2 roots have a Lean certificate. [Validation evidence](../../paper-b-formalization/evidence/plan-validation.json)

From the project root run

~~~sh
python3 -B evidence/controller-paper-b-v1.2-20261118/check_revision.py --replay
python3 -B paper-b-formalization/plan.py validate
python3 -B paper-b-formalization/test_plan.py
~~~

The edition history is local to `evidence/paper-b-editions.git`, with the project root as its worktree. Commit `3063f82` preserves the complete prior planning and manuscript baseline. The frozen mathematical prototype and its independent review are in the separate [proof workspace](../paper-b-space-20261118/README.md) at commit `dab731b`.
