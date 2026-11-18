# Paper B v1.2 prepublication review, 18 November 2026

The exit-transfer theorem supports the preprocessing claim for all directed acyclic graphs. The sequential reader found the worked example correct. The proof audit also follows the result into the query index and accounts for all scans, map installations and retained words. The review recommends retaining the graph title and clarifying the abstract and introduction before posting.

| Question | Finding |
|---|---|
| What is the claimed advance? | From an adjacency-list DAG and a fixed source, build one index in \(O((n+m)\log^3(n+2))\) deterministic time, using \(O(n+m)\) working words. After discarding the graph, \(O(n)\) words suffice to answer any later target and at most two named vertex failures in \(O(\log^3(n+2))\) time. |
| What needs editing? | Say that the two original-tree LCAs describe one separating cut and one target. Define flatness by the ordinary dominator tree, and describe qualifying exit tails by their continuation. State explicitly which individual chains the 2006 algorithm assumes. [Passages and replacements](local-review.md) |
| Does the 2006 comparison hold? | On printed p. 38 the algorithm takes the individual chains as input, and on p. 40 it returns prefix references. The stated \(O(k\log n)\) computation combines the supplied chains. Its analysis leaves the simultaneous all-target build and storage unaccounted for. The earlier general-digraph oracle of Choudhary already covers the same online predicate. The contribution supported by this comparison is the DAG preprocessing bound and its physical-tail transfer. [Full-text comparison and recommended attribution](novelty.md) |
| What was tested? | 976 comparisons of physical exit-tail sets and 4,392 comparisons against direct reachability on expanded DAGs. Replacing each physical tail by its block root produced 126 wrong answers. The earlier edition replay also reproduced 421,402 query answers. [New results](physical-checks.json) · [Edition checks](../controller-paper-b-v1.2-20261118/README.md) |

The reviewed [manuscript](../../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md) is the 5,232-word edition at checkpoint `bcc6879`, SHA-256 `f62cda3d37658f5158bda908c03518fae5f04f59fa1a68b14cb4f312878d4d0c`. The review covers the title through §4 and follows the theorem through its use in §5. The finite checks exercise the proof on small graphs. They do not certify the asymptotic running time or global priority.

Carbon High checked both inclusions of Theorem 4.1 and recommended minor exposition repairs. Its most concrete addition is to specify how a query recovers the order of the two endpoints after the original graph is discarded. The first report was interrupted, and the follow-up returned the last three conclusions with a terminal error. Both responses and the checked findings are preserved. [Verified external report and conclusion](peer-verification.md)

## Replay

From the project root, the following commands run the two independent checks and the edition replay.

```bash
python3 -B evidence/paper-b-v12-adversarial-20261118/check_physical_tails.py
python3 -B evidence/paper-b-v12-adversarial-20261118/check_2006_example.py
python3 -B evidence/controller-paper-b-v1.2-20261118/check_revision.py --replay
```
