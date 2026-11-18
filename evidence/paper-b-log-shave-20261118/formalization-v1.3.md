# Lean obligations for the Paper B v1.3 draft

The [draft](../../papers/controller/paper-b-two-failure-reachability-v1.3-draft.md) proves a deterministic fixed-source oracle for at most two failed vertices on an arbitrary DAG. Its constructor takes \(O((n+m)L^2)\) time and \(O(n+m)\) peak words. Its index occupies \(O(n)\) words and answers each subsequent single-target query in \(O(L)\) time, with \(L=\lceil\log_2(n+2)\rceil\). These resource bounds have a manuscript proof and finite implementation checks. Their Lean status is **planned**.

The main [Lean tracker](../../paper-b-formalization/README.md) binds its task IDs to the deposited v1.2 article. The rows below specify the additional or revised obligations for v1.3 and identify the corresponding existing work packages. Each resource claim refers to the same implementation that proves the reachability predicate.

| Paper item | Work packages | v1.3 acceptance condition |
|---|---|---|
| Lemma 2.2 | EX1.4, EX1.6 | Prove original-tree subtree containment by the minimum and maximum ranks of a nonempty support, using an exclusive upper endpoint. The empty summary is the identity for unions. Test the boundary at the first rank outside a subtree. |
| Lemma 3.2 | EX2.3, EX2.4 | Prove the skew-binary block invariant on every parent path, including after branching. Charge constant work and words per insertion and \(O(L)\) moves per level search. Charge the pair lookup and all predecessor scans for the \(O((n_H+m_H)L^2)\) forest construction. |
| Lemma 5.1 | EX4.1, EX4.2, EX4.3 | Prove that joining rank pairs represents union and that both two-coordinate maps compose in the stated order. Justify availability of the older jump maps at a merge. Given the completed forest, charge \(O((n_H+m_H)L)\) time to build the summaries and \(O(L)\) to evaluate them. |
| Theorem 1.1 | EX0.2, EX0.3, EX1.5, EX1.6, EX4.4, EX5.1–EX5.4 | Bind the strengthened constructor and query costs and both space bounds to one implementation. Include ordinary dominator construction, the LCA of the two failures, child and key lookup, every labelled arc, temporary arrays and final interval tests. A dominator constructor proved only at the v1.2 cubic-logarithmic bound needs a tighter proof or a costed replacement. |
| Corollary 1.2 | EX5.5 | Write one Boolean per list. An empty list costs \(O(1)\), and the \(M\) target occurrences cost \(O(ML)\) in total. Prove \(O((n+m)L^2+q+ML)\) time with \(O(n+m+q+M)\) words, and \(O(1+|T_i|L)\) time for a later list. |
| Corollary 6.1 | EX6.1, EX6.2 | Use the same detecting witness and residual-target lists. Count all guard and terminal incidences to obtain \(O(G_{\mathrm{dec}}\log^2(G_{\mathrm{dec}}+2))\) time and \(O(G_{\mathrm{dec}})\) working words. |

Lemmas 2.1 and 3.1 and Theorem 4.1 have the same statements and proofs as in v1.2. In particular, EX3.1–EX3.3 concern the exact sets of physical tails before taking either preorder extreme. Question 6.2 continues to concern three or more failures.

Draft SHA-256: 5a97193d8af211f92df3a569a030a2070e8eca4d90afcb4f4e585aa0f94590e5. The [proof note](proof.md), [prototype replay](replay.py), and [comparison counts](checks.json) identify the mathematical argument and its finite tests.
