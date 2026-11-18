# Lean obligations for published Paper B v1.3

The [published v1.3](../../submissions/paper-b-v1.3-20261118/paper-b-v1.3.md) keeps the same two-failure reachability problem, paper numbering, word model and space bounds. The Lean plan still has the same 27 work packages and seven milestones. The active [statement and proof ledger](../../paper-b-formalization/COVERAGE.md) and current Carbon contracts are pinned to [published v1.2](../../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md). The v1.3 changes below apply when the affected implementation and cost packages start.

## Proofs to continue

A comparison of both archived sources finds the statements and proofs of Lemmas 2.1 and 3.1 and Theorem 4.1 byte-identical. The statement of Question 6.2 is also identical. Lemma 3.1 still characterizes proper losses by inclusive ancestor membership, with the same predecessor sweep and reuse of a repeated pair key. Theorem 4.1 still equates the exact sets of physical tails for every real forest edge, parent endpoint and child proper-loss target. This preserves the current EX2.1–EX2.2 work and the structural path to EX3.1–EX3.3. Close the finite sweep and forest representation before using their ancestor labels to discharge the exit-transfer hypotheses.

Keep the existence of a surviving original arc tail as the semantic interface between EX1.4, EX3 and EX4. The optimized summaries can then discharge the same last-exit test. Preserve distinct physical tails until the set identity is proved. At the executable boundary, link the canonical pair-key order to the order of the two failure coordinates.

## Changes for the executable path

Write \(L=\lceil\log_2(n+2)\rceil\). The space obligations remain \(O(n+m)\) peak construction words and \(O(n)\) retained words for the oracle. The construction and query bounds must apply to the same implementation.

| Paper item | Work packages | v1.3 acceptance condition |
|---|---|---|
| Lemma 2.2 | EX1.4, EX1.6 | Use a nonempty interval of minimum and maximum original dominator-tree preorder ranks. A tail set is contained in a failed subtree iff both extremes are in its half-open interval \([\operatorname{tin}(a),\operatorname{tout}(a))\). Handle the empty summary explicitly and test a tail at \(\operatorname{tout}(a)\). Keep heavy-path LCA for the two failed vertices. |
| Lemma 3.2 | EX2.3, EX2.4 | Use the skew-binary parent/depth/jump invariant on each growing ancestor path. Prove constant-time insertion, \(O(L)\) moves per level search and \(O(L)\) online ancestry. Charge \(O(L)\) prefix probes, including every repeated predecessor scan, for \(O((n_H+m_H)L^2)\) construction. Final pair lookup stays \(O(L)\) and ancestry of a known pair stays \(O(1)\). |
| Lemma 5.1 | EX4.1–EX4.3 | Join intervals with min and max and an empty identity. Prove that this represents union and preserves the two-coordinate map algebra. In a skew merge compose the new parent-edge map followed by the two older jump maps, which are already installed. Charge \(O((n_H+m_H)L)\) summary construction and \(O(L)\) per evaluation, with constant work per composition. |
| Theorem 1.1 | EX0.2–EX0.3, EX1.5–EX1.6, EX4.4, EX5.1–EX5.4 | Prove \(O((n+m)L^2)\) deterministic preprocessing and \(O(L)\) worst-case online queries. Charge dominators, labelled quotient formation, repeated predecessor scans, temporaries, the failures' LCA, child and pair lookup and map traversal. The final interval comparisons cost \(O(1)\). Prove space for the same code and an index queried after input adjacency is discarded. |
| Corollary 1.2 | EX5.5 | Charge \(O((n+m)L^2+q+ML)\) time and \(O(n+m+q+M)\) words for \(q\) lists and \(M\) original target occurrences. A later list costs \(O(1+|T_i|L)\). Include empty lists in the \(O(q)\) charge. |
| Corollary 6.1 | EX6.1–EX6.2 | Reuse the same residual failure lists and detecting witness. Charge \(O(G_{\mathrm{dec}}\log^2(G_{\mathrm{dec}}+2))\) time and \(O(G_{\mathrm{dec}})\) words, including all declared labels, guard incidences and terminals. |

The first change to the growing-forest implementation is EX2.3. Use skew-binary jumps when writing that kernel and pass its interface to EX2.4 and EX4.3. The original-tree interval and child-search interface remains useful. At EX0.3, cost rank comparisons, depth subtraction and the constant-size map operations actually used by v1.3. A low-bit primitive belongs to a v1.2 implementation, if retained for comparison.

EX1.5 needs its own checked cost bound for the headline theorem. The manuscript uses the simple Lengauer–Tarjan construction in \(O((n+m)L)\). The planned DAG-specific alternative needs an \(O((n+m)L^2)\) proof. Once skew level-ancestor queries cost \(O(L)\), binary search over common ancestor depth takes \(O(L^2)\) per predecessor LCA. With a proof that a reachable vertex's immediate dominator is the LCA of its reachable predecessors and that appending a leaf preserves earlier ancestors, folding over predecessor occurrences fits the v1.3 budget. This is a Lean implementation route to prove.

Before accepting the optimized packages, bind their exact statements to the v1.3 release and its hash. A checked v1.3 oracle can establish the weaker v1.2 oracle time bounds using the same program. The LCA-valued statement of v1.2 Lemma 5.1 and the interval-valued v1.3 statement each require exact correspondence to their own Lean declarations. Preserve the existing source lock and evidence as the record for v1.2.

The v1.3 Markdown SHA-256 is 86098c578c3297fc7952aa357bec9c0d80b9c6e854ce117622561cda7c276808. The Markdown, PDF and source bundle for both versions match their local release hashes. The optimization has a manuscript proof and finite prototype checks. The new Lean cost bounds remain planned. [Detailed proof](proof.md) · [Prototype replay](replay.py) · [Comparison counts](checks.json)
