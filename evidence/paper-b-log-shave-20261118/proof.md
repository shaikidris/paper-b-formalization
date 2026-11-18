# Paper B two-failure oracle with logarithmic query time

On an adjacency-list DAG with a fixed source, the construction in Paper B v1.2 can be implemented with deterministic preprocessing time \(O((n+m)L^2)\), peak working space \(O(n+m)\) words, retained space \(O(n)\) words, and query time \(O(L)\), where \(L=\lceil\log_2(n+2)\rceil\). A query names at most two failed vertices and a target. For \(q\) explicitly listed queries with \(M\) target occurrences, the total time is \(O((n+m)L^2+(q+M)L)\). The exit-transfer identity applies with the hypotheses of Paper B v1.2.

## Summarizing exit-tail sets

Store the minimum and maximum dominator-tree preorder ranks of each nonempty support set, with a separate empty value. In the half-open subtree interval \([\operatorname{tin}(a),\operatorname{tout}(a))\), a nonempty support fits entirely exactly when both endpoint ranks do. An empty support provides no surviving tail. Union takes the minimum of the lower ranks and the maximum of the upper ranks, with empty as identity. Thus Theorem 4.1 and the base recurrence of Lemma 5.1 can use this associative join directly. A map coordinate still consists of a constant and at most one inherited input slot. Composition requires a constant number of interval joins. The LCA of the two failed vertices can still use the original \(O(L)\) heavy-path implementation.

## Growing the pair forest

Store the parent, depth and one jump \(j(v)\) per node. The artificial root has depth zero and jumps to itself. To append a node \(v\) with parent \(p\), put \(a=j(p)\), \(b=j(a)\). If \(a\) is real and the two positive jump lengths from \(p\) to \(a\) and from \(a\) to \(b\) are equal, set \(j(v)=b\). Otherwise set \(j(v)=p\). Insertion takes constant time.

Represent the list of real ancestors starting at \(v\), including \(v\), as consecutive blocks. Each block has size \(2^k-1\) and consists of a leading element followed by two equal child blocks, with a singleton as the base. Sizes increase strictly from the front except that the first two may tie. Prepending either creates a singleton or merges the first two tied blocks with the new leading element. A jump skips the first block. This invariant applies at every branch because each insertion prepends to its own parent's list. To reach a specified depth, skip the complete leading blocks before the target. There are \(O(L)\) blocks. If the next jump would pass the target, a parent step removes the leading element of that block. At most one whole child block precedes the target, and the process recurses in at most one child of half the size. This adds \(O(L)\) moves. This is Myers's skew-binary stack operation on the ancestor list. [Myers, 1983, §§3–4](https://publications.mpi-cbg.de/Myers_1983_6328.pdf)

For a nonmerged jump use the new node's map to its parent. For a merged jump use that map followed by the already installed maps from \(p\) to \(a\) and from \(a\) to \(b\). Both older jumps start at proper ancestors, so the order of base and map installation in Lemma 5.1 applies. Each map has two output coordinates and constant size. Summed over the quotients, building the support summaries takes \(O((n+m)L)\) time and each support evaluation takes \(O(L)\).

## Full cost

Lemma 3.2 still performs binary search on the prefix predicate. Each probe locates its candidate pair and scans the distinct predecessors, spending \(O(L)\) per online ancestor check. There are \(O(L)\) probes. This stage takes \(O((n+m)L^2)\) time including every repeated scan. The quotient vertex counts sum to \(O(n)\), and every labelled arc is charged to one quotient. Sorting and finding the relevant child blocks fit \(O((n+m)L)\) as in v1.2. In the retained index, the failures' LCA, block lookup, pair lookup and composed-map traversal each take at most \(O(L)\). The final subtree tests take constant time. This gives the stated bounds.

The published PDF was checked against its release hash. Corollary 6.1 displays \(h_i\) followed by a comma. Both the in-text citation and the bibliography use Tes08.

## Replay

Run the adjacent replay.py script with Python 3 from the project root. It applies the patch to temporary copies of the original oracle and checks the new composition and traversal against existing independent graph-search suites. The finite checks exercise correctness. The worst-case cost follows from the proof above.
