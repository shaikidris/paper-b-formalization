# Interfaces and quantifiers

## Static index

Choose one pair of deterministic programs build and query, with uniform constants. For every finite explicitly represented DAG \(G\) and every specified original source \(r\), build takes only \(G,r\). Its result \(I\) must answer every subsequently supplied \(F,t\) on original vertex identifiers, for \(|F|\le2\), without consulting adjacency lists. The Boolean answer is true exactly when \(t\) is reachable from \(r\) in \(G-F\). An empty path counts. Queries are independent. Parallel arcs count toward \(m\).

Put \(n=|V|,\ m=|E|,\ L=\lceil\log_2(n+2)\rceil\). For that very implementation require four bounds.

| Observable | Required bound |
|---|---|
| Construction operations | \(O((n+m)L^3)\) |
| Peak live construction words | \(O(n+m)\) |
| Words reachable from the retained index | \(O(n)\) |
| Operations for any subsequent single-target query | \(O(L^3)\) |

Words have logarithmic bit length in the explicit input. Resource accounting includes the identifier translation for initially unreachable vertices, scanning of labelled arcs, comparisons in sorted dictionaries, repeated predecessor tests, low-bit jumps, map composition, LCA operations and temporary arrays. Proper-loss lookup uses a pair key and a vertex label. A query cannot access the original graph through a closure over its constructor.

## Structural target

In one flat sibling quotient, take a real child pair \(P\) and real parent \(B\), a coordinate \(s\in B\) and a target \(y\in J(P)\). An exit is identified by its original tail. The theorem equates \(X_s^B(y)\) with the union of \(X_s^B(p)\) for all \(p\in P\setminus B\), together with \(X_s^P(y)\) if \(s\in P\). The inherited contribution is empty otherwise. Pairs may be disjoint. The fresh-endpoint sets do not depend on the target. This identity precedes any quotient by common ancestors and any per-coordinate Boolean test. [Theorem 4.1](sources/paper-b-v1.2-draft.md#statement-4-1)

## Downstream outputs

Corollary 1.2 returns a Boolean per original list, including empty and repeated lists. With \(M=\sum_i |T_i|\) and \(S=n+m+q+M\), total time is \(O(SL^3)\), including construction, with \(O(S)\) working words. For a later single list the query bound is \(O((1+|T_i|)L^3)\). Corollary 6.1 accepts the decoder and \(Q\) as input and recovers an admissible detecting set for a supplied healthy-zero root. [Coverage map](COVERAGE.md)
