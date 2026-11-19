# Paper B Lemma 2.1 correspondence

`PaperB.sibling_quotients` obtains an injective arc-increasing rank
and the ordinary dominator parent map for every input DAG and source.
For every reachable root, the exact finite builder and its key-based
form satisfy flatness, rank increase and path correspondence. The
underlying boundary lemma gives unique entry at the block root and the
block system supplies paths from the root to each internal vertex.

The trace declarations project original paths along the block map and
lift every chosen sequence of labelled steps, preserving each physical
exit tail. Their label tag permits occurrence identities even when
several arcs have the same endpoints. In the serialized quotient each
occurrence stores its original tail under the matching quotient edge.

The per-occurrence theorem assigns each retained input arc to exactly
the ordinary parent of its head. Filtering retains occurrences,
including repeated entries. Over the distinct reachable roots the
actual arc-array count is exactly the count of retained input
occurrences. The total vertex slots are at most twice the input vertex
count, also covering roots with zero children. The book-keeping and
scope match the lemma on the root-reachable part of the original DAG.
