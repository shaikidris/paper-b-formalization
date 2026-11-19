# Paper B Theorem 4.1 correspondence

`PaperB.exit_set_transfer` uses the actual finite sibling quotient of
an original rooted DAG and the actual proper-loss forest for that
quotient. Its node-key hypotheses quantify over every real child and
real parent. There is no disjointness or overlap assumption.
`B.Mem s` ranges over both endpoint coordinates and
`H.ProperLoss P y` ranges over every proper loss of the child.

The identity is a membership equivalence for every original tail
`x : Fin g.vertexCount`. The first right-side term uses an existential
over precisely `P \ B` and repeats the same physical tail, independently
of `y`. The second term uses the same tail with the child exit predicate
and explicitly requires `s ∈ P`. With extensionality this is the
equality of sets, before the later LCA or extrema compression.

Figure 1 replays the exact fresh and inherited tails and the constructed
parent and label values. The separate regression checks that each of the
two surviving routes suffices and that deleting both blocks eliminates
both routes. The finite replays supplement the universal Lean proof.
