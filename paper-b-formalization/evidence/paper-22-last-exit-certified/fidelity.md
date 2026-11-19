# Paper B Lemma 2.2 correspondence

`PaperB.last_exit_test` takes arbitrary initially reachable incomparable
failures and the validated ordinary dominator tree. It obtains their
lowest common ancestor and the two distinct child blocks from the
original tree. Its finite sibling pair keeps the correspondence between
each original failure and its own quotient endpoint.

The result covers all initially reachable targets outside the common
subtree, the common ancestor itself, and targets inside either failure
block. The within-block equivalence is the negated inclusive ordinary
dominance test. It includes a failed block root.

For a third block, a clean quotient path suffices. If the target's block
root is a proper loss, the two actual physical exit-tail lists are both
nonempty. Their unique original-tree LCAs give exactly the two inclusive
dominance tests in the paper, including direct final exits. These are
statements about the original surviving path, with quotient paths used
only to expose the witnesses.
