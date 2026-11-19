import PaperB.ForestIntervals

open PaperB LabelledQuotient

#check @isForestAncestor_iff_dfsIntervalContains
#check @buildProperLossForest_ancestor_iff_interval_of_node
#check @buildProperLossForest_properLoss_iff_interval_of_node
#check @not_isForestAncestor_of_entry_eq_right_endpoint

#print axioms isForestAncestor_iff_dfsIntervalContains
#print axioms buildProperLossForest_ancestor_iff_interval_of_node
#print axioms buildProperLossForest_properLoss_iff_interval_of_node
#print axioms not_isForestAncestor_of_entry_eq_right_endpoint
#print axioms total_bucketChildren_edges

-- Compare the elaborated proof conclusions with the explicit half-open predicate.
example {N : Nat} {root : Fin N} {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (tree : ValidDepthTree root parent depth) (a v : Fin N) :
    IsForestAncestor parent a v ↔
      let preorder := dfsPreorder root parent depth
      let lo := firstOccurrence a preorder
      let i := firstOccurrence v preorder
      lo ≤ i ∧ i < lo + (dfsSubtree root parent depth a).length :=
  isForestAncestor_iff_dfsIntervalContains tree a v
