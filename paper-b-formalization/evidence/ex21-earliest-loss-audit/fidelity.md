# EX2.1 earliest-loss fidelity

`LabelledQuotient.properLoss_follows_endpoints` concerns every proper
loss after deleting two distinct nonroot vertices. Both endpoints precede
the loss in any arc-increasing rank. For an earliest proper loss,
`predecessors_iff_endpoints_of_first_properLoss` gives exact equality
of predecessor membership with pair membership. Membership forgets only
parallel multiplicity, which does not affect a lost-vertex test.
`buildProperLossForest_label_of_root_arc` rules out a proper loss at
a direct root successor. `buildProperLossForest_exists_node_iff` rules
out a node when no proper loss exists.
