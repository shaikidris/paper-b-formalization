# EX2.2 proper-loss forest fidelity

`LabelledQuotient.exists_properLossForest_lemma_3_1` chooses the
actual topological sweep's forest for each valid flat quotient and
injective arc-increasing rank. It gives canonical duplicate-free keys,
all real key existence conditions, root and direct-successor labels,
the equivalence between proper loss and inclusive ancestry, real edge
endpoint inclusion, loss-set nesting and fresh endpoint order.
`buildProperLossForest_validDepthTree` and `isForestAncestor_root`
verify that all node parents lead to the artificial root.
`predecessor_losses_form_prefix`, `sweep_parent_eq_for_reused_pair_key`
and `sweep_step_preserves_proper_loss_labels` independently replay
the raw-loss prefix and key reuse steps. The predecessor tests use
existential adjacency, so parallel arcs do not add keys.

This accepts the sweep semantics. An implementation with the advertised
word-operation bounds is the subject of EX2.4.
