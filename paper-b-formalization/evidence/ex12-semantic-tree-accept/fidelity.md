# EX1.2 ordinary dominator tree fidelity

For every acyclic original graph and source, the rank and parent
construction in `TopologicalRank` produces a semantic parent family.
`semanticParent_ancestor_iff_dominates` checks the inclusive ancestor
equivalence on all reachable vertices. The ordinary root and singleton
cases use reflexive reachability and dominance. For every reachable
nonroot the predecessor recurrence and unique-point theorem produce
the strict immediate dominator. Paths surviving deletion of an ordinary
vertex are exactly those appearing in the negated dominance test.

`exists_unique_dominatorLCA` supplies the unique greatest ordinary
dominator common to any nonempty finite list of reachable vertices,
including pairs and singleton lists. The checked all-tail equivalence
relates every physical tail's dominance to the LCA's dominance.
The original-DAG boundary lemmas supply internal paths and their
suffixes. Constructing this tree within the cost bound is EX1.5.
