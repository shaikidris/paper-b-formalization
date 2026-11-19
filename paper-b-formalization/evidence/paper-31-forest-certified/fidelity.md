# Paper B Lemma 3.1 correspondence

`PaperB.proper_loss_forest` is stated for any flat finite labelled
quotient and any injective rank increasing on its arcs. The proof
chooses the actual topological sweep, `buildProperLossForest`.

- Canonical ordered keys represent unordered distinct nonroot pairs.
  The keys are pairwise distinct. Their node existence iff quantifies
  over all such pairs and requires a nonempty proper-loss set.
- The artificial node has no key, is its own parent and is an ancestor
  of every node in the same valid depth tree. The label function reaches
  every quotient vertex. The source and all its direct successors receive
  the artificial-root label.
- For every pair and vertex, proper loss means loss excluding the pair
  endpoints and is equivalent to the pair node lying on the inclusive
  ancestor chain of the vertex's label.
- For every real child and its real parent, child endpoints are raw
  losses of the parent and proper losses are nested. Every fresh child
  endpoint follows both parent endpoints in rank.
- The number of real nodes is bounded by the quotient vertex count.

The semantic assertion is Lemma 3.1. Implementing the stated time and
workspace bounds for the sweep is the separate Lemma 3.2.
