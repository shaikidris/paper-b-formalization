# Required inputs and formalization decisions

[external-inputs.json](external-inputs.json) is the machine-readable dependency inventory. `TO_SURVEY` means availability in the selected formal libraries has not been established; it does not mean no such formalization exists.

## Inputs needed before Theorem 3.2 closes

Finite paths, finite sets, arrays, order and arithmetic should use supported standard libraries where their literal statements match. Survey and pin them in PB0.5. The project must still prove its concrete graph encodings and refinements.

The core needs a constructed dominator/LCA index, deterministic reachability/topological/SCC procedures, the bounded-capacity flow/cut argument and path decomposition, timestamp/incidence primitives, and an actual step/space model. An imported theorem granting correctness of an abstract dominator relation does not supply the cost of building its index. Likewise, a max-flow/min-cut existence theorem does not prove the cost of the three augmenting searches used here.

The core can use logarithmic-factor implementations, since its headline uses soft-O. This deliberately separates it from the harder exact-linear dominator requirement of Proposition 4.1. Every primitive in the final root must be discharged by checked implementation or an exact supported proved dependency.

Proposition 3.3 additionally needs a deterministic balanced dictionary with tuple-comparison costs. A generic finite map or hash map with unspecified worst-case lookup cost is insufficient.

## Optional branches with substantial inputs

- **Exact linear dominators and independent trees.** The paper cites [BGK+08](https://doi.org/10.1137/070693217) and [GT15](https://doi.org/10.1145/2764913). The one-occurrence theorem requires literal linear preprocessing; the depth theorem must construct valid independent trees and charge their construction. Conditional localization under supplied trees is a useful intermediate theorem, not the complete algorithmic claim.
- **Capacity/Kraft.** The input is the general directed edge-failure preserver theorem of [BCR18, Theorem 2](https://web.iitd.ac.in/~keerti/Papers/k-ftrs.pdf), or a matching proved improved anti-isolation theorem as attributed to [HSW25, Lemma 2.3](https://arxiv.org/abs/2510.02562). Cycles are allowed. Merely citing either result in a Lean comment leaves a formal hypothesis open.
- **Randomized algebra.** Proposition A.3 needs a finite-field nonzero polynomial test with a total error bound, matrix identities and a computation model accounting for the chosen matrix arithmetic. The identity alone is not its advertised algorithm.
- **Conditional complexity.** Triangle, clique, directed-cycle, algebraic-clique and Hitting Set assumptions are distinct propositions with different quantifiers, regimes and model clauses. A theorem conditional on a precise conjecture is appropriate. The reduction's construction cost and closure of its algorithm model are proved obligations.
- **Controller transfer.** Use the exact Paper A sources and declarations in [REUSE.md](REUSE.md). The native-size statement assumes supplied roles; recognition of arbitrary unannotated CNFs is outside that contract.

## Decision rule

For each input choose one of: supported proved import; substantive local proof; explicitly conditional intermediate result; defer the branch. Record the exact theorem type, environment, source identity, consumer and construction-cost coverage. A missing proved input must never be replaced by an unnamed axiom and counted as unconditional paper coverage.

## Constructed structural parameters

PB6.8–PB6.9 formalize the classical greedy overlapping-path construction and its complete composition with the streamed solver. PB6.10–PB6.11 formalize primal-dual weighted cover, fixed-tree subtree costs and the resulting OPT_c bound. These are later source-faithful obligations, not assumed free preprocessing.
