# EX1.5 statement correspondence

`PaperB.EX15.runGraph` uses Kahn's actual order, one reachability scan,
one incoming-occurrence grouping, and the initialized packed jump region.
`runGraph_spec` supplies the immediate dominator of each reachable nonroot
in the original graph. Its row order and multiplicities are exact. The
source dominates itself and no other vertex dominates the source, by the
zero-edge path.

The full scan consumes at most one fold input per incoming occurrence and
at most one LCA per fold input. The per-LCA depth search and all predecessor
folds use the charged bounds in `JumpLCA` and `DomPredecessorFold`.
Each new leaf uses exactly fourteen word accesses. The separate
`aggregateGraphWordBudget` inequality combines linear initialization and
scan costs with the already verified bound per LCA. The bound is
(O((n+m)L^2)), with (O(n+m)) build words from the single grouping,
fixed growing jump region, state columns, and sequential scan.
Final placement and charging in the end-to-end fixed RAM program belong
to EX5.
