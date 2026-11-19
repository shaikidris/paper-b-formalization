# EX1.6 statement correspondence

The ordinary dominator records from the actual original DAG run supply both
packed tree columns. `EX16Assembly.fromOriginal` invokes the original
scan once and constructs a single shared `StaticTreeReader.Reader`.
Its original-ID result relates inclusive dominance to the stored entry
and exclusive stop by two exact comparisons. The zero-edge path supplies
the original source premises. The breakpoint at the entry rank lies inside
that interval and the breakpoint at the stop lies outside.

`StaticTreeReader.Reader.child_some_iff` and `child_none_iff` certify
the strict-child search, including boundary ranks. The binary search
charges logarithmically many probes. `Reader.lca_exact` and
`lca_pow_jumps_le` certify the same reader's heavy-path result and
logarithmic cost by the strict halving of every light crossing. The
layout, head and child-range proofs count one construction per retained
vertex or tree edge, giving linear work and words for this static phase.
The formal oracle's final fixed-machine fields remain within EX5 scope.
