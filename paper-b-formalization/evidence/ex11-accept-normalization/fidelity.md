# EX1.1 normalization fidelity

- `Normalization.normalize` uses the actual Kahn order, its reachability
  scan and mark compaction. `normalized_survivingPath_iff` covers every
  source and original target with zero, one or two failed slots. The
  compact map rejects discarded endpoints and respects failed source,
  failed target, repeated failures and the live zero-length path.
- `CompactGraph.map_decode_outArcs` and the compact path equivalence
  preserve ordered parallel arc occurrences. Parallel occurrences never
  become disjoint reachability obligations.
- `KahnDecreasing.kahnValidOrder` builds the indexed order maps from
  `Kahn.run`; the map has a charged full array scatter. Its application
  to `Decreasing.ValidOrder.survivingPath_iff` relates original paths to
  the decreasing-child ReachAvoid contract. The standalone declaration
  uses the same zero-length and leading-arc constructors as the pinned
  FailureBatch source, with a separate namespace for the standalone build.
- `Normalization.normalization_counts` and `kahn_inverse_cost` cover
  topological edge scans, reachability mask construction, compact writes
  and inverse-rank order reads/writes. Sealed machine instruction and
  whole-oracle bounds are covered by later resource packages.
