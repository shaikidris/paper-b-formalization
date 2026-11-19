# EX2.3 depth-jump task fidelity

The growing forest consists of a root record followed by appended leaf
records. Each record stores its parent, depth and one skew-binary jump.
The kernel represents these as three words and carries one size header.
For each valid preallocated region, each current node and each insertion
under an existing parent with capacity remaining,
`PaperB.jumpWordRamBridge_endToEnd` gives the new layout, word fit and the
14-access insertion bound. The same statement gives exact refinement for
depth lookup and inclusive ancestry, including logarithmic read bounds
in the region capacity. `ancestorAtDepthWords_spec` and
`decideAncestorWords_spec` expose the corresponding detailed guarantees.
No new Lean code is introduced by this audit.

This discharges the EX2.3 data-structure task. The later oracle resource
tasks still have to place these arrays in the sealed machine and charge
arithmetic instructions, loops and complete build and query executions.
