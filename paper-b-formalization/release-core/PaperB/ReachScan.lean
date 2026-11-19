import PaperB.Graph

-- Append after the supplied Digraph definitions.
namespace PaperB.Digraph

/-- Every vertex occurs once, and every arc points into the suffix after its tail. -/
def IsTopologicalList (g : Digraph) (order : List (Fin g.vertexCount)) : Prop :=
  order.Nodup ∧
  (∀ u : Fin g.vertexCount, u ∈ order) ∧
  (∀ (pre : List (Fin g.vertexCount)) (u : Fin g.vertexCount)
     (post : List (Fin g.vertexCount)),
    order = pre ++ (u :: post) →
      ∀ v : Fin g.vertexCount, g.HasArc u v → v ∈ post)

structure ReachScanResult where
  marked : Array Bool
  vertexVisits : Nat
  adjacencyOccurrences : Nat
  deriving Repr

/-- Semantic traversal count, not a count of word-RAM operations. -/
def ReachScanResult.probes (r : ReachScanResult) : Nat :=
  r.vertexVisits + r.adjacencyOccurrences

/-- The adjacency budget for the supplied list. This is not computed by the scan. -/
def suppliedAdjacencyLength (g : Digraph) : List (Fin g.vertexCount) → Nat
  | [] => 0
  | u :: us => (g.outArcs u).length + suppliedAdjacencyLength g us

/-- Mark and count each list cell, including repeated heads and already marked heads. -/
private def markReachHeads {n : Nat} (marked : Array Bool) :
    List (Fin n) → Array Bool × Nat
  | [] => (marked, 0)
  | v :: vs =>
      let rest := markReachHeads (marked.setIfInBounds v.val true) vs
      (rest.1, rest.2 + 1)

private def visitReachVertex (g : Digraph) (marked : Array Bool)
    (u : Fin g.vertexCount) : Array Bool × Nat :=
  if (marked[u.val]?).getD false then
    markReachHeads marked (g.outArcs u)
  else
    (marked, 0)

private def scanReachVertices (g : Digraph) (marked : Array Bool) :
    List (Fin g.vertexCount) → ReachScanResult
  | [] => ⟨marked, 0, 0⟩
  | u :: us =>
      let step := visitReachVertex g marked u
      let rest := scanReachVertices g step.1 us
      ⟨rest.marked, rest.vertexVisits + 1,
        step.2 + rest.adjacencyOccurrences⟩

private def seedReachMarks (g : Digraph) (source : Fin g.vertexCount) :
    Array Bool :=
  (Array.replicate g.vertexCount false).setIfInBounds source.val true

/-- Scan an already verified order. The order proof is not used at runtime. -/
def scanReachability (g : Digraph) (source : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (_verified : g.IsTopologicalList order) :
    ReachScanResult :=
  scanReachVertices g (seedReachMarks g source) order

private theorem markReachHeads_spec {n : Nat} (heads : List (Fin n))
    (marked : Array Bool) :
    (markReachHeads marked heads).1.size = marked.size ∧
    (markReachHeads marked heads).2 = heads.length := by
  induction heads generalizing marked with
  | nil => exact ⟨rfl, rfl⟩
  | cons v vs ih =>
      rcases ih (marked.setIfInBounds v.val true) with ⟨hs, hc⟩
      constructor
      · simp [markReachHeads, hs]
      · simp only [markReachHeads, List.length_cons, hc]

private theorem visitReachVertex_spec (g : Digraph) (marked : Array Bool)
    (u : Fin g.vertexCount) :
    (visitReachVertex g marked u).1.size = marked.size ∧
    (visitReachVertex g marked u).2 ≤ (g.outArcs u).length := by
  unfold visitReachVertex
  split
  · rcases markReachHeads_spec (g.outArcs u) marked with ⟨hs, hc⟩
    refine ⟨hs, ?_⟩
    simpa only [hc] using Nat.le_refl (g.outArcs u).length
  · exact ⟨rfl, Nat.zero_le _⟩

/-- Size and counting invariants hold even for lists that are not topological. -/
private theorem scanReachVertices_spec (g : Digraph)
    (order : List (Fin g.vertexCount)) (marked : Array Bool) :
    (scanReachVertices g marked order).marked.size = marked.size ∧
    (scanReachVertices g marked order).vertexVisits = order.length ∧
    (scanReachVertices g marked order).adjacencyOccurrences ≤
      g.suppliedAdjacencyLength order := by
  induction order generalizing marked with
  | nil => exact ⟨rfl, rfl, Nat.le_refl 0⟩
  | cons u us ih =>
      rcases visitReachVertex_spec g marked u with ⟨hsize, hcount⟩
      rcases ih (visitReachVertex g marked u).1 with ⟨hs, hv, hc⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa only [scanReachVertices] using hs.trans hsize
      · simp only [scanReachVertices, List.length_cons, hv]
      · simpa only [scanReachVertices, suppliedAdjacencyLength] using
          Nat.add_le_add hcount hc

theorem scanReachability_size (g : Digraph) (source : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (verified : g.IsTopologicalList order) :
    (g.scanReachability source order verified).marked.size = g.vertexCount := by
  simpa [scanReachability, seedReachMarks] using
    (scanReachVertices_spec g order (seedReachMarks g source)).1

theorem scanReachability_vertexVisits (g : Digraph) (source : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (verified : g.IsTopologicalList order) :
    (g.scanReachability source order verified).vertexVisits = order.length :=
  (scanReachVertices_spec g order (seedReachMarks g source)).2.1

theorem scanReachability_adjacencyOccurrences_le (g : Digraph)
    (source : Fin g.vertexCount) (order : List (Fin g.vertexCount))
    (verified : g.IsTopologicalList order) :
    (g.scanReachability source order verified).adjacencyOccurrences ≤
      g.suppliedAdjacencyLength order :=
  (scanReachVertices_spec g order (seedReachMarks g source)).2.2

theorem scanReachability_probes_le (g : Digraph) (source : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (verified : g.IsTopologicalList order) :
    (g.scanReachability source order verified).probes ≤
      order.length + g.suppliedAdjacencyLength order := by
  unfold ReachScanResult.probes
  rw [scanReachability_vertexVisits]
  exact Nat.add_le_add (Nat.le_refl _)
    (scanReachability_adjacencyOccurrences_le g source order verified)

end PaperB.Digraph
