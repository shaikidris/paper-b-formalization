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

private theorem markReachHeads_query {n : Nat} (heads : List (Fin n))
    (marked : Array Bool) (hsize : marked.size = n) (u : Fin n) :
    ((markReachHeads marked heads).1[u.val]?).getD false = true ↔
      (marked[u.val]?).getD false = true ∨ u ∈ heads := by
  induction heads generalizing marked with
  | nil =>
      simp [markReachHeads]
  | cons v vs ih =>
      have hv : v.val < marked.size := by
        simpa only [hsize] using v.isLt
      have hs : (marked.setIfInBounds v.val true).size = n := by
        simpa using hsize
      simp only [markReachHeads]
      rw [ih (marked.setIfInBounds v.val true) hs]
      by_cases h : v.val = u.val
      · have he : v = u := Fin.ext h
        subst v
        rw [Array.getElem?_setIfInBounds_self_of_lt hv]
        simp
      · have hne : u ≠ v := fun he => h (congrArg Fin.val he.symm)
        rw [Array.getElem?_setIfInBounds_ne h]
        simp [List.mem_cons, hne]

private theorem seedReachMarks_query (g : Digraph)
    (source u : Fin g.vertexCount) :
    ((seedReachMarks g source)[u.val]?).getD false = true ↔ u = source := by
  unfold seedReachMarks
  have hu : u.val < (Array.replicate g.vertexCount false).size := by
    simp
  by_cases h : source.val = u.val
  · have he : source = u := Fin.ext h
    subst source
    rw [Array.getElem?_setIfInBounds_self_of_lt hu]
    simp
  · have hne : u ≠ source := fun he => h (congrArg Fin.val he.symm)
    rw [Array.getElem?_setIfInBounds_ne h]
    simp [u.isLt, hne]

private theorem visitReachVertex_sound (g : Digraph)
    (source u : Fin g.vertexCount) (marked : Array Bool)
    (hsize : marked.size = g.vertexCount)
    (hsound : ∀ v : Fin g.vertexCount,
      (marked[v.val]?).getD false = true → g.InitiallyReachable source v)
    (v : Fin g.vertexCount)
    (hv : ((visitReachVertex g marked u).1[v.val]?).getD false = true) :
    g.InitiallyReachable source v := by
  unfold visitReachVertex at hv
  split at hv
  · rename_i hu
    rcases (markReachHeads_query (g.outArcs u) marked hsize v).mp hv with
      hmarked | hhead
    · exact hsound v hmarked
    · exact initiallyReachable_extend (hsound u hu) (show g.HasArc u v from hhead)
  · exact hsound v hv

/-- Every scan preserves soundness of its input marks, regardless of order. -/
private theorem scanReachVertices_sound (g : Digraph)
    (source : Fin g.vertexCount) (order : List (Fin g.vertexCount))
    (marked : Array Bool) (hsize : marked.size = g.vertexCount)
    (hsound : ∀ v : Fin g.vertexCount,
      (marked[v.val]?).getD false = true → g.InitiallyReachable source v) :
    ∀ v : Fin g.vertexCount,
      ((scanReachVertices g marked order).marked[v.val]?).getD false = true →
        g.InitiallyReachable source v := by
  induction order generalizing marked with
  | nil =>
      simpa only [scanReachVertices] using hsound
  | cons u us ih =>
      have hstepSize : (visitReachVertex g marked u).1.size = g.vertexCount :=
        (visitReachVertex_spec g marked u).1.trans hsize
      simpa only [scanReachVertices] using
        (ih (visitReachVertex g marked u).1 hstepSize
          (visitReachVertex_sound g source u marked hsize hsound))

/-- Every marked vertex is reachable from the original source. -/
theorem scanReachability_sound (g : Digraph) (source : Fin g.vertexCount)
    (order : List (Fin g.vertexCount)) (verified : g.IsTopologicalList order)
    (u : Fin g.vertexCount)
    (hu : ((g.scanReachability source order verified).marked[u.val]?).getD false =
      true) :
    g.InitiallyReachable source u := by
  have hsize : (seedReachMarks g source).size = g.vertexCount := by
    simp [seedReachMarks]
  have hseed : ∀ v : Fin g.vertexCount,
      ((seedReachMarks g source)[v.val]?).getD false = true →
        g.InitiallyReachable source v := by
    intro v hv
    have he : v = source := (seedReachMarks_query g source v).mp hv
    subst v
    exact initiallyReachable_source g source
  exact scanReachVertices_sound g source order (seedReachMarks g source) hsize
    hseed u (by simpa only [scanReachability] using hu)

end PaperB.Digraph
