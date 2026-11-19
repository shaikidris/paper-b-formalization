-- lean-toolchain: leanprover/lean4:v4.35.0-rc3
-- PaperB/CompactCounts.lean
import PaperB.CompactGraph
import PaperB.Kahn

namespace PaperB.CompactCounts

open PaperB.CompactGraph

private theorem mem_enum {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    f i ∈ List.ofFn f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases (motive := fun j => f j ∈ List.ofFn f) ?_ ?_ i
    · rw [List.ofFn_succ]
      simp
    · intro j
      rw [List.ofFn_succ]
      exact List.mem_cons_of_mem _ (ih (fun k : Fin n => f k.succ) j)

private theorem enum_witness {α : Type} {n : Nat} (f : Fin n → α) {a : α}
    (ha : a ∈ List.ofFn f) : ∃ i, f i = a := by
  induction n with
  | zero => simp at ha
  | succ n ih =>
    rw [List.ofFn_succ] at ha
    rcases List.mem_cons.mp ha with h | h
    · exact ⟨0, h.symm⟩
    · obtain ⟨i, hi⟩ := ih (fun j : Fin n => f j.succ) h
      exact ⟨i.succ, hi⟩

private theorem enum_nodup {α : Type} {n : Nat} (f : Fin n → α)
    (hf : ∀ {i j}, f i = f j → i = j) : (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.nodup_cons]
    refine ⟨?_, ih (fun i : Fin n => f i.succ) ?_⟩
    · intro h
      obtain ⟨i, hi⟩ := enum_witness (fun j : Fin n => f j.succ) h
      have he : i.succ = (0 : Fin (n + 1)) := hf hi
      have hv : i.val + 1 = 0 := congrArg Fin.val he
      omega
    · intro i j h
      have he : i.succ = j.succ := hf h
      exact Fin.ext (Nat.succ.inj (congrArg Fin.val he))

private theorem map_enum {α β : Type} {n : Nat} (f : Fin n → α) (w : α → β) :
    (List.ofFn f).map w = List.ofFn (fun i => w (f i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ, ih]

private theorem nodup_filter' {α : Type} (p : α → Bool) {xs : List α}
    (hx : xs.Nodup) : (xs.filter p).Nodup := by
  induction xs with
  | nil => simp
  | cons a ts ih =>
    have hn := List.nodup_cons.mp hx
    have ht := ih hn.2
    by_cases hp : p a = true
    · have he : (a :: ts).filter p = a :: ts.filter p := by
        simp [hp]
      rw [he, List.nodup_cons]
      exact ⟨fun h => hn.1 (List.mem_filter.mp h).1, ht⟩
    · simpa [List.filter_cons, hp] using ht

private theorem nodup_append' {α : Type} {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup)
    (hd : ∀ a, a ∈ xs → a ∉ ys) : (xs ++ ys).Nodup := by
  induction xs with
  | nil => simpa using hy
  | cons a ts ih =>
    change (a :: (ts ++ ys)).Nodup
    rw [List.nodup_cons]
    have hn := List.nodup_cons.mp hx
    refine ⟨?_, ih hn.2 (fun b hb => hd b (List.mem_cons_of_mem a hb))⟩
    intro h
    rcases List.mem_append.mp h with h | h
    · exact hn.1 h
    · exact hd a (by simp) h

private theorem pull_front {α : Type} (a : α) {ys : List α} (h : a ∈ ys) :
    ∃ zs, ys.Perm (a :: zs) := by
  induction ys with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with he | ht
    · subst b
      exact ⟨bs, List.Perm.refl _⟩
    · obtain ⟨zs, hp⟩ := ih ht
      refine ⟨b :: zs, (List.Perm.cons b hp).trans ?_⟩
      apply List.Perm.swap

private theorem perm_nodup_mem {α : Type} {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup)
    (hm : ∀ a, a ∈ xs ↔ a ∈ ys) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact List.Perm.nil
    | cons a ts =>
      have h : a ∈ ([] : List α) := (hm a).mpr (by simp)
      simp at h
  | cons a ts ih =>
    obtain ⟨zs, hp⟩ := pull_front a ((hm a).mp (by simp))
    have hz : (a :: zs).Nodup := by
      first
      | exact hp.nodup_iff.mp hy
      | exact hp.nodup hy
    have ht := List.nodup_cons.mp hx
    have hzs := List.nodup_cons.mp hz
    have hmem : ∀ b, b ∈ ts ↔ b ∈ zs := by
      intro b
      by_cases e : b = a
      · subst b
        simp [ht.1, hzs.1]
      · have hb : b ∈ a :: ts ↔ b ∈ a :: zs := (hm b).trans hp.mem_iff
        simpa only [List.mem_cons, e, false_or] using hb
    have htail : ts.Perm zs := by
      apply ih
      · exact ht.2
      · exact hzs.2
      · exact hmem
    exact (List.Perm.cons a htail).trans hp.symm

private theorem sum_map_perm {α : Type} (w : α → Nat) {xs ys : List α}
    (h : xs.Perm ys) : (xs.map w).sum = (ys.map w).sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [ih]
  | swap a b ts => simp [Nat.add_left_comm]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

def fullVertices (g : Digraph) : List (Fin g.vertexCount) :=
  List.ofFn (id : Fin g.vertexCount → Fin g.vertexCount)

def decodedVertices {g : Digraph} {marks : Array Bool} (idx : Index g marks) :
    List (Fin g.vertexCount) :=
  List.ofFn (decode idx)

def complement {g : Digraph} {marks : Array Bool} (idx : Index g marks) :
    List (Fin g.vertexCount) :=
  (fullVertices g).filter (fun u => decide (u ∉ decodedVertices idx))

private theorem mem_full (g : Digraph) (u : Fin g.vertexCount) :
    u ∈ fullVertices g :=
  mem_enum id u

private theorem mem_complement {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (u : Fin g.vertexCount) :
    u ∈ complement idx ↔ u ∉ decodedVertices idx := by
  simp [complement, List.mem_filter, mem_full g u]

theorem decodedVertices_nodup {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) : (decodedVertices idx).Nodup := by
  apply enum_nodup
  intro i j h
  have he := congrArg (encode idx) h
  rw [encode_decode idx i, encode_decode idx j] at he
  exact Option.some.inj he

theorem decoded_append_complement_perm {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) :
    (decodedVertices idx ++ complement idx).Perm (fullVertices g) := by
  have hf : (fullVertices g).Nodup :=
    enum_nodup id (fun h => h)
  have hc : (complement idx).Nodup :=
    nodup_filter' _ hf
  apply perm_nodup_mem (nodup_append' (decodedVertices_nodup idx) hc ?_) hf
  · intro u
    rw [List.mem_append, mem_complement]
    constructor
    · intro _
      exact mem_full g u
    · intro _
      by_cases h : u ∈ decodedVertices idx
      · exact Or.inl h
      · exact Or.inr h
  · intro u hu hc'
    exact ((mem_complement idx u).mp hc') hu

theorem vertexCount_build_le {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) : (build idx).vertexCount ≤ g.vertexCount := by
  have h := (decoded_append_complement_perm idx).length_eq
  simp [decodedVertices, fullVertices] at h
  change idx.tables.inverse.size ≤ g.vertexCount
  omega

private theorem rows_toList (g : Digraph) :
    List.ofFn g.outArcs = g.adj.toList := by
  have h : (Array.ofFn g.outArcs).toList = g.adj.toList := by
    apply List.ext_getElem
    · simp [g.adj_size]
    · intro i hi hj
      simp [Digraph.outArcs]
  simpa only [Array.toList_ofFn] using h

private theorem foldl_sum_map {α : Type} (w : α → Nat) (xs : List α) (a : Nat) :
    xs.foldl (fun s x => s + w x) a = a + (xs.map w).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x ts ih => simp [List.foldl, ih, Nat.add_assoc]

-- The full-row equality in Kahn is private; recover it from the raw array.
private theorem sum_full_rows (g : Digraph) :
    ((fullVertices g).map (fun u => (g.outArcs u).length)).sum = g.arcCount := by
  calc
    _ = (((fullVertices g).map g.outArcs).map List.length).sum := by
      simp only [List.map_map, Function.comp_def]
    _ = g.arcCount := by
      change (((List.ofFn (id : Fin g.vertexCount → Fin g.vertexCount)).map
        g.outArcs).map List.length).sum = g.arcCount
      rw [map_enum]
      change ((List.ofFn g.outArcs).map List.length).sum = g.arcCount
      rw [rows_toList]
      unfold Digraph.arcCount
      generalize g.adj.toList = rows
      first
      | change (rows.map List.length).sum =
          rows.foldl (fun s row => s + row.length) 0
        simpa only [Nat.zero_add] using (foldl_sum_map List.length rows 0).symm
      | induction rows with
        | nil => rfl
        | cons row rows ih =>
          rw [List.map_cons, List.sum_cons, ih] <;>
            first | rfl | exact Nat.add_comm _ _

/-- `build` makes one `filterMap` pass per inverse slot. Its input is the
original row of the decoded vertex, so each entry in that row counts once. -/
def adjacencyScans {g : Digraph} {marks : Array Bool} (idx : Index g marks) : Nat :=
  ((decodedVertices idx).map (fun u => (g.outArcs u).length)).sum

theorem adjacencyScans_le {g : Digraph} {marks : Array Bool} (idx : Index g marks) :
    adjacencyScans idx ≤ g.arcCount := by
  have h := sum_map_perm (fun u : Fin g.vertexCount => (g.outArcs u).length)
    (decoded_append_complement_perm idx)
  rw [List.map_append, List.sum_append, sum_full_rows] at h
  unfold adjacencyScans
  omega

theorem arcCount_build_eq_adjacencyScans {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (closed : OutgoingClosed idx) :
    (build idx).arcCount = adjacencyScans idx := by
  rw [← sum_full_rows (build idx)]
  unfold fullVertices adjacencyScans decodedVertices
  simp only [map_enum]
  apply congrArg (fun f : Vertex idx → Nat => (List.ofFn f).sum)
  funext k
  change ((build idx).outArcs k).length = (g.outArcs (decode idx k)).length
  have hlen (xs : List (Fin idx.tables.inverse.size)) :
      (xs.map (decode idx)).length = xs.length := by
    simp only [List.length_map]
  exact (hlen ((build idx).outArcs k)).symm.trans
    (congrArg List.length (map_decode_outArcs idx closed k))

theorem arcCount_build_le {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (closed : OutgoingClosed idx) :
    (build idx).arcCount ≤ g.arcCount := by
  rw [arcCount_build_eq_adjacencyScans idx closed]
  exact adjacencyScans_le idx

theorem compact_counts (g : Digraph) (marks : Array Bool)
    (hsize : marks.size = g.vertexCount)
    (closed : OutgoingClosed (Index.ofMarks g marks hsize)) :
    (CompactGraph.compact g marks hsize).vertexCount ≤ g.vertexCount ∧
      (CompactGraph.compact g marks hsize).arcCount ≤ g.arcCount :=
  ⟨vertexCount_build_le (Index.ofMarks g marks hsize),
   arcCount_build_le (Index.ofMarks g marks hsize) closed⟩

/-- Counts from the same checked tables: the map scan records one visit per
original vertex, each inverse fill appends one slot, and adjacency scans the
retained source rows. The total counts these events, not Word-RAM operations.
Closure is needed for equality with the output arc count, not for the scan
bound. -/
theorem traversal_bounds {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) :
    idx.tables.visits = g.vertexCount ∧
    idx.tables.inverse.size ≤ g.vertexCount ∧
    adjacencyScans idx ≤ g.arcCount ∧
    idx.tables.visits + idx.tables.inverse.size + adjacencyScans idx ≤
      2 * g.vertexCount + g.arcCount := by
  have hv : idx.tables.visits = g.vertexCount := by
    rw [idx.checked]
    exact (CompactIds.compact_spec marks).1.trans idx.size_eq
  have hi : idx.tables.inverse.size ≤ g.vertexCount := vertexCount_build_le idx
  have ha := adjacencyScans_le idx
  refine ⟨hv, hi, ha, ?_⟩
  omega

end PaperB.CompactCounts
