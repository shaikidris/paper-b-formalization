import PaperB.CompactIds
import PaperB.Graph

namespace PaperB.CompactGraph

/-- A checked table value shared by the encoder, decoder, and graph builder. -/
structure Index (g : Digraph) (marks : Array Bool) where
  size_eq : marks.size = g.vertexCount
  tables : CompactIds.Tables marks.size
  checked : tables = CompactIds.compact marks

def Index.ofMarks (g : Digraph) (marks : Array Bool)
    (hsize : marks.size = g.vertexCount) : Index g marks :=
  ⟨hsize, CompactIds.compact marks, rfl⟩

abbrev Vertex {g : Digraph} {marks : Array Bool} (idx : Index g marks) : Type :=
  Fin idx.tables.inverse.size

def markId {g : Digraph} {marks : Array Bool} (idx : Index g marks)
    (u : Fin g.vertexCount) : Fin marks.size :=
  Fin.cast idx.size_eq.symm u

def IsMarked {g : Digraph} {marks : Array Bool} (idx : Index g marks)
    (u : Fin g.vertexCount) : Prop :=
  CompactIds.marked marks (markId idx u) = true

def OutgoingClosed {g : Digraph} {marks : Array Bool} (idx : Index g marks) : Prop :=
  ∀ (u v : Fin g.vertexCount), IsMarked idx u → g.HasArc u v → IsMarked idx v

/-- One forward lookup, followed by a bounds check on the returned slot. -/
def encode {g : Digraph} {marks : Array Bool} (idx : Index g marks)
    (u : Fin g.vertexCount) : Option (Vertex idx) :=
  match CompactIds.lookup idx.tables (markId idx u) with
  | none => none
  | some j =>
    if hj : j < idx.tables.inverse.size then some ⟨j, hj⟩ else none

def decode {g : Digraph} {marks : Array Bool} (idx : Index g marks)
    (k : Vertex idx) : Fin g.vertexCount :=
  Fin.cast idx.size_eq (idx.tables.inverse[k.val]'k.isLt)

private theorem cast_back {n m : Nat} (h : n = m) (i : Fin n) :
    Fin.cast h.symm (Fin.cast h i) = i := by
  cases h
  rfl

private theorem lookup_some_iff_index {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (i : Fin marks.size) (j : Nat) :
    CompactIds.lookup idx.tables i = some j ↔
      ∃ (hj : j < idx.tables.inverse.size), idx.tables.inverse[j]'hj = i := by
  cases idx with
  | mk hsize tables checked =>
    subst tables
    exact CompactIds.lookup_some_iff marks i j

private theorem lookup_exists_iff_marked_index {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (i : Fin marks.size) :
    (∃ (j : Nat), CompactIds.lookup idx.tables i = some j) ↔
      CompactIds.marked marks i = true := by
  cases idx with
  | mk hsize tables checked =>
    subst tables
    exact CompactIds.lookup_exists_iff_marked marks i

theorem encode_eq_some_iff_lookup {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (u : Fin g.vertexCount) (k : Vertex idx) :
    encode idx u = some k ↔
      CompactIds.lookup idx.tables (markId idx u) = some k.val := by
  constructor
  · intro h
    unfold encode at h
    cases hl : CompactIds.lookup idx.tables (markId idx u) with
    | none =>
      simp [hl] at h
    | some j =>
      by_cases hj : j < idx.tables.inverse.size
      · have hs : some (⟨j, hj⟩ : Vertex idx) = some k := by
          simpa only [hl, dite_eq_left hj] using h
        have hv : j = k.val :=
          congrArg (fun (q : Vertex idx) => q.val) (Option.some.inj hs)
        simpa only [hl] using (congrArg (fun (q : Nat) => some q) hv)
      · simp [hl, hj] at h
  · intro h
    cases k with
    | mk j hj =>
      change CompactIds.lookup idx.tables (markId idx u) = some j at h
      simp [encode, h, hj]

theorem encode_eq_some_iff_decode {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (u : Fin g.vertexCount) (k : Vertex idx) :
    encode idx u = some k ↔ decode idx k = u := by
  constructor
  · intro h
    obtain ⟨hk, he⟩ := (lookup_some_iff_index idx (markId idx u) k.val).mp
      ((encode_eq_some_iff_lookup idx u k).mp h)
    calc
      decode idx k = Fin.cast idx.size_eq (markId idx u) :=
        congrArg (fun (i : Fin marks.size) => Fin.cast idx.size_eq i) he
      _ = u := cast_back idx.size_eq.symm u
  · intro h
    have he : markId idx (decode idx k) = markId idx u :=
      congrArg (markId idx) h
    have hc : markId idx (decode idx k) = idx.tables.inverse[k.val]'k.isLt :=
      cast_back idx.size_eq (idx.tables.inverse[k.val]'k.isLt)
    exact (encode_eq_some_iff_lookup idx u k).mpr
      ((lookup_some_iff_index idx (markId idx u) k.val).mpr
        ⟨k.isLt, hc.symm.trans he⟩)

theorem decode_encode {g : Digraph} {marks : Array Bool} (idx : Index g marks)
    (u : Fin g.vertexCount) (k : Vertex idx) (h : encode idx u = some k) :
    decode idx k = u :=
  (encode_eq_some_iff_decode idx u k).mp h

theorem encode_decode {g : Digraph} {marks : Array Bool} (idx : Index g marks)
    (k : Vertex idx) : encode idx (decode idx k) = some k :=
  (encode_eq_some_iff_decode idx (decode idx k) k).mpr rfl

theorem encode_exists_iff_marked {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (u : Fin g.vertexCount) :
    (∃ (k : Vertex idx), encode idx u = some k) ↔ IsMarked idx u := by
  constructor
  · rintro ⟨k, hk⟩
    exact (lookup_exists_iff_marked_index idx (markId idx u)).mp
      ⟨k.val, (encode_eq_some_iff_lookup idx u k).mp hk⟩
  · intro hu
    obtain ⟨j, hj⟩ := (lookup_exists_iff_marked_index idx (markId idx u)).mpr hu
    obtain ⟨hb, _⟩ := (lookup_some_iff_index idx (markId idx u) j).mp hj
    let k : Vertex idx := ⟨j, hb⟩
    exact ⟨k, (encode_eq_some_iff_lookup idx u k).mpr hj⟩

theorem decode_encode_marked {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (u : Fin g.vertexCount) (hu : IsMarked idx u) :
    (encode idx u).map (decode idx) = some u := by
  obtain ⟨k, hk⟩ := (encode_exists_iff_marked idx u).mpr hu
  rw [hk]
  exact congrArg (fun (v : Fin g.vertexCount) => some v) (decode_encode idx u k hk)

theorem marked_decode {g : Digraph} {marks : Array Bool} (idx : Index g marks)
    (k : Vertex idx) : IsMarked idx (decode idx k) :=
  (encode_exists_iff_marked idx (decode idx k)).mp ⟨k, encode_decode idx k⟩

theorem encode_head {g : Digraph} {marks : Array Bool} (idx : Index g marks)
    (closed : OutgoingClosed idx) (u : Vertex idx) (v : Fin g.vertexCount)
    (hv : g.HasArc (decode idx u) v) :
    ∃ (k : Vertex idx), encode idx v = some k :=
  (encode_exists_iff_marked idx v).mpr
    (closed (decode idx u) v (marked_decode idx u) hv)

/-- Each row makes one `filterMap` pass over the corresponding original row. -/
def build {g : Digraph} {marks : Array Bool} (idx : Index g marks) : Digraph where
  vertexCount := idx.tables.inverse.size
  adj := Array.ofFn (fun (k : Vertex idx) =>
    (g.outArcs (decode idx k)).filterMap (encode idx))
  adj_size := by simp

/-- Construct the checked tables once, then share them across all rows. -/
def compact (g : Digraph) (marks : Array Bool) (hsize : marks.size = g.vertexCount) :
    Digraph :=
  let idx : Index g marks := Index.ofMarks g marks hsize
  build idx

theorem outArcs_build {g : Digraph} {marks : Array Bool} (idx : Index g marks)
    (u : Vertex idx) :
    (build idx).outArcs u = (g.outArcs (decode idx u)).filterMap (encode idx) := by
  simp [Digraph.outArcs, build, Array.getElem_ofFn]

private theorem map_decode_filterMap {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (xs : List (Fin g.vertexCount))
    (hxs : ∀ (v : Fin g.vertexCount), v ∈ xs →
      ∃ (k : Vertex idx), encode idx v = some k) :
    (xs.filterMap (encode idx)).map (decode idx) = xs := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨k, hk⟩ := hxs v (by simp)
    have hvs : ∀ (w : Fin g.vertexCount), w ∈ vs →
        ∃ (q : Vertex idx), encode idx w = some q :=
      fun (w : Fin g.vertexCount) (hw : w ∈ vs) =>
        hxs w (List.mem_cons_of_mem v hw)
    have htail : (vs.filterMap (encode idx)).map (decode idx) = vs := ih hvs
    simp [List.filterMap, hk, decode_encode idx v k hk, htail]

/-- List equality preserves both the order and the multiplicity of arcs. -/
theorem map_decode_outArcs {g : Digraph} {marks : Array Bool} (idx : Index g marks)
    (closed : OutgoingClosed idx) (u : Vertex idx) :
    ((build idx).outArcs u).map (decode idx) = g.outArcs (decode idx u) := by
  rw [outArcs_build idx u]
  exact map_decode_filterMap idx (g.outArcs (decode idx u))
    (fun (v : Fin g.vertexCount) (hv : v ∈ g.outArcs (decode idx u)) =>
      encode_head idx closed u v hv)

theorem hasArc_iff {g : Digraph} {marks : Array Bool} (idx : Index g marks)
    (closed : OutgoingClosed idx) (u v : Vertex idx) :
    (build idx).HasArc u v ↔ g.HasArc (decode idx u) (decode idx v) := by
  change v ∈ (build idx).outArcs u ↔ decode idx v ∈ g.outArcs (decode idx u)
  rw [← map_decode_outArcs idx closed u]
  constructor
  · intro hv
    exact List.mem_map.mpr ⟨v, hv, rfl⟩
  · intro hv
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hv
    have hs : some w = some v :=
      (encode_decode idx w).symm.trans
        ((congrArg (encode idx) he).trans (encode_decode idx v))
    have hwv : w = v := Option.some.inj hs
    subst w
    exact hw

end PaperB.CompactGraph
