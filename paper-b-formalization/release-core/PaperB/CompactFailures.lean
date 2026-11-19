import PaperB.CompactGraph

namespace PaperB.CompactGraph

def restrictFailures {g : Digraph} {marks : Array Bool} (idx : Index g marks) :
    FailureSet g.vertexCount → FailureSet (build idx).vertexCount
  | .none => .none
  | .one a =>
    match encode idx a with
    | none => .none
    | some i => .one i
  | .two a b =>
    match encode idx a, encode idx b with
    | none, none => .none
    | some i, none => .one i
    | none, some j => .one j
    | some i, some j => .two i j

theorem mem_restrictFailures_iff {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (F : FailureSet g.vertexCount) (k : Vertex idx) :
    (restrictFailures idx F).Mem k ↔ F.Mem (decode idx k) := by
  have absent (u : Fin g.vertexCount) (hu : encode idx u = none) :
      decode idx k ≠ u := by
    intro h
    have hs := (encode_eq_some_iff_decode idx u k).mpr h
    rw [hu] at hs
    cases hs
  have kept (u : Fin g.vertexCount) (i : Vertex idx)
      (hu : encode idx u = some i) : k = i ↔ decode idx k = u := by
    constructor
    · intro h
      exact (encode_eq_some_iff_decode idx u k).mp
        (hu.trans (congrArg some h.symm))
    · intro h
      have hs := (encode_eq_some_iff_decode idx u k).mpr h
      exact Option.some.inj (hs.symm.trans hu)
  cases F with
  | none => rfl
  | one a =>
    cases ha : encode idx a with
    | none =>
      simp [restrictFailures, FailureSet.Mem, ha, absent a ha]
    | some i =>
      simp only [restrictFailures, FailureSet.Mem, ha]
      change @Eq (Fin idx.tables.inverse.size) k i ↔ decode idx k = a
      exact kept a i ha
  | two a b =>
    cases ha : encode idx a with
    | none =>
      cases hb : encode idx b with
      | none =>
        simp [restrictFailures, FailureSet.Mem, ha, hb, absent a ha, absent b hb]
      | some j =>
        simp only [restrictFailures, FailureSet.Mem, ha, hb, absent a ha, false_or]
        change @Eq (Fin idx.tables.inverse.size) k j ↔ decode idx k = b
        exact kept b j hb
    | some i =>
      cases hb : encode idx b with
      | none =>
        simp only [restrictFailures, FailureSet.Mem, ha, hb, absent b hb, or_false]
        change @Eq (Fin idx.tables.inverse.size) k i ↔ decode idx k = a
        exact kept a i ha
      | some j =>
        simp only [restrictFailures, FailureSet.Mem, ha, hb]
        change
          (@Eq (Fin idx.tables.inverse.size) k i ∨
            @Eq (Fin idx.tables.inverse.size) k j) ↔
          (decode idx k = a ∨ decode idx k = b)
        exact or_congr (kept a i ha) (kept b j hb)

end PaperB.CompactGraph
