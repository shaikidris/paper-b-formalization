import PaperB.ForestPreparedBuild
import PaperB.OracleContract

namespace PaperB

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS

namespace QuotientMembership.Index

variable {H : LabelledQuotient} [DecidableEq (CutPair H)]

/-- Take the scalar slot from the exported query's definition. The witness is
    inferred by definitional equality, not by a second vertex-index formula. -/
private def exportedSlot (s : RetainedProperLoss.Columns H)
    (q : CutPair H) (v : Vertex H) :
    {i : Nat // s.contains q i =
      QuotientMembership.Index.contains (some s) q v} := by
  unfold QuotientMembership.Index.contains
  exact ⟨_, rfl⟩

def containsCounted (idx : QuotientMembership.Index H)
    (q : CutPair H) (v : Vertex H) : Bool × Nat :=
  match idx with
  | none => (false, 0)
  | some s => s.containsCounted q (exportedSlot s q v).val

theorem containsCounted_value (idx : QuotientMembership.Index H)
    (q : CutPair H) (v : Vertex H) :
    (containsCounted idx q v).1 = QuotientMembership.Index.contains idx q v := by
  cases idx with
  | none => rfl
  | some s =>
      exact
        (RetainedProperLoss.Columns.containsCounted_value
          s q (exportedSlot s q v).val).trans
          (exportedSlot s q v).property

private theorem logBudget (n : Nat) :
    1 ≤ OracleContract.L n ∧
      Nat.log2 (n + 1) + 8 ≤ 10 * OracleContract.L n := by
  unfold OracleContract.L
  constructor <;> omega

/-- The exported index type also admits arbitrary columns, so the size
    hypothesis is explicit here and discharged below for the exported build. -/
theorem containsCounted_count_le (idx : QuotientMembership.Index H)
    (q : CutPair H) (v : Vertex H)
    (hd : ∀ s : RetainedProperLoss.Columns H,
      idx = some s → s.dict.size ≤ H.vertexCount) :
    (containsCounted idx q v).2 ≤ 10 * OracleContract.L H.vertexCount := by
  cases idx with
  | none => exact Nat.zero_le _
  | some s =>
      have hs := hd s rfl
      have hl : Nat.log2 (s.dict.size + 1) ≤ Nat.log2 (H.vertexCount + 1) :=
        (Nat.le_log2 (by omega : H.vertexCount + 1 ≠ 0)).mpr
          (Nat.le_trans (Nat.log2_self_le (by omega)) (by omega))
      have hc := RetainedProperLoss.Columns.containsCounted_count_le
        s q (exportedSlot s q v).val
      have hb := (logBudget H.vertexCount).2
      change (s.containsCounted q (exportedSlot s q v).val).2 ≤
        10 * OracleContract.L H.vertexCount
      omega

/-- In the word model the pair has two dense numeric component IDs. A fixed
    allowance for field work, scalar-slot extraction, and other non-probe
    operations can therefore be added without changing the logarithmic order. -/
theorem containsCounted_withOverhead_le (idx : QuotientMembership.Index H)
    (q : CutPair H) (v : Vertex H) (c : Nat)
    (hd : ∀ s : RetainedProperLoss.Columns H,
      idx = some s → s.dict.size ≤ H.vertexCount) :
    (containsCounted idx q v).2 + c ≤ (10 + c) * OracleContract.L H.vertexCount := by
  have hc : c ≤ c * OracleContract.L H.vertexCount := by
    calc
      c = c * 1 := (Nat.mul_one c).symm
      _ ≤ c * OracleContract.L H.vertexCount :=
        Nat.mul_le_mul_left c (logBudget H.vertexCount).1
  rw [Nat.add_mul]
  exact Nat.add_le_add (containsCounted_count_le idx q v hd) hc

end QuotientMembership.Index

namespace ForestPreparedBuild

variable {H : LabelledQuotient} [DecidableEq (CutPair H)]
variable (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
variable (rank : Vertex H → Nat)
variable (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
  rank (orderedVertexAt data size_data i) <
    rank (orderedVertexAt data size_data j))
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)
variable (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
variable (flat : H.IsFlat)

/-- Explicit uniform `O(OracleContract.L H.vertexCount)` probe bound for
    querying an index produced by the exported build. -/
theorem containsCounted_count_le (q : CutPair H) (v : Vertex H) :
    (QuotientMembership.Index.containsCounted
      (build data size_data rank increasing covers rankArc flat) q v).2 ≤
        10 * OracleContract.L H.vertexCount := by
  apply QuotientMembership.Index.containsCounted_count_le
  intro s hs
  by_cases large : 3 ≤ H.vertexCount
  · rw [build, dite_eq_left large] at hs
    have he := Option.some.inj hs
    subst s
    exact RetainedProperLoss.ofOrderedReader_dict_size_le _
  · rw [build, dite_eq_right large] at hs
    cases hs

end ForestPreparedBuild
end PaperB
