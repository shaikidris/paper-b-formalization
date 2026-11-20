import PaperB.ForestSlimIndex

namespace PaperB
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
namespace RetainedProperLoss

private def meterKey {H : LabelledQuotient} (q : CutPair H) : EncodedKey := by
  first
  | exact orderedPairCode q
  | exact orderedPairCode H q
  | exact ForestDictionary.orderedPairCode q
  | exact ForestDictionary.orderedPairCode H q

/-- Meter one optional array access, including an out-of-bounds access. -/
private def meterRead {α : Type} (xs : Array α) (i n : Nat) : Option α × Nat :=
  (xs[i]?, n + 1)

structure QueryTariff where
  dict : Nat
  direct : Nat

namespace Columns
variable {H : LabelledQuotient}

/-- Schedule all four accesses before the Boolean test. -/
def knownMetered (s : Columns H) (a i : Nat) : Bool × Nat :=
  let l := meterRead s.labels i 0
  let k := meterRead s.entry (l.1.getD 0) l.2
  let e := meterRead s.entry a k.2
  let t := meterRead s.stop a e.2
  (decide (e.1.getD 0 ≤ k.1.getD 0) && decide (k.1.getD 0 < t.1.getD 0), t.2)

theorem knownMetered_eq (s : Columns H) (a i : Nat) :
    s.knownMetered a i = (s.known a i, 4) := rfl

variable [DecidableEq (CutPair H)]

/-- Use the dictionary's own tariff, which charges the final bounded check. -/
def checkedMetered (s : Columns H) (key : EncodedKey) (q : CutPair H) :
    Option Nat × QueryTariff :=
  let hit := PairLookup.lookup s.dict key
  match hit.1 with
  | none => (none, ⟨hit.2, 0⟩)
  | some j =>
      let slot := meterRead s.slots j 0
      let a := slot.1.getD 0
      if a = 0 then (none, ⟨hit.2, slot.2⟩)
      else
        let b := meterRead s.back a slot.2
        (if b.1 = some (some q) then some a else none, ⟨hit.2, b.2⟩)

theorem checkedMetered_spec (s : Columns H) (key : EncodedKey) (q : CutPair H) :
    (s.checkedMetered key q).1 = s.checked key q ∧
    (s.checkedMetered key q).2.dict = (PairLookup.lookup s.dict key).2 ∧
    (s.checkedMetered key q).2.direct ≤ 2 := by
  cases h : (PairLookup.lookup s.dict key).1 with
  | none => simp [checkedMetered, checked, h]
  | some j =>
      by_cases hz : (s.slots[j]?).getD 0 = 0 <;>
        simp [checkedMetered, checked, meterRead, h, hz]

theorem checkedMetered_dict_le (s : Columns H) (key : EncodedKey) (q : CutPair H) :
    (s.checkedMetered key q).2.dict ≤ Nat.log2 (s.dict.size + 1) + 2 := by
  rw [(s.checkedMetered_spec key q).2.1]
  exact PairLookup.lookup_count_le s.dict key

def containsMetered (s : Columns H) (q : CutPair H) (i : Nat) :
    Bool × QueryTariff :=
  let c := s.checkedMetered (meterKey q) q
  match c.1 with
  | none => (false, c.2)
  | some a =>
      let k := s.knownMetered a i
      (k.1, ⟨c.2.dict, c.2.direct + k.2⟩)

theorem containsMetered_spec (s : Columns H) (q : CutPair H) (i : Nat) :
    (s.containsMetered q i).1 = s.contains q i ∧
    (s.containsMetered q i).2.dict = (PairLookup.lookup s.dict (meterKey q)).2 ∧
    (s.containsMetered q i).2.direct =
      (s.checkedMetered (meterKey q) q).2.direct +
        (match s.checked (meterKey q) q with | none => 0 | some _ => 4) := by
  obtain ⟨hv, hd, _⟩ := s.checkedMetered_spec (meterKey q) q
  have hc : s.contains q i =
      (match s.checked (meterKey q) q with
       | none => false
       | some a => s.known a i) := rfl
  cases h : s.checked (meterKey q) q <;>
    simp [containsMetered, hv, hd, hc, h, knownMetered_eq]

theorem containsMetered_eq (s : Columns H) (q : CutPair H) (i : Nat) :
    (s.containsMetered q i).1 = s.contains q i :=
  (s.containsMetered_spec q i).1

theorem containsMetered_count_le (s : Columns H) (q : CutPair H) (i : Nat) :
    (s.containsMetered q i).2.dict ≤ Nat.log2 (s.dict.size + 1) + 2 ∧
    (s.containsMetered q i).2.direct ≤ 6 := by
  obtain ⟨_, hd, hr⟩ := s.containsMetered_spec q i
  constructor
  · rw [hd]
    exact PairLookup.lookup_count_le s.dict (meterKey q)
  · rw [hr]
    have hb := (s.checkedMetered_spec (meterKey q) q).2.2
    cases s.checked (meterKey q) q with
    | none =>
        simpa only [Nat.add_zero] using (Nat.le_trans hb (by decide : 2 ≤ 6))
    | some a => exact Nat.add_le_add_right hb 4

end Columns

/-- Metering adds no retained columns; the tariff is a query result. -/
theorem metered_retained_size
    {H : LabelledQuotient} {p : ForestDictionary.Rows H}
    {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    [DecidableEq (CutPair H)]
    (r : OrderedReaderResult p data size_data rank large) :
    (ofOrderedReader r).arraySize =
      (orderedConfig p large).dict.size + r.out.tables.slots.size +
      r.out.tables.back.size + r.out.labels.size +
      r.index.reader.layout.endpoints.entry.data.size +
      r.index.reader.layout.endpoints.stop.data.size := rfl

end RetainedProperLoss
end PaperB
