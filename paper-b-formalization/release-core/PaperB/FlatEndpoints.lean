import PaperB.ForestSlimIndex

namespace PaperB.EX52.FlatEndpoints

open PaperB.RetainedProperLoss (Columns)

abbrev Word (w : Nat) := Fin (2 ^ w)

variable {H : LabelledQuotient} {w : Nat}

/-- Header words 0, 1, and 2 store the three exclusive cuts. -/
def labelBase : Nat := 3

def labelEnd (s : Columns H) : Nat :=
  labelBase + s.labels.size

def entryEnd (s : Columns H) : Nat :=
  labelEnd s + s.entry.size

def stopEnd (s : Columns H) : Nat :=
  entryEnd s + s.stop.size

theorem cut_order (s : Columns H) :
    labelBase ≤ labelEnd s ∧ labelEnd s ≤ entryEnd s ∧
      entryEnd s ≤ stopEnd s := by
  simp only [stopEnd, entryEnd, labelEnd]
  omega

theorem region_bounds (s : Columns H) (i : Nat) :
    (labelBase + i < labelEnd s ↔ i < s.labels.size) ∧
    (labelEnd s + i < entryEnd s ↔ i < s.entry.size) ∧
    (entryEnd s + i < stopEnd s ↔ i < s.stop.size) := by
  simp only [stopEnd, entryEnd, labelEnd]
  omega

/-- The field hypotheses concern only in-bounds source reads. The strict
    capacity bound also makes the final one-past cut a valid word. -/
structure Fits (w : Nat) (s : Columns H) : Prop where
  labels : ∀ i : Nat, i < s.labels.size →
    (s.labels[i]?).getD 0 < 2 ^ w
  entry : ∀ i : Nat, i < s.entry.size →
    (s.entry[i]?).getD 0 < 2 ^ w
  stop : ∀ i : Nat, i < s.stop.size →
    (s.stop[i]?).getD 0 < 2 ^ w
  capacity : stopEnd s < 2 ^ w

private def headerValue (s : Columns H) (j : Nat) : Nat :=
  if j = 0 then labelEnd s else
  if j = 1 then entryEnd s else stopEnd s

private theorem headerValue_fit (s : Columns H) (f : Fits w s) (j : Nat) :
    headerValue s j < 2 ^ w := by
  obtain ⟨_, hl, he⟩ := cut_order s
  have hc := f.capacity
  unfold headerValue
  split
  · omega
  · split <;> omega

private def cell (s : Columns H) (f : Fits w s) (j : Fin (stopEnd s)) :
    Word w :=
  if h0 : j.val < labelBase then
    ⟨headerValue s j.val, headerValue_fit s f j.val⟩
  else if hl : j.val < labelEnd s then
    ⟨(s.labels[j.val - labelBase]?).getD 0,
      f.labels (j.val - labelBase) (by
        unfold labelEnd at hl
        omega)⟩
  else if he : j.val < entryEnd s then
    ⟨(s.entry[j.val - labelEnd s]?).getD 0,
      f.entry (j.val - labelEnd s) (by
        unfold entryEnd at he
        omega)⟩
  else
    ⟨(s.stop[j.val - entryEnd s]?).getD 0,
      f.stop (j.val - entryEnd s) (by
        have hj := j.isLt
        unfold stopEnd at hj
        omega)⟩

/-- One flat array. Neither the source columns nor a graph, reader, or
    configuration is part of the result. Each word uses its original
    natural value, not a modular conversion. -/
def serialize (s : Columns H) (f : Fits w s) : Array (Word w) :=
  Array.ofFn (cell s f)

@[simp] theorem serialize_size (s : Columns H) (f : Fits w s) :
    (serialize s f).size = stopEnd s := by
  simp [serialize]

theorem retained_words (s : Columns H) (f : Fits w s) :
    (serialize s f).size =
      3 + s.labels.size + s.entry.size + s.stop.size := by
  rw [serialize_size]
  rfl

theorem retained_words_le (s : Columns H) (f : Fits w s) :
    (serialize s f).size ≤ 3 + s.arraySize := by
  rw [retained_words]
  unfold Columns.arraySize
  omega

/-- Applies to each payload region using `region_bounds` and `cut_order`.
    In particular, forming an in-region address needs no modular wrap. -/
theorem region_address_noWrap (s : Columns H) (f : Fits w s)
    {lo hi i : Nat} (hend : hi ≤ stopEnd s) (hin : lo + i < hi) :
    lo ≤ lo + i ∧ lo + i < (serialize s f).size ∧
      lo + i < 2 ^ w ∧ (lo + i) % (2 ^ w) = lo + i := by
  have hj : lo + i < stopEnd s := Nat.lt_of_lt_of_le hin hend
  have hw : lo + i < 2 ^ w := Nat.lt_trans hj f.capacity
  exact ⟨Nat.le_add_right lo i, by simpa only [serialize_size] using hj,
    hw, Nat.mod_eq_of_lt hw⟩

/-- `none` is an out-of-bounds read result, not a stored word code. -/
def readWord (xs : Array (Word w)) (j : Nat) : Option Nat :=
  (xs[j]?).map Fin.val

private theorem serialize_get (s : Columns H) (f : Fits w s)
    (j : Nat) (hj : j < stopEnd s) :
    (serialize s f)[j]'(by simpa only [serialize_size] using hj) =
      cell s f ⟨j, hj⟩ := by
  simp [serialize]

private theorem readWord_serialize (s : Columns H) (f : Fits w s)
    (j : Nat) (hj : j < stopEnd s) :
    readWord (serialize s f) j = some (cell s f ⟨j, hj⟩).val := by
  have hb : j < (serialize s f).size := by
    simpa only [serialize_size] using hj
  simp only [readWord, getElem?_def, hb, dite_eq_left,
    serialize_get s f j hj, Option.map_some]

theorem header_exact (s : Columns H) (f : Fits w s) :
    readWord (serialize s f) 0 = some (labelEnd s) ∧
    readWord (serialize s f) 1 = some (entryEnd s) ∧
    readWord (serialize s f) 2 = some (stopEnd s) := by
  have h2 : 2 < stopEnd s := by
    simp only [stopEnd, entryEnd, labelEnd, labelBase]
    omega
  have h0 : 0 < stopEnd s := by omega
  have h1 : 1 < stopEnd s := by omega
  constructor
  · rw [readWord_serialize s f 0 h0] <;>
      simp [cell, labelBase, headerValue]
  · constructor
    · rw [readWord_serialize s f 1 h1] <;>
        simp [cell, labelBase, headerValue]
    · rw [readWord_serialize s f 2 h2] <;>
        simp [cell, labelBase, headerValue]

theorem label_physical (s : Columns H) (f : Fits w s)
    (i : Nat) (hi : i < s.labels.size) :
    readWord (serialize s f) (labelBase + i) = s.labels[i]? := by
  have h0 : ¬ labelBase + i < labelBase := by omega
  have hl := ((region_bounds s i).1).mpr hi
  have hj : labelBase + i < stopEnd s := by
    obtain ⟨_, hle, hes⟩ := cut_order s
    omega
  have hs : labelBase + i - labelBase = i := by omega
  rw [readWord_serialize s f (labelBase + i) hj] <;>
    simp [cell, h0, hl, hs, hi]

theorem entry_physical (s : Columns H) (f : Fits w s)
    (i : Nat) (hi : i < s.entry.size) :
    readWord (serialize s f) (labelEnd s + i) = s.entry[i]? := by
  obtain ⟨hbl, _, hes⟩ := cut_order s
  have h0 : ¬ labelEnd s + i < labelBase := by omega
  have hl : ¬ labelEnd s + i < labelEnd s := by omega
  have he := ((region_bounds s i).2.1).mpr hi
  have hj : labelEnd s + i < stopEnd s := by omega
  have hs : labelEnd s + i - labelEnd s = i := by omega
  rw [readWord_serialize s f (labelEnd s + i) hj] <;>
    simp [cell, h0, hl, he, hs, hi]

theorem stop_physical (s : Columns H) (f : Fits w s)
    (i : Nat) (hi : i < s.stop.size) :
    readWord (serialize s f) (entryEnd s + i) = s.stop[i]? := by
  obtain ⟨hbl, hle, _⟩ := cut_order s
  have h0 : ¬ entryEnd s + i < labelBase := by omega
  have hl : ¬ entryEnd s + i < labelEnd s := by omega
  have he : ¬ entryEnd s + i < entryEnd s := by omega
  have hj := ((region_bounds s i).2.2).mpr hi
  have hs : entryEnd s + i - entryEnd s = i := by omega
  rw [readWord_serialize s f (entryEnd s + i) hj] <;>
    simp [cell, h0, hl, he, hs, hi]

def readRegion (xs : Array (Word w)) (lo hi i : Nat) : Option Nat :=
  if lo + i < hi then readWord xs (lo + i) else none

def label? (xs : Array (Word w)) (i : Nat) : Option Nat :=
  readRegion xs labelBase ((readWord xs 0).getD 0) i

def entry? (xs : Array (Word w)) (i : Nat) : Option Nat :=
  readRegion xs ((readWord xs 0).getD 0) ((readWord xs 1).getD 0) i

def stop? (xs : Array (Word w)) (i : Nat) : Option Nat :=
  readRegion xs ((readWord xs 1).getD 0) ((readWord xs 2).getD 0) i

private theorem readRegion_exact (xs : Array (Word w)) (ys : Array Nat)
    (lo hi : Nat) (hcut : hi = lo + ys.size)
    (hread : ∀ i : Nat, i < ys.size → readWord xs (lo + i) = ys[i]?)
    (i : Nat) : readRegion xs lo hi i = ys[i]? := by
  by_cases h : i < ys.size
  · have hin : lo + i < hi := by omega
    simpa only [readRegion, if_pos hin] using hread i h
  · have hout : ¬ lo + i < hi := by omega
    simp [readRegion, hout, h]

theorem label_exact (s : Columns H) (f : Fits w s) (i : Nat) :
    label? (serialize s f) i = s.labels[i]? := by
  unfold label?
  rw [(header_exact s f).1]
  exact readRegion_exact (serialize s f) s.labels labelBase (labelEnd s)
    rfl (label_physical s f) i

theorem entry_exact (s : Columns H) (f : Fits w s) (i : Nat) :
    entry? (serialize s f) i = s.entry[i]? := by
  unfold entry?
  rw [(header_exact s f).1, (header_exact s f).2.1]
  exact readRegion_exact (serialize s f) s.entry (labelEnd s) (entryEnd s)
    rfl (entry_physical s f) i

theorem stop_exact (s : Columns H) (f : Fits w s) (i : Nat) :
    stop? (serialize s f) i = s.stop[i]? := by
  unfold stop?
  rw [(header_exact s f).2.1, (header_exact s f).2.2]
  exact readRegion_exact (serialize s f) s.stop (entryEnd s) (stopEnd s)
    rfl (stop_physical s f) i

def labelAt (xs : Array (Word w)) (i : Nat) : Nat :=
  (label? xs i).getD 0

theorem labelAt_exact (s : Columns H) (f : Fits w s) (i : Nat) :
    labelAt (serialize s f) i = s.labelAt i := by
  simp only [labelAt, label_exact, Columns.labelAt]

/-- The half-open interval test uses only the flat payload and scalar inputs. -/
def known (xs : Array (Word w)) (a i : Nat) : Bool :=
  let k := (entry? xs (labelAt xs i)).getD 0
  decide ((entry? xs a).getD 0 ≤ k) && decide (k < (stop? xs a).getD 0)

theorem known_exact (s : Columns H) (f : Fits w s) (a i : Nat) :
    known (serialize s f) a i = s.known a i := by
  simp only [known, labelAt_exact, entry_exact, stop_exact, Columns.known]

end PaperB.EX52.FlatEndpoints
