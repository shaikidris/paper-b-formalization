import PaperB.FlatPairDictionary

namespace PaperB.ForestSlimIndex.FlatPairDictionary.BackKey

variable {bits : Nat} {H : PaperB.LabelledQuotient}

def tagCode : Option (PaperB.LabelledQuotient.CutPair H) → Nat
  | none => 0
  | some _ => 1

def firstCode : Option (PaperB.LabelledQuotient.CutPair H) → Nat
  | none => 0
  | some q => q.fst.val

def secondCode : Option (PaperB.LabelledQuotient.CutPair H) → Nat
  | none => 0
  | some q => q.snd.val

/-- No extra tag-fit hypothesis is needed. A present pair has two
    distinct dense IDs, so its vertex count is at least two. -/
theorem row_fits (verticesFit : H.vertexCount ≤ 2 ^ bits)
    (o : Option (PaperB.LabelledQuotient.CutPair H)) :
    tagCode o < 2 ^ bits ∧
      firstCode o < 2 ^ bits ∧ secondCode o < 2 ^ bits := by
  cases o with
  | none =>
    have hz : 0 < 2 ^ bits := by
      first
      | exact Nat.two_pow_pos bits
      | exact Nat.pow_pos (by decide)
    exact ⟨hz, hz, hz⟩
  | some q =>
    have hne : q.fst.val ≠ q.snd.val := fun e => q.ne (Fin.ext e)
    have hf : q.fst.val < H.vertexCount := q.fst.isLt
    have hs : q.snd.val < H.vertexCount := q.snd.isLt
    have ht : 1 < H.vertexCount := by omega
    exact ⟨Nat.lt_of_lt_of_le ht verticesFit,
      Nat.lt_of_lt_of_le hf verticesFit,
      Nat.lt_of_lt_of_le hs verticesFit⟩

/-- The three arrays are the only runtime fields. The row-alignment
    proofs are erased, and no source array is retained. -/
structure Buffer (bits : Nat) where
  private mk ::
  tag : Array (Word bits)
  first : Array (Word bits)
  second : Array (Word bits)
  first_size : first.size = tag.size
  second_size : second.size = tag.size

def rows (b : Buffer bits) : Nat := b.tag.size

def cells (b : Buffer bits) : Nat :=
  b.tag.size + b.first.size + b.second.size

theorem cells_eq (b : Buffer bits) : cells b = 3 * rows b := by
  simp only [cells, rows, b.first_size, b.second_size]
  omega

def serialize (src : Array (Option (PaperB.LabelledQuotient.CutPair H)))
    (verticesFit : H.vertexCount ≤ 2 ^ bits) : Buffer bits where
  tag := Array.ofFn (fun i : Fin src.size =>
    ⟨tagCode (src[i.val]'(i.isLt)),
      (row_fits verticesFit (src[i.val]'(i.isLt))).1⟩)
  first := Array.ofFn (fun i : Fin src.size =>
    ⟨firstCode (src[i.val]'(i.isLt)),
      (row_fits verticesFit (src[i.val]'(i.isLt))).2.1⟩)
  second := Array.ofFn (fun i : Fin src.size =>
    ⟨secondCode (src[i.val]'(i.isLt)),
      (row_fits verticesFit (src[i.val]'(i.isLt))).2.2⟩)
  first_size := by simp
  second_size := by simp

theorem rows_seal (src : Array (Option (PaperB.LabelledQuotient.CutPair H)))
    (verticesFit : H.vertexCount ≤ 2 ^ bits) :
    rows (serialize src verticesFit) = src.size := by
  simp [rows, serialize]

theorem cells_seal (src : Array (Option (PaperB.LabelledQuotient.CutPair H)))
    (verticesFit : H.vertexCount ≤ 2 ^ bits) :
    cells (serialize src verticesFit) = 3 * src.size := by
  rw [cells_eq, rows_seal]

/- Each reader is one array access at the supplied row address. -/
def tagAt (b : Buffer bits) (a : Nat) (ha : a < rows b) : Word bits :=
  b.tag[a]'ha

def firstAt (b : Buffer bits) (a : Nat) (ha : a < rows b) : Word bits :=
  b.first[a]'(by rw [b.first_size]; exact ha)

def secondAt (b : Buffer bits) (a : Nat) (ha : a < rows b) : Word bits :=
  b.second[a]'(by rw [b.second_size]; exact ha)

/-- Proof-only link between each physical read and its source row. -/
structure Represents (b : Buffer bits)
    (src : Array (Option (PaperB.LabelledQuotient.CutPair H))) : Prop where
  size_eq : rows b = src.size
  tag_eq : ∀ (a : Nat) (ha : a < rows b) (hs : a < src.size),
    (tagAt b a ha).val = tagCode (src[a]'hs)
  first_eq : ∀ (a : Nat) (ha : a < rows b) (hs : a < src.size),
    (firstAt b a ha).val = firstCode (src[a]'hs)
  second_eq : ∀ (a : Nat) (ha : a < rows b) (hs : a < src.size),
    (secondAt b a ha).val = secondCode (src[a]'hs)

theorem seal_represents (src : Array (Option (PaperB.LabelledQuotient.CutPair H)))
    (verticesFit : H.vertexCount ≤ 2 ^ bits) :
    Represents (serialize src verticesFit) src where
  size_eq := rows_seal src verticesFit
  tag_eq a ha hs := by
    simp only [tagAt, serialize, Array.getElem_ofFn]
  first_eq a ha hs := by
    simp only [firstAt, serialize, Array.getElem_ofFn]
  second_eq a ha hs := by
    simp only [secondAt, serialize, Array.getElem_ofFn]

/-- One bounds check and at most three direct reads. No scan, decoding
    pass, source lookup, or endpoint reordering occurs here. -/
def matchesKey (b : Buffer bits) (a : Nat)
    (u v : Fin H.vertexCount) : Bool :=
  if ha : a < rows b then
    decide ((tagAt b a ha).val = 1) &&
      (decide ((firstAt b a ha).val = u.val) &&
       decide ((secondAt b a ha).val = v.val))
  else false

theorem matches_eq_true_iff {b : Buffer bits}
    {src : Array (Option (PaperB.LabelledQuotient.CutPair H))}
    (r : Represents b src) (a : Nat) (u v : Fin H.vertexCount) :
    matchesKey b a u v = true ↔
      ∃ p : PaperB.LabelledQuotient.CutPair H,
        src[a]? = some (some p) ∧ p.fst = u ∧ p.snd = v := by
  by_cases ha : a < rows b
  · have hs : a < src.size := by simpa only [r.size_eq] using ha
    rw [matchesKey, dif_pos ha, r.tag_eq a ha hs, r.first_eq a ha hs,
      r.second_eq a ha hs, getElem?_def, dif_pos hs]
    cases (src[a]'hs) with
    | none =>
      simp [tagCode, firstCode, secondCode]
    | some p =>
      have hu : p.fst.val = u.val ↔ p.fst = u :=
        ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      have hv : p.snd.val = v.val ↔ p.snd = v :=
        ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      constructor
      · intro ht
        have hends : p.fst = u ∧ p.snd = v := by
          simpa [tagCode, firstCode, secondCode, hu, hv] using ht
        exact ⟨p, rfl, hends.1, hends.2⟩
      · rintro ⟨p', hp, hf, hs'⟩
        have e : p = p' := Option.some.inj (Option.some.inj hp)
        cases e
        simpa [tagCode, firstCode, secondCode, hu, hv] using
          (And.intro hf hs')
  · have hs : ¬ a < src.size := by simpa only [r.size_eq] using ha
    simp [matchesKey, ha, getElem?_def, hs]

/-- Both an out-of-bounds address and an explicitly empty row reject. -/
theorem matches_absent {b : Buffer bits}
    {src : Array (Option (PaperB.LabelledQuotient.CutPair H))}
    (r : Represents b src) (a : Nat) (u v : Fin H.vertexCount)
    (absent : src[a]? = none ∨ src[a]? = some none) :
    matchesKey b a u v = false := by
  cases hm : matchesKey b a u v with
  | false => rfl
  | true =>
    obtain ⟨p, hp, _, _⟩ := (matches_eq_true_iff r a u v).mp hm
    rcases absent with he | he <;> simp [he] at hp

private theorem cutPair_eq_of_endpoints {p q : PaperB.LabelledQuotient.CutPair H}
    (hf : p.fst = q.fst) (hs : p.snd = q.snd) : p = q := by
  cases p with
  | mk pf ps pfr psr pne =>
    cases q with
    | mk qf qs qfr qsr qne =>
      change pf = qf at hf
      change ps = qs at hs
      cases hf
      cases hs
      rfl

theorem matches_pair {b : Buffer bits}
    {src : Array (Option (PaperB.LabelledQuotient.CutPair H))}
    (r : Represents b src) (a : Nat) (q : PaperB.LabelledQuotient.CutPair H) :
    matchesKey b a q.fst q.snd = true ↔ src[a]? = some (some q) := by
  rw [matches_eq_true_iff r a q.fst q.snd]
  constructor
  · rintro ⟨p, hp, hf, hs⟩
    have e : p = q := cutPair_eq_of_endpoints hf hs
    simpa only [e] using hp
  · intro h
    exact ⟨q, h, rfl, rfl⟩

/-- Keep both dictionary key-word comparisons on the physical slices.
    The back-key check does not replace either comparison. -/
theorem worker_key_checks_eq {xs : Array (Word bits)}
    {s : PaperB.RetainedProperLoss.Columns H}
    (d : FlatPairDictionary.Represents xs s)
    (key : PaperB.PairLookup.Key) (i : Nat) (hi : i < s.dict.size) :
    (decide (((workerColumns xs d).first.get i
        (by rw [(workerColumns xs d).first_len]; exact hi)).val = key.1) &&
      decide (((workerColumns xs d).second.get i
        (by rw [(workerColumns xs d).second_len]; exact hi)).val = key.2)) =
    (decide ((s.dict[i]'hi).1 = key.1) &&
      decide ((s.dict[i]'hi).2 = key.2)) := by
  rw [(workerColumns xs d).first_word i hi,
    (workerColumns xs d).second_word i hi]

def validateSlot (b : Buffer bits) (slot : Option Nat)
    (u v : Fin H.vertexCount) : Option Nat :=
  match slot with
  | none => none
  | some a =>
    if a = 0 then none
    else if matchesKey b a u v = true then some a else none

theorem validateSlot_some [DecidableEq (PaperB.LabelledQuotient.CutPair H)] {b : Buffer bits}
    {src : Array (Option (PaperB.LabelledQuotient.CutPair H))}
    (r : Represents b src) (a : Nat) (q : PaperB.LabelledQuotient.CutPair H) :
    validateSlot b (some a) q.fst q.snd =
      (if a ≠ 0 ∧ src[a]? = some (some q) then some a else none) := by
  by_cases h0 : a = 0 <;> simp [validateSlot, h0, matches_pair r a q]

/-- `hit` is the unchanged physical dictionary worker's row result.
    This stage reads its slot and validates it against the sealed back key. -/
def checkedFromHit (xs : Array (Word bits)) (valid : Valid xs)
    (b : Buffer bits) (hit : Option Nat) (u v : Fin H.vertexCount) :
    Option Nat :=
  validateSlot b (readHitSlot xs valid hit) u v

theorem checkedFromHit_eq {xs : Array (Word bits)} {b : Buffer bits}
    {s : PaperB.RetainedProperLoss.Columns H}
    [DecidableEq (PaperB.LabelledQuotient.CutPair H)]
    (d : FlatPairDictionary.Represents xs s) (r : Represents b s.back)
    (key : PaperB.PairLookup.Key) (q : PaperB.LabelledQuotient.CutPair H)
    (hit : Option Nat)
    (hit_eq : hit = (PaperB.PairLookup.lookup s.dict key).1) :
    checkedFromHit xs d.valid b hit q.fst q.snd = s.checked key q := by
  unfold checkedFromHit
  rw [worker_hit_slot_eq d key hit hit_eq]
  unfold PaperB.RetainedProperLoss.Columns.checked
  cases (PaperB.PairLookup.lookup s.dict key).1 with
  | none => rfl
  | some i =>
    simpa only [Option.map_some] using validateSlot_some r ((s.slots[i]?).getD 0) q

theorem checkedFromHit_seal {xs : Array (Word bits)}
    {s : PaperB.RetainedProperLoss.Columns H}
    [DecidableEq (PaperB.LabelledQuotient.CutPair H)]
    (d : FlatPairDictionary.Represents xs s)
    (verticesFit : H.vertexCount ≤ 2 ^ bits)
    (key : PaperB.PairLookup.Key) (q : PaperB.LabelledQuotient.CutPair H)
    (hit : Option Nat)
    (hit_eq : hit = (PaperB.PairLookup.lookup s.dict key).1) :
    checkedFromHit xs d.valid (serialize s.back verticesFit) hit q.fst q.snd =
      s.checked key q :=
  checkedFromHit_eq d (seal_represents s.back verticesFit) key q hit hit_eq

end PaperB.ForestSlimIndex.FlatPairDictionary.BackKey
