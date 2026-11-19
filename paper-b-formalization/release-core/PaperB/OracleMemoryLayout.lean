import PaperB.SealedBuild

set_option autoImplicit false

namespace PaperB.EX52.ExplicitOracle

open PaperB.Machine (Word)
open PaperB.RamProgram (Layout Input State)

structure Counts (n m : Nat) where
  nH : Nat
  mH : Nat
  pairCount : Nat
  nH_le : nH ≤ 2 * n
  mH_le : mH ≤ m
  pairCount_le : pairCount ≤ nH

/-- Supply the fixed word widths of the record formats. A zero-width
    record has no addressable fields. -/
structure Widths where
  inputVertex : Nat
  inputArc : Nat
  translation : Nat
  vertexRecord : Nat
  pairRecord : Nat
  vertexInterval : Nat
  pairInterval : Nat
  originalVertexScan : Nat
  originalArcScan : Nat
  transformedHeads : Nat
  transformedArcs : Nat
  vertexArray : Nat
  arcArray : Nat
  pairArray : Nat
  groupOffsets : Nat
  groupItems : Nat
  buildRegs : Nat
  queryRegs : Nat

/-- A block is a row-major rectangle of word slots. `cut i` is its
    concrete base, and `cut (i+1)` is its exclusive end. -/
structure Table where
  rows : Nat → Nat
  width : Nat → Nat

def widthSum (w : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => widthSum w i + w i

namespace Table

def cut (t : Table) : Nat → Nat
  | 0 => 0
  | i + 1 => cut t i + t.rows i * t.width i

def cell (t : Table) (i : Nat) (r : Fin (t.rows i))
    (f : Fin (t.width i)) : Nat :=
  t.cut i + r.val * t.width i + f.val

theorem cut_mono (t : Table) {i j : Nat} (h : i ≤ j) :
    t.cut i ≤ t.cut j := by
  induction j with
  | zero =>
    have he : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases hj : i ≤ j
    · have hm := ih hj
      change t.cut i ≤ t.cut j + t.rows j * t.width j
      omega
    · have he : i = j.succ := by omega
      subst i
      exact Nat.le_refl _

theorem cut_le_scaled (t : Table) (k s : Nat)
    (h : ∀ i, i < k → t.rows i ≤ s) :
    t.cut k ≤ s * widthSum t.width k := by
  induction k with
  | zero => simp [cut, widthSum]
  | succ k ih =>
    have hp := ih (fun i hi => h i (by omega))
    have hr := Nat.mul_le_mul_right (t.width k) (h k (by omega))
    change t.cut k + t.rows k * t.width k ≤
      s * (widthSum t.width k + t.width k)
    rw [Nat.mul_add]
    exact Nat.add_le_add hp hr

theorem cell_bounds (t : Table) (i : Nat) (r : Fin (t.rows i))
    (f : Fin (t.width i)) :
    t.cut i ≤ t.cell i r f ∧ t.cell i r f < t.cut (i + 1) := by
  have hr : r.val + 1 ≤ t.rows i := r.isLt
  have hf := f.isLt
  have hm := Nat.mul_le_mul_right (t.width i) hr
  rw [Nat.add_mul, Nat.one_mul] at hm
  change t.cut i ≤ t.cut i + r.val * t.width i + f.val ∧
    t.cut i + r.val * t.width i + f.val < t.cut i + t.rows i * t.width i
  omega

theorem cell_lt_cut (t : Table) {i k : Nat} (hi : i < k)
    (r : Fin (t.rows i)) (f : Fin (t.width i)) :
    t.cell i r f < t.cut k :=
  Nat.lt_of_lt_of_le (t.cell_bounds i r f).2 (t.cut_mono hi)

theorem blocks_ordered (t : Table) {i j : Nat} (h : i < j)
    (r : Fin (t.rows i)) (f : Fin (t.width i))
    (s : Fin (t.rows j)) (g : Fin (t.width j)) :
    t.cell i r f < t.cell j s g :=
  Nat.lt_of_lt_of_le (t.cell_lt_cut h r f) (t.cell_bounds j s g).1

theorem rows_ordered (t : Table) (i : Nat) {r s : Fin (t.rows i)}
    (h : r.val < s.val) (f g : Fin (t.width i)) :
    t.cell i r f < t.cell i s g := by
  have hm := Nat.mul_le_mul_right (t.width i) (show r.val + 1 ≤ s.val from h)
  have hf := f.isLt
  rw [Nat.add_mul, Nat.one_mul] at hm
  unfold cell
  omega

theorem same_block_injective (t : Table) (i : Nat)
    {r s : Fin (t.rows i)} {f g : Fin (t.width i)}
    (h : t.cell i r f = t.cell i s g) : r = s ∧ f = g := by
  have hrs : ¬ r.val < s.val := by
    intro hlt
    have ho := t.rows_ordered i hlt f g
    omega
  have hsr : ¬ s.val < r.val := by
    intro hlt
    have ho := t.rows_ordered i hlt g f
    omega
  have hr : r.val = s.val := by omega
  refine ⟨Fin.ext hr, Fin.ext ?_⟩
  unfold cell at h
  rw [hr] at h
  omega

private theorem cover_cut (t : Table) (k a : Nat) (h : a < t.cut k) :
    ∃ i, i < k ∧ t.cut i ≤ a ∧ a < t.cut (i + 1) := by
  induction k with
  | zero => simp [cut] at h
  | succ k ih =>
    by_cases hk : a < t.cut k
    · obtain ⟨i, hi, hlo, hhi⟩ := ih hk
      exact ⟨i, by omega, hlo, hhi⟩
    · exact ⟨k, Nat.lt_succ_self k, by omega, h⟩

private theorem cover_rectangle (rows w a : Nat) (h : a < rows * w) :
    ∃ (r : Fin rows) (f : Fin w), r.val * w + f.val = a := by
  induction rows with
  | zero => simp at h
  | succ rows ih =>
    by_cases ha : a < rows * w
    · obtain ⟨r, f, hf⟩ := ih ha
      exact ⟨⟨r.val, Nat.lt_trans r.isLt (Nat.lt_succ_self rows)⟩, f, hf⟩
    · have hb : a < rows * w + w := by
        simpa only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] using h
      refine ⟨⟨rows, Nat.lt_succ_self rows⟩, ⟨a - rows * w, by omega⟩, ?_⟩
      change rows * w + (a - rows * w) = a
      omega

/-- No padding or holes between cuts, including when some blocks are empty. -/
theorem cells_cover (t : Table) {lo hi a : Nat}
    (hl : t.cut lo ≤ a) (hh : a < t.cut hi) :
    ∃ i, lo ≤ i ∧ i < hi ∧
      ∃ (r : Fin (t.rows i)) (f : Fin (t.width i)), t.cell i r f = a := by
  obtain ⟨i, hi', hlo, hhi⟩ := cover_cut t hi a hh
  have hli : lo ≤ i := by
    by_cases h : lo ≤ i
    · exact h
    · have hm := t.cut_mono (show i + 1 ≤ lo by omega)
      omega
  change a < t.cut i + t.rows i * t.width i at hhi
  have hd : a - t.cut i < t.rows i * t.width i := by omega
  obtain ⟨r, f, hf⟩ := cover_rectangle (t.rows i) (t.width i) (a - t.cut i) hd
  refine ⟨i, hli, hi', r, f, ?_⟩
  unfold cell
  omega

/-- The base, product, partial sum, and final address all fit. -/
theorem address_parts_fit (t : Table) {bits i k : Nat}
    (hk : t.cut k ≤ 2 ^ bits) (hi : i < k)
    (r : Fin (t.rows i)) (f : Fin (t.width i)) :
    t.cut i < 2 ^ bits ∧ r.val * t.width i < 2 ^ bits ∧
      t.cut i + r.val * t.width i < 2 ^ bits ∧ t.cell i r f < 2 ^ bits := by
  have h := Nat.lt_of_lt_of_le (t.cell_lt_cut hi r f) hk
  unfold cell at h ⊢
  omega

def word (t : Table) {bits i k : Nat} (hk : t.cut k ≤ 2 ^ bits)
    (hi : i < k) (r : Fin (t.rows i)) (f : Fin (t.width i)) : Word bits :=
  ⟨t.cell i r f, Nat.lt_of_lt_of_le (t.cell_lt_cut hi r f) hk⟩

@[simp] theorem word_val (t : Table) {bits i k : Nat}
    (hk : t.cut k ≤ 2 ^ bits) (hi : i < k)
    (r : Fin (t.rows i)) (f : Fin (t.width i)) :
    (t.word hk hi r f).val = t.cell i r f := rfl

end Table

namespace InBlock
abbrev header : Nat := 0
abbrev vertices : Nat := 1
abbrev arcs : Nat := 2
abbrev stop : Nat := 3
end InBlock

namespace WorkBlock
abbrev originalToH : Nat := 0
abbrev vertex : Nat := 1
abbrev pair : Nat := 2
abbrev vertexInterval : Nat := 3
abbrev pairInterval : Nat := 4
abbrev retainedEnd : Nat := 5
abbrev originalVertexScan : Nat := 5
abbrev originalArcScan : Nat := 6
abbrev transformedHeads : Nat := 7
abbrev transformedArcs : Nat := 8
abbrev vertexArray : Nat := 9
abbrev arcArray : Nat := 10
abbrev pairArray : Nat := 11
abbrev groupOffsets : Nat := 12
abbrev groupItems : Nat := 13
abbrev stop : Nat := 14
end WorkBlock

def inputRows (n m : Nat) : Nat → Nat
  | 0 => 1
  | 1 => n
  | 2 => m
  | _ => 0

def inputWidths (w : Widths) : Nat → Nat
  | 0 => 2                         -- n, m
  | 1 => w.inputVertex
  | 2 => w.inputArc
  | _ => 0

variable {n m : Nat}

def workRows (c : Counts n m) : Nat → Nat
  | 0 => n                        -- direct indexing by original vertex ID
  | 1 => c.nH
  | 2 => c.pairCount
  | 3 => c.nH
  | 4 => c.pairCount
  | 5 => n
  | 6 => m
  | 7 => c.nH
  | 8 => c.mH
  | 9 => c.nH
  | 10 => c.mH
  | 11 => c.pairCount
  | 12 => c.nH + 1                 -- includes the terminal group offset
  | 13 => c.pairCount
  | _ => 0

def workWidths (w : Widths) : Nat → Nat
  | 0 => w.translation
  | 1 => w.vertexRecord
  | 2 => w.pairRecord
  | 3 => w.vertexInterval
  | 4 => w.pairInterval
  | 5 => w.originalVertexScan
  | 6 => w.originalArcScan
  | 7 => w.transformedHeads
  | 8 => w.transformedArcs
  | 9 => w.vertexArray
  | 10 => w.arcArray
  | 11 => w.pairArray
  | 12 => w.groupOffsets
  | 13 => w.groupItems
  | _ => 0

def inputTable (w : Widths) (n m : Nat) : Table :=
  ⟨inputRows n m, inputWidths w⟩

def workTable (w : Widths) (c : Counts n m) : Table :=
  ⟨workRows c, workWidths w⟩

/-- Use the named block numbers with these bases. For example, the pair
    base is `n * translation + nH * vertexRecord`; the first scan starts
    at `retainedWords`. No base is rounded up. -/
def inputBase (w : Widths) (n m i : Nat) : Nat := (inputTable w n m).cut i
def workBase (w : Widths) (c : Counts n m) (i : Nat) : Nat := (workTable w c).cut i

def inputWords (w : Widths) (n m : Nat) : Nat := inputBase w n m InBlock.stop
def workWords (w : Widths) (c : Counts n m) : Nat := workBase w c WorkBlock.stop
def retainedWords (w : Widths) (c : Counts n m) : Nat :=
  workBase w c WorkBlock.retainedEnd

theorem inputWords_eq (w : Widths) (n m : Nat) :
    inputWords w n m = 2 + n * w.inputVertex + m * w.inputArc := by
  change 0 + 1 * 2 + n * w.inputVertex + m * w.inputArc = _
  simp only [Nat.zero_add, Nat.one_mul]

theorem retainedWords_eq (w : Widths) (c : Counts n m) :
    retainedWords w c =
      n * w.translation + c.nH * w.vertexRecord + c.pairCount * w.pairRecord +
        c.nH * w.vertexInterval + c.pairCount * w.pairInterval := by
  change 0 + n * w.translation + c.nH * w.vertexRecord + c.pairCount * w.pairRecord +
    c.nH * w.vertexInterval + c.pairCount * w.pairInterval = _
  simp only [Nat.zero_add]

theorem retained_le_work (w : Widths) (c : Counts n m) :
    retainedWords w c ≤ workWords w c :=
  (workTable w c).cut_mono (show WorkBlock.retainedEnd ≤ WorkBlock.stop by decide)

theorem retained_dense (w : Widths) (c : Counts n m) {a : Nat}
    (ha : a < retainedWords w c) :
    ∃ i, i < WorkBlock.retainedEnd ∧
      ∃ (r : Fin (workRows c i)) (f : Fin (workWidths w i)),
        (workTable w c).cell i r f = a := by
  obtain ⟨i, _, hi, r, f, hf⟩ :=
    (workTable w c).cells_cover (lo := 0) (hi := WorkBlock.retainedEnd)
      (Nat.zero_le a) ha
  exact ⟨i, hi, r, f, hf⟩

theorem scratch_dense (w : Widths) (c : Counts n m) {a : Nat}
    (ha : retainedWords w c ≤ a) (hb : a < workWords w c) :
    ∃ i, WorkBlock.retainedEnd ≤ i ∧ i < WorkBlock.stop ∧
      ∃ (r : Fin (workRows c i)) (f : Fin (workWidths w i)),
        (workTable w c).cell i r f = a :=
  (workTable w c).cells_cover (lo := WorkBlock.retainedEnd)
    (hi := WorkBlock.stop) ha hb

theorem retained_before_scratch (w : Widths) (c : Counts n m) {i j : Nat}
    (hi : i < WorkBlock.retainedEnd) (hj : WorkBlock.retainedEnd ≤ j)
    (r : Fin (workRows c i)) (f : Fin (workWidths w i))
    (s : Fin (workRows c j)) (g : Fin (workWidths w j)) :
    (workTable w c).cell i r f < retainedWords w c ∧
      retainedWords w c ≤ (workTable w c).cell j s g :=
  ⟨(workTable w c).cell_lt_cut hi r f,
    Nat.le_trans ((workTable w c).cut_mono hj) ((workTable w c).cell_bounds j s g).1⟩

def scale (n m : Nat) : Nat := n + m + 1

def inputCoeff (w : Widths) : Nat := widthSum (inputWidths w) InBlock.stop
def workCoeff (w : Widths) : Nat := 2 * widthSum (workWidths w) WorkBlock.stop
def retainedCoeff (w : Widths) : Nat :=
  2 * widthSum (workWidths w) WorkBlock.retainedEnd

private theorem inputRows_le (n m i : Nat) (hi : i < InBlock.stop) :
    inputRows n m i ≤ scale n m := by
  change i < 3 at hi
  have he : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases he with rfl | rfl | rfl <;> simp only [inputRows, scale] <;> omega

private theorem retainedRows_le (c : Counts n m) (i : Nat)
    (hi : i < WorkBlock.retainedEnd) : workRows c i ≤ 2 * n := by
  change i < 5 at hi
  have hh := c.nH_le
  have hp := c.pairCount_le
  have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl <;> simp only [workRows] <;> omega

private theorem workRows_le (c : Counts n m) (i : Nat) (hi : i < WorkBlock.stop) :
    workRows c i ≤ 2 * scale n m := by
  change i < 14 at hi
  have hh := c.nH_le
  have hm := c.mH_le
  have hp := c.pairCount_le
  have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
      i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [workRows, scale] <;> omega

theorem inputWords_le (w : Widths) (n m : Nat) :
    inputWords w n m ≤ scale n m * inputCoeff w :=
  (inputTable w n m).cut_le_scaled InBlock.stop (scale n m) (inputRows_le n m)

theorem retainedWords_le (w : Widths) (c : Counts n m) :
    retainedWords w c ≤ n * retainedCoeff w := by
  have h := (workTable w c).cut_le_scaled WorkBlock.retainedEnd (2 * n)
    (retainedRows_le c)
  change retainedWords w c ≤ (2 * n) * widthSum (workWidths w) WorkBlock.retainedEnd
    at h
  calc
    retainedWords w c ≤ (2 * n) * widthSum (workWidths w) WorkBlock.retainedEnd := h
    _ = n * retainedCoeff w := by rw [retainedCoeff, Nat.mul_comm 2 n, Nat.mul_assoc]

theorem workWords_le (w : Widths) (c : Counts n m) :
    workWords w c ≤ scale n m * workCoeff w := by
  have h := (workTable w c).cut_le_scaled WorkBlock.stop (2 * scale n m) (workRows_le c)
  change workWords w c ≤ (2 * scale n m) * widthSum (workWidths w) WorkBlock.stop at h
  calc
    workWords w c ≤ (2 * scale n m) * widthSum (workWidths w) WorkBlock.stop := h
    _ = scale n m * workCoeff w := by
      rw [workCoeff, Nat.mul_comm 2 (scale n m), Nat.mul_assoc]

/-- Capacity accounting only. All scratch blocks coexist in `workWords`.
    The last summand allows a fresh sealed copy to coexist with the entire
    construction arena, including the preallocated input. -/
def simultaneousWords (w : Widths) (c : Counts n m) : Nat :=
  inputWords w n m + workWords w c + w.buildRegs + retainedWords w c

def simultaneousCoeff (w : Widths) : Nat :=
  inputCoeff w + workCoeff w + w.buildRegs + retainedCoeff w

private theorem le_scale_mul (n m x : Nat) : x ≤ scale n m * x := by
  have hs : 1 ≤ scale n m := by unfold scale; omega
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right x hs

theorem simultaneousWords_le (w : Widths) (c : Counts n m) :
    simultaneousWords w c ≤ scale n m * simultaneousCoeff w := by
  have hi := inputWords_le w n m
  have hw := workWords_le w c
  have hg := le_scale_mul n m w.buildRegs
  have hn : n ≤ scale n m := by unfold scale; omega
  have hr := Nat.le_trans (retainedWords_le w c)
    (Nat.mul_le_mul_right (retainedCoeff w) hn)
  unfold simultaneousWords simultaneousCoeff
  simp only [Nat.mul_add]
  omega

/-- The base address width plus a constant number of bits depending only
    on the fixed widths. The strict budget also permits one-past cuts. -/
def addressCoeff (w : Widths) : Nat := simultaneousCoeff w + w.queryRegs + 2

def bits (w : Widths) (n m : Nat) : Nat :=
  (Nat.log2 (scale n m) + 1) + (Nat.log2 (addressCoeff w) + 1)

theorem budget_fits (w : Widths) (n m : Nat) :
    scale n m * addressCoeff w < 2 ^ bits w n m := by
  have hs : 0 < scale n m := by unfold scale; omega
  have hc : addressCoeff w ≠ 0 := by unfold addressCoeff; omega
  have hS : scale n m < 2 ^ (Nat.log2 (scale n m) + 1) :=
    (Nat.log2_lt (Nat.ne_of_gt hs)).mp (Nat.lt_succ_self _)
  have hC : addressCoeff w < 2 ^ (Nat.log2 (addressCoeff w) + 1) :=
    (Nat.log2_lt hc).mp (Nat.lt_succ_self _)
  rw [bits, Nat.pow_add]
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hC hs)
    (Nat.mul_le_mul_right _ (Nat.le_of_lt hS))

theorem simultaneousWords_fit (w : Widths) (c : Counts n m) :
    simultaneousWords w c < 2 ^ bits w n m := by
  have hc : simultaneousCoeff w ≤ addressCoeff w := by unfold addressCoeff; omega
  exact Nat.lt_of_le_of_lt
    (Nat.le_trans (simultaneousWords_le w c) (Nat.mul_le_mul_left _ hc))
    (budget_fits w n m)

theorem caps_fit (w : Widths) (c : Counts n m) :
    inputWords w n m < 2 ^ bits w n m ∧ workWords w c < 2 ^ bits w n m ∧
      w.buildRegs < 2 ^ bits w n m ∧ retainedWords w c < 2 ^ bits w n m := by
  have h := simultaneousWords_fit w c
  unfold simultaneousWords at h
  omega

theorem queryRegs_fit (w : Widths) (n m : Nat) :
    w.queryRegs < 2 ^ bits w n m := by
  have hc : w.queryRegs ≤ addressCoeff w := by unfold addressCoeff; omega
  exact Nat.lt_of_le_of_lt
    (Nat.le_trans (le_scale_mul n m w.queryRegs) (Nat.mul_le_mul_left _ hc))
    (budget_fits w n m)

/-- Counts and inclusive endpoint bounds also fit, independently of any
    assertion about which field a later program writes. -/
theorem count_values_fit (w : Widths) (c : Counts n m) :
    n < 2 ^ bits w n m ∧ m < 2 ^ bits w n m ∧ c.nH < 2 ^ bits w n m ∧
      c.mH < 2 ^ bits w n m ∧ c.pairCount < 2 ^ bits w n m := by
  have hc : 2 ≤ addressCoeff w := by unfold addressCoeff; omega
  have hb := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left (scale n m) hc)
    (budget_fits w n m)
  have hn := c.nH_le
  have hm := c.mH_le
  have hp := c.pairCount_le
  unfold scale at hb
  omega

def builderLayout (w : Widths) (c : Counts n m) : Layout (bits w n m) where
  registerCount := w.buildRegs
  inputCap := inputWords w n m
  workCap := workWords w c
  inputFits := Nat.le_of_lt (caps_fit w c).1
  workFits := Nat.le_of_lt (caps_fit w c).2.1

/-- A read-only sealed-input layout. This specifies capacities, not a
    query implementation or a register sufficiency theorem. -/
def queryLayout (w : Widths) (c : Counts n m) : Layout (bits w n m) where
  registerCount := w.queryRegs
  inputCap := retainedWords w c
  workCap := 0
  inputFits := Nat.le_of_lt (caps_fit w c).2.2.2
  workFits := Nat.zero_le _

def sealLayout (w : Widths) (c : Counts n m) :
    PaperB.SealedBuild.SealLayout (builderLayout w c) where
  registerFits := Nat.le_of_lt (caps_fit w c).2.2.1
  k := retainedWords w c
  k_le_workCap := retained_le_work w c

def sealedInput (w : Widths) (c : Counts n m) (s : State (builderLayout w c)) :
    Input (queryLayout w c) where
  words := PaperB.SealedBuild.copyPrefix (sealLayout w c) s
  size_eq := PaperB.SealedBuild.copyPrefix_size (sealLayout w c) s

def inputAddr (w : Widths) (c : Counts n m) {i : Nat}
    (hi : i < InBlock.stop) (r : Fin (inputRows n m i))
    (f : Fin (inputWidths w i)) : Word (bits w n m) :=
  (inputTable w n m).word (builderLayout w c).inputFits hi r f

def workAddr (w : Widths) (c : Counts n m) {i : Nat}
    (hi : i < WorkBlock.stop) (r : Fin (workRows c i))
    (f : Fin (workWidths w i)) : Word (bits w n m) :=
  (workTable w c).word (builderLayout w c).workFits hi r f

def sealedAddr (w : Widths) (c : Counts n m) {i : Nat}
    (hi : i < WorkBlock.retainedEnd) (r : Fin (workRows c i))
    (f : Fin (workWidths w i)) : Word (bits w n m) :=
  (workTable w c).word (queryLayout w c).inputFits hi r f

/-- Sealing does not rebase any retained address. -/
theorem sealedAddr_eq_workAddr (w : Widths) (c : Counts n m) {i : Nat}
    (hi : i < WorkBlock.retainedEnd) (r : Fin (workRows c i))
    (f : Fin (workWidths w i)) :
    sealedAddr w c hi r f =
      workAddr w c (Nat.lt_of_lt_of_le hi
        (show WorkBlock.retainedEnd ≤ WorkBlock.stop by decide)) r f := rfl

def originalToHAddr (w : Widths) (c : Counts n m) (v : Fin n)
    (f : Fin w.translation) : Word (bits w n m) :=
  sealedAddr w c (i := WorkBlock.originalToH) (by decide) v f

theorem originalToHAddr_val (w : Widths) (c : Counts n m) (v : Fin n)
    (f : Fin w.translation) :
    (originalToHAddr w c v f).val = v.val * w.translation + f.val := by
  change 0 + v.val * w.translation + f.val = _
  rw [Nat.zero_add]

/-- A bound on simultaneous allocated slots, not an execution observation. -/
theorem builder_and_seal_bound (w : Widths) (c : Counts n m) :
    PaperB.RamProgram.footprint (builderLayout w c) + (sealLayout w c).k
      ≤ scale n m * simultaneousCoeff w :=
  simultaneousWords_le w c

end PaperB.EX52.ExplicitOracle
