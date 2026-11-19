import PaperB.OracleMemoryLayout
import PaperB.OracleContract

namespace PaperB.EX52.UniformArena

open ExplicitOracle (Counts Widths Table)

/-- The reservation depends only on the declared vertex and arc counts.
    In particular, no transformed graph or reachability result is needed. -/
def worstCounts (n m : Nat) : Counts n m where
  nH := 2 * n
  mH := m
  pairCount := 2 * n
  nH_le := Nat.le_refl _
  mH_le := Nat.le_refl _
  pairCount_le := Nat.le_refl _

/-- Fix `w` for the deployment. The slack then has no dependence on `n` or `m`. -/
def wordSlack (w : Widths) : Nat :=
  Nat.log2 (ExplicitOracle.addressCoeff w) + 1

abbrev bits (w : Widths) (n m : Nat) : Nat :=
  OracleContract.wordBits (wordSlack w) n m

theorem memoryLayout_bits_eq (w : Widths) (n m : Nat) :
    ExplicitOracle.bits w n m = bits w n m :=
  rfl

def builderLayout (w : Widths) (n m : Nat) :
    PaperB.RamProgram.Layout (bits w n m) :=
  ExplicitOracle.builderLayout w (worstCounts n m)

def queryLayout (w : Widths) (n m : Nat) :
    PaperB.RamProgram.Layout (bits w n m) :=
  ExplicitOracle.queryLayout w (worstCounts n m)

/-- Preserve the upstream seal type, including its dependent indices.
    Its word index is definitionally `bits w n m`, so no cast is needed. -/
abbrev sealLayout (w : Widths) (n m : Nat) :=
  ExplicitOracle.sealLayout w (worstCounts n m)

abbrev sealedWords (w : Widths) (n m : Nat) : Nat :=
  (sealLayout w n m).k

theorem sealedWords_eq (w : Widths) (n m : Nat) :
    sealedWords w n m = ExplicitOracle.retainedWords w (worstCounts n m) :=
  rfl

theorem query_input_eq_sealed (w : Widths) (n m : Nat) :
    (queryLayout w n m).inputCap = sealedWords w n m :=
  rfl

theorem query_workCap_eq_zero (w : Widths) (n m : Nat) :
    (queryLayout w n m).workCap = 0 :=
  rfl

/-- Logical header charge for `WordIndex.vertices` and `WordIndex.bits`.
    This is separate from the flat payload and is not an accounting of
    Lean's runtime object or array representation. -/
def indexHeaderWords : Nat := 2

/-- A conservative allocation budget: the entire builder arena, a fresh
    sealed payload, the index header, and even the fixed query registers
    are charged together. -/
def peakWords (w : Widths) (n m : Nat) : Nat :=
  PaperB.RamProgram.footprint (builderLayout w n m) +
    sealedWords w n m + w.queryRegs + indexHeaderWords

/-- The immutable payload and header plus the query's fixed registers. -/
def queryWords (w : Widths) (n m : Nat) : Nat :=
  PaperB.RamProgram.footprint (queryLayout w n m) + indexHeaderWords

theorem queryWords_eq (w : Widths) (n m : Nat) :
    queryWords w n m = sealedWords w n m + w.queryRegs + indexHeaderWords := by
  change
    ExplicitOracle.retainedWords w (worstCounts n m) + 0 + w.queryRegs +
        indexHeaderWords =
      ExplicitOracle.retainedWords w (worstCounts n m) + w.queryRegs +
        indexHeaderWords
  rw [Nat.add_zero]

private theorem fixed_le_scale (n m x : Nat) :
    x ≤ ExplicitOracle.scale n m * x := by
  have hs : 1 ≤ ExplicitOracle.scale n m := by
    unfold ExplicitOracle.scale
    omega
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right x hs

theorem peakWords_le_scaled (w : Widths) (n m : Nat) :
    peakWords w n m ≤ ExplicitOracle.scale n m * ExplicitOracle.addressCoeff w := by
  have hb :
      PaperB.RamProgram.footprint (builderLayout w n m) + sealedWords w n m ≤
        ExplicitOracle.scale n m * ExplicitOracle.simultaneousCoeff w :=
    ExplicitOracle.builder_and_seal_bound w (worstCounts n m)
  have hq := fixed_le_scale n m w.queryRegs
  have hh := fixed_le_scale n m indexHeaderWords
  simpa only [peakWords, ExplicitOracle.addressCoeff, Nat.mul_add,
    indexHeaderWords] using Nat.add_le_add (Nat.add_le_add hb hq) hh

/-- Strict, so the aggregate one-past bound also fits the word width. -/
theorem peakWords_fit (w : Widths) (n m : Nat) :
    peakWords w n m < 2 ^ bits w n m :=
  Nat.lt_of_le_of_lt (peakWords_le_scaled w n m)
    (ExplicitOracle.budget_fits w n m)

theorem queryWords_fit (w : Widths) (n m : Nat) :
    queryWords w n m < 2 ^ bits w n m := by
  apply Nat.lt_of_le_of_lt _ (peakWords_fit w n m)
  rw [queryWords_eq, peakWords]
  omega

/-- Explicit deployment constants for the two linear bounds. -/
def buildCoeff (w : Widths) : Nat :=
  2 * ExplicitOracle.addressCoeff w

def queryCoeff (w : Widths) : Nat :=
  ExplicitOracle.retainedCoeff w + w.queryRegs + indexHeaderWords

theorem peakWords_le_linear (w : Widths) (n m : Nat) (hn : 1 ≤ n) :
    peakWords w n m ≤ buildCoeff w * (n + m) := by
  have hs : ExplicitOracle.scale n m ≤ 2 * (n + m) := by
    unfold ExplicitOracle.scale
    omega
  calc
    peakWords w n m ≤ ExplicitOracle.scale n m * ExplicitOracle.addressCoeff w :=
      peakWords_le_scaled w n m
    _ ≤ (2 * (n + m)) * ExplicitOracle.addressCoeff w :=
      Nat.mul_le_mul_right _ hs
    _ = buildCoeff w * (n + m) := by
      unfold buildCoeff
      ac_rfl

theorem queryWords_le_linear (w : Widths) (n m : Nat) (hn : 1 ≤ n) :
    queryWords w n m ≤ queryCoeff w * n := by
  have hr : sealedWords w n m ≤ n * ExplicitOracle.retainedCoeff w :=
    ExplicitOracle.retainedWords_le w (worstCounts n m)
  have hq : w.queryRegs ≤ n * w.queryRegs := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right w.queryRegs hn
  have hh : indexHeaderWords ≤ n * indexHeaderWords := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right indexHeaderWords hn
  rw [queryWords_eq, Nat.mul_comm (queryCoeff w) n]
  simpa only [queryCoeff, Nat.mul_add] using
    Nat.add_le_add (Nat.add_le_add hr hq) hh

theorem declared_counts_fit (w : Widths) (n m : Nat) :
    n < 2 ^ bits w n m ∧ m < 2 ^ bits w n m ∧
      2 * n < 2 ^ bits w n m :=
  let h := ExplicitOracle.count_values_fit w (worstCounts n m)
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem sealedWords_fit (w : Widths) (n m : Nat) :
    sealedWords w n m < 2 ^ bits w n m :=
  (ExplicitOracle.caps_fit w (worstCounts n m)).2.2.2

/-- Every reserved payload slot, used or unused, has a word address.
    The embedding preserves the slot number. -/
def sealedAddress (w : Widths) (n m : Nat) (i : Fin (sealedWords w n m)) :
    Fin (2 ^ bits w n m) :=
  ⟨i.val, Nat.lt_trans i.isLt (sealedWords_fit w n m)⟩

/-- The query sees exactly the reserved prefix as its input capacity.
    Nothing at or beyond the exclusive seal cut is a query input slot. -/
theorem query_slot_iff (w : Widths) (n m a : Nat) :
    a < (queryLayout w n m).inputCap ↔ a < sealedWords w n m :=
  Iff.rfl

theorem outside_seal_not_query_slot (w : Widths) (n m a : Nat)
    (ha : sealedWords w n m ≤ a) :
    ¬ a < (queryLayout w n m).inputCap := by
  rw [query_input_eq_sealed]
  omega

private theorem cut_mono (t : Table) {a b : Nat} (h : a ≤ b) :
    t.cut a ≤ t.cut b := by
  induction b with
  | zero =>
      have e : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases hab : a ≤ b
      · have hs : t.cut b ≤ t.cut (b + 1) := by
          change t.cut b ≤ t.cut b + t.rows b * t.width b
          omega
        exact Nat.le_trans (ih hab) hs
      · have e : a = b + 1 := by omega
        subst a
        exact Nat.le_refl _

/-- A rectangle contained in the sealed prefix cannot spill out of that
    prefix, even on a reserved row that the builder does not use. The
    bounds are on reserved rows and fields, not on live rows. In particular,
    a zero-width rectangle supplies no field satisfying `hfield`. -/
theorem reserved_field_lt_seal (w : Widths) (n m : Nat)
    (t : Table) {blocks i row field : Nat}
    (hend : t.cut blocks ≤ sealedWords w n m)
    (hi : i < blocks) (hrow : row < t.rows i) (hfield : field < t.width i) :
    t.cut i + row * t.width i + field < sealedWords w n m := by
  have hlocal : row * t.width i + field < t.rows i * t.width i := by
    calc
      row * t.width i + field < row * t.width i + t.width i :=
        Nat.add_lt_add_left hfield _
      _ = (row + 1) * t.width i := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ t.rows i * t.width i :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hrow)
  have hnext : t.cut i + row * t.width i + field < t.cut (i + 1) := by
    change t.cut i + row * t.width i + field <
      t.cut i + t.rows i * t.width i
    omega
  exact Nat.lt_of_lt_of_le hnext
    (Nat.le_trans (cut_mono t (Nat.succ_le_of_lt hi)) hend)

/- These are prebuild layout and capacity facts only. They do not assert
   that a builder initializes the padding, that a query reads only live
   records, or that any program runs within these allocations. -/

end PaperB.EX52.UniformArena
