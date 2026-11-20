import PaperB.RamStaticLCA

open PaperB.Machine (Word)
open PaperB.RamProgram

set_option maxHeartbeats 2000000

namespace PaperB.EX53.OriginalColumns

def cellCount (n : Nat) : Nat := 3 + 3 * n

variable {n bits : Nat}

/-- Supply this for the exact final tables passed to `serialize`. No depth bound
    for a different table or slot numbering is used. -/
abbrev OriginalReaderFinalDepthFits
    (bits : Nat) (T : _root_.EX16.Tables (Fin n)) : Prop :=
  ∀ v, T.depth v < 2 ^ bits

theorem OriginalReaderFinalDepthFits.of_depth_le
    {T : _root_.EX16.Tables (Fin n)} {d : Nat}
    (h : ∀ v, T.depth v ≤ d) (hd : d < 2 ^ bits) :
    OriginalReaderFinalDepthFits bits T :=
  fun v => Nat.lt_of_le_of_lt (h v) hd

private theorem idsFitOf (fit : cellCount n ≤ 2 ^ bits) :
    n ≤ 2 ^ bits := by
  unfold cellCount at fit
  omega

private theorem depthBaseFit (fit : cellCount n ≤ 2 ^ bits) :
    3 + 2 * n < 2 ^ bits := by
  unfold cellCount at fit
  by_cases hn : n = 0
  · -- At n = 0 all three bases are 3. A power of two that is ≥ 3 is > 3.
    cases bits with
    | zero => simp [hn] at fit
    | succ b =>
      rw [Nat.pow_succ] at fit ⊢
      omega
  · omega

private def headBase (fit : cellCount n ≤ 2 ^ bits) : Word bits :=
  ⟨3, by have h := depthBaseFit fit; omega⟩

private def parentBase (fit : cellCount n ≤ 2 ^ bits) : Word bits :=
  ⟨3 + n, by have h := depthBaseFit fit; omega⟩

private def depthBase (fit : cellCount n ≤ 2 ^ bits) : Word bits :=
  ⟨3 + 2 * n, depthBaseFit fit⟩

private inductive Cell (n : Nat) where
  | headHeader
  | parentHeader
  | depthHeader
  | head (v : Fin n)
  | parent (v : Fin n)
  | depth (v : Fin n)

private def locate (i : Fin (cellCount n)) : Cell n :=
  if hh : i.val < 3 then
    if i.val = 0 then .headHeader
    else if i.val = 1 then .parentHeader
    else .depthHeader
  else if h : i.val < 3 + n then
    .head ⟨i.val - 3, by omega⟩
  else if h : i.val < 3 + 2 * n then
    .parent ⟨i.val - (3 + n), by omega⟩
  else
    .depth ⟨i.val - (3 + 2 * n), by
      have hi : i.val < 3 + 3 * n := i.isLt
      omega⟩

private theorem locate_head (v : Fin n) (hi : 3 + v.val < cellCount n) :
    locate ⟨3 + v.val, hi⟩ = Cell.head v := by
  have hv := v.isLt
  have h0 : ¬ (3 + v.val < 3) := by omega
  have h1 : 3 + v.val < 3 + n := by omega
  simp only [locate, Fin.val_mk, dif_neg h0, dif_pos h1]
  exact congrArg Cell.head (Fin.ext (by
    change 3 + v.val - 3 = v.val
    omega))

private theorem locate_parent (v : Fin n)
    (hi : 3 + n + v.val < cellCount n) :
    locate ⟨3 + n + v.val, hi⟩ = Cell.parent v := by
  have hv := v.isLt
  have h0 : ¬ (3 + n + v.val < 3) := by omega
  have h1 : ¬ (3 + n + v.val < 3 + n) := by omega
  have h2 : 3 + n + v.val < 3 + 2 * n := by omega
  simp only [locate, Fin.val_mk, dif_neg h0, dif_neg h1, dif_pos h2]
  exact congrArg Cell.parent (Fin.ext (by
    change 3 + n + v.val - (3 + n) = v.val
    omega))

private theorem locate_depth (v : Fin n)
    (hi : 3 + 2 * n + v.val < cellCount n) :
    locate ⟨3 + 2 * n + v.val, hi⟩ = Cell.depth v := by
  have h0 : ¬ (3 + 2 * n + v.val < 3) := by omega
  have h1 : ¬ (3 + 2 * n + v.val < 3 + n) := by omega
  have h2 : ¬ (3 + 2 * n + v.val < 3 + 2 * n) := by omega
  simp only [locate, Fin.val_mk, dif_neg h0, dif_neg h1, dif_neg h2]
  exact congrArg Cell.depth (Fin.ext (by
    change 3 + 2 * n + v.val - (3 + 2 * n) = v.val
    omega))

private def emit (T : _root_.EX16.Tables (Fin n))
    (fit : cellCount n ≤ 2 ^ bits)
    (depthFit : OriginalReaderFinalDepthFits bits T)
    (i : Fin (cellCount n)) : Word bits :=
  match locate i with
  | .headHeader => headBase fit
  | .parentHeader => parentBase fit
  | .depthHeader => depthBase fit
  | .head v => PaperB.EX53.vertexWord (idsFitOf fit) (T.head v)
  | .parent v => PaperB.EX53.vertexWord (idsFitOf fit) (T.parent v)
  | .depth v => ⟨T.depth v, depthFit v⟩

/-- Local placement: the three headers, then heads, parents, and depths.
    All bases in the headers are relative to the start of this array. -/
def buildInput (T : _root_.EX16.Tables (Fin n))
    (fit : cellCount n ≤ 2 ^ bits)
    (depthFit : OriginalReaderFinalDepthFits bits T) :
    Input (PaperB.EX53.layout bits (cellCount n) fit) where
  words := Array.ofFn (emit T fit depthFit)
  size_eq := by
    change (Array.ofFn (emit T fit depthFit)).size = cellCount n
    simp

private theorem buildInput_get (T : _root_.EX16.Tables (Fin n))
    (fit : cellCount n ≤ 2 ^ bits)
    (depthFit : OriginalReaderFinalDepthFits bits T)
    (i : Nat) (hi : i < cellCount n) :
    (buildInput T fit depthFit).words[i]? =
      some (emit T fit depthFit ⟨i, hi⟩) := by
  have h : i < (buildInput T fit depthFit).words.size := by
    change i < (Array.ofFn (emit T fit depthFit)).size
    simpa using hi
  rw [getElem?_pos (buildInput T fit depthFit).words i h]
  change some ((Array.ofFn (emit T fit depthFit))[i]'h) =
    some (emit T fit depthFit ⟨i, hi⟩)
  exact congrArg some (Array.getElem_ofFn (f := emit T fit depthFit) h)

def buildPacked (T : _root_.EX16.Tables (Fin n))
    (fit : cellCount n ≤ 2 ^ bits)
    (depthFit : OriginalReaderFinalDepthFits bits T) :
    PaperB.EX53.Packed (buildInput T fit depthFit) T where
  idsFit := idsFitOf fit
  headersFit := by
    change 3 ≤ cellCount n
    unfold cellCount
    omega
  depthFits := depthFit
  headBase := headBase fit
  parentBase := parentBase fit
  depthBase := depthBase fit
  headHeader := by
    rw [buildInput_get T fit depthFit 0 (by unfold cellCount; omega)] <;> rfl
  parentHeader := by
    rw [buildInput_get T fit depthFit 1 (by unfold cellCount; omega)] <;> rfl
  depthHeader := by
    rw [buildInput_get T fit depthFit 2 (by unfold cellCount; omega)] <;> rfl
  headCell := by
    intro v
    change (buildInput T fit depthFit).words[3 + v.val]? =
      some (PaperB.EX53.vertexWord (idsFitOf fit) (T.head v))
    have hv := v.isLt
    have hi : 3 + v.val < cellCount n := by unfold cellCount; omega
    rw [buildInput_get T fit depthFit _ hi]
    simp only [emit, locate_head]
  parentCell := by
    intro v
    change (buildInput T fit depthFit).words[3 + n + v.val]? =
      some (PaperB.EX53.vertexWord (idsFitOf fit) (T.parent v))
    have hv := v.isLt
    have hi : 3 + n + v.val < cellCount n := by unfold cellCount; omega
    rw [buildInput_get T fit depthFit _ hi]
    simp only [emit, locate_parent]
  depthCell := by
    intro v
    change (buildInput T fit depthFit).words[3 + 2 * n + v.val]? =
      some (⟨T.depth v, depthFit v⟩ : Word bits)
    have hv := v.isLt
    have hi : 3 + 2 * n + v.val < cellCount n := by unfold cellCount; omega
    rw [buildInput_get T fit depthFit _ hi]
    simp only [emit, locate_depth]

structure Sealed (T : _root_.EX16.Tables (Fin n))
    (fit : cellCount n ≤ 2 ^ bits) where
  input : Input (PaperB.EX53.layout bits (cellCount n) fit)
  packed : PaperB.EX53.Packed input T
  width : input.words.size ≤ 2 ^ bits

def serialize (T : _root_.EX16.Tables (Fin n))
    (fit : cellCount n ≤ 2 ^ bits)
    (depthFit : OriginalReaderFinalDepthFits bits T) : Sealed T fit where
  input := buildInput T fit depthFit
  packed := buildPacked T fit depthFit
  width := by
    calc
      (buildInput T fit depthFit).words.size = cellCount n :=
        (buildInput T fit depthFit).size_eq
      _ ≤ 2 ^ bits := fit

/-- Supplied prices for reads of the actual `T`. These are cost premises,
    not claims about the evaluation time of arbitrary Lean functions. -/
structure ReadCosts (T : _root_.EX16.Tables (Fin n)) where
  headCost : Fin n → Nat
  parentCost : Fin n → Nat
  depthCost : Fin n → Nat
  bound : Nat
  head_le : ∀ v, headCost v ≤ bound
  parent_le : ∀ v, parentCost v ≤ bound
  depth_le : ∀ v, depthCost v ≤ bound

structure Bill where
  indexed : Nat
  source : Nat

private def readPrice {T : _root_.EX16.Tables (Fin n)}
    (C : ReadCosts T) (i : Fin (cellCount n)) : Nat :=
  match locate i with
  | .headHeader => 0
  | .parentHeader => 0
  | .depthHeader => 0
  | .head v => C.headCost v
  | .parent v => C.parentCost v
  | .depth v => C.depthCost v

/-- One indexed output charge per cell. Source reads are billed separately,
    using the same dispatch as `emit`. -/
def cellBill {T : _root_.EX16.Tables (Fin n)}
    (C : ReadCosts T) (i : Fin (cellCount n)) : Bill :=
  ⟨1, readPrice C i⟩

private theorem readPrice_le {T : _root_.EX16.Tables (Fin n)}
    (C : ReadCosts T) (i : Fin (cellCount n)) :
    readPrice C i ≤ C.bound := by
  unfold readPrice
  cases locate i with
  | headHeader => exact Nat.zero_le _
  | parentHeader => exact Nat.zero_le _
  | depthHeader => exact Nat.zero_le _
  | head v => exact C.head_le v
  | parent v => exact C.parent_le v
  | depth v => exact C.depth_le v

private theorem readPrice_header {T : _root_.EX16.Tables (Fin n)}
    (C : ReadCosts T) (i : Fin (cellCount n)) (hi : i.val < 3) :
    readPrice C i = 0 := by
  by_cases h0 : i.val = 0
  · simp [readPrice, locate, hi, h0]
  · by_cases h1 : i.val = 1
    · simp [readPrice, locate, hi, h0, h1]
    · simp [readPrice, locate, hi, h0, h1]

private def prefixSum {m : Nat} (p : Fin m → Nat) :
    (k : Nat) → k ≤ m → Nat
  | 0, _ => 0
  | k + 1, hk => prefixSum p k (by omega) + p ⟨k, by omega⟩

private theorem prefixSum_ones {m : Nat} (k : Nat) (hk : k ≤ m) :
    prefixSum (fun _ : Fin m => 1) k hk = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k ≤ m := by omega
    rw [prefixSum, ih hk']

private theorem prefixSum_le_after_headers {m : Nat} (p : Fin m → Nat)
    (b : Nat) (hp : ∀ i, p i ≤ b)
    (hz : ∀ i, i.val < 3 → p i = 0) (k : Nat) (hk : k ≤ m) :
    prefixSum p k hk ≤ (k - 3) * b := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hk' : k ≤ m := by omega
    have hkm : k < m := by omega
    have hprev := ih hk'
    rw [prefixSum]
    by_cases h : k < 3
    · rw [hz ⟨k, hkm⟩ h, Nat.add_zero]
      have hsub : k - 3 = 0 := by omega
      rw [hsub, Nat.zero_mul] at hprev
      exact Nat.le_trans hprev (Nat.zero_le _)
    · have hsub : k + 1 - 3 = (k - 3) + 1 := by omega
      rw [hsub, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add hprev (hp ⟨k, hkm⟩)

/-- The sum of the per-cell charges. This ledger is not run by `serialize`. -/
def bill {T : _root_.EX16.Tables (Fin n)} (C : ReadCosts T) : Bill :=
  ⟨prefixSum (fun i => (cellBill C i).indexed) (cellCount n) (Nat.le_refl _),
   prefixSum (fun i => (cellBill C i).source) (cellCount n) (Nat.le_refl _)⟩

theorem bill_indexed {T : _root_.EX16.Tables (Fin n)} (C : ReadCosts T) :
    (bill C).indexed = cellCount n :=
  prefixSum_ones (cellCount n) (Nat.le_refl _)

theorem bill_source_le {T : _root_.EX16.Tables (Fin n)} (C : ReadCosts T) :
    (bill C).source ≤ (3 * n) * C.bound := by
  change prefixSum (readPrice C) (cellCount n) (Nat.le_refl _) ≤ _
  have h := prefixSum_le_after_headers (readPrice C) C.bound
    (readPrice_le C) (readPrice_header C) (cellCount n) (Nat.le_refl _)
  have hsub : cellCount n - 3 = 3 * n := by unfold cellCount; omega
  simpa only [hsub] using h

theorem seal_bill {T : _root_.EX16.Tables (Fin n)}
    (fit : cellCount n ≤ 2 ^ bits)
    (depthFit : OriginalReaderFinalDepthFits bits T) (C : ReadCosts T) :
    (bill C).indexed = (serialize T fit depthFit).input.words.size ∧
    (bill C).source ≤ (3 * n) * C.bound := by
  refine ⟨?_, bill_source_le C⟩
  calc
    (bill C).indexed = cellCount n := bill_indexed C
    _ = (serialize T fit depthFit).input.words.size :=
      (serialize T fit depthFit).input.size_eq.symm

end PaperB.EX53.OriginalColumns
