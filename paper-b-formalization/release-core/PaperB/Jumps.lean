import Challenge

/-! Growing-tree skew-binary `parent` / `depth` / `jump` kernel (Paper B v1.3, Lemma 3.2, EX2.3):
    part 1 — store, persistence, skew-block forest invariant, depth-target traversal, and
    unique ancestor-at-depth correctness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

private def headNat : List Nat → Nat
  | [] => 0
  | x :: _ => x

private def tailNat : List Nat → List Nat
  | [] => []
  | _ :: xs => xs

private theorem list_length_snoc {α : Type} (xs : List α) (x : α) :
    (xs ++ [x]).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons _ tl ih => exact congrArg (· + 1) ih

private theorem nat_strong_ind {P : Nat → Prop}
    (step : ∀ n, (∀ m, m < n → P m) → P n) (n : Nat) : P n := by
  have bounded : ∀ k m, m ≤ k → P m := by
    intro k
    induction k with
    | zero =>
        intro m hm
        have hm0 : m = 0 := by omega
        rw [hm0]
        exact step 0 (fun _ hLt => by omega)
    | succ k ih =>
        intro m hm
        exact step m (fun j hj => ih j (by omega))
  exact bounded n n (Nat.le_refl n)

/-- Concrete per-node record in the growing skew-binary jump forest:
    one `parent`, one `depth`, and one `jump` index per node. -/
structure JumpRecord where
  parent : Nat
  depth : Nat
  jump : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Artificial root record at index `0` (`depth = 0`, `parent = 0`, `jump = 0`). -/
def rootRecord : JumpRecord :=
  { parent := 0, depth := 0, jump := 0 }

/-- Structural index lookup on a record list. -/
def listRecordAt? : List JumpRecord → Nat → Option JumpRecord
  | [], _ => none
  | r :: _, 0 => some r
  | _ :: rs, i + 1 => listRecordAt? rs i

theorem listRecordAt?_lt_none {rs : List JumpRecord} {i : Nat}
    (hge : rs.length ≤ i) : listRecordAt? rs i = none := by
  induction rs generalizing i with
  | nil => rfl
  | cons _ tl ih =>
      cases i with
      | zero =>
          simp only [List.length_cons] at hge
          omega
      | succ j =>
          simp only [List.length_cons] at hge
          exact ih (by omega)

theorem listRecordAt?_append_old (rs : List JumpRecord) (r : JumpRecord)
    {i : Nat} (hi : i < rs.length) :
    listRecordAt? (rs ++ [r]) i = listRecordAt? rs i := by
  induction rs generalizing i with
  | nil =>
      simp only [List.length_nil] at hi
      omega
  | cons _ tl ih =>
      cases i with
      | zero => rfl
      | succ j =>
          simp only [List.length_cons] at hi
          exact ih (by omega)

theorem listRecordAt?_append_new (rs : List JumpRecord) (r : JumpRecord) :
    listRecordAt? (rs ++ [r]) rs.length = some r := by
  induction rs with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Growing forest store indexed `0 .. size - 1` (`0` is the artificial root). -/
structure JumpForest where
  records : List JumpRecord
  deriving DecidableEq, Repr

namespace JumpForest

/-- Initial forest containing only the artificial root `0`. -/
def init : JumpForest :=
  { records := [rootRecord] }

/-- Total number of stored records (`1 + numInserted`). -/
def size (F : JumpForest) : Nat :=
  F.records.length

/-- Number of appended real nodes (`size - 1`). -/
def numInserted (F : JumpForest) : Nat :=
  F.records.length - 1

/-- Checked optional record lookup at index `u`. -/
def recordAt? (F : JumpForest) (u : Nat) : Option JumpRecord :=
  listRecordAt? F.records u

/-- Total record lookup at index `u` (defaults out-of-range indices to `rootRecord`). -/
def recordAt (F : JumpForest) (u : Nat) : JumpRecord :=
  match F.recordAt? u with
  | some r => r
  | none => rootRecord

def parentOf (F : JumpForest) (u : Nat) : Nat :=
  (F.recordAt u).parent

def depthOf (F : JumpForest) (u : Nat) : Nat :=
  (F.recordAt u).depth

def jumpOf (F : JumpForest) (u : Nat) : Nat :=
  (F.recordAt u).jump

/-- New leaf record formed under existing node `p` by Myers's skew-binary merge rule. -/
def mkAppendedRecord (F : JumpForest) (p : Nat) : JumpRecord :=
  let recP := F.recordAt p
  let a := recP.jump
  let recA := F.recordAt a
  let b := recA.jump
  let recB := F.recordAt b
  let len1 := recP.depth - recA.depth
  let len2 := recA.depth - recB.depth
  let j := if 0 < len1 ∧ len1 = len2 then b else p
  { parent := p, depth := recP.depth + 1, jump := j }

/-- Append a new leaf at index `F.size` under parent `p`. -/
def appendLeaf (F : JumpForest) (p : Nat) : JumpForest :=
  { records := F.records ++ [F.mkAppendedRecord p] }

theorem size_init : JumpForest.init.size = 1 := rfl

theorem numInserted_init : JumpForest.init.numInserted = 0 := rfl

theorem size_appendLeaf (F : JumpForest) (p : Nat) :
    (F.appendLeaf p).size = F.size + 1 :=
  list_length_snoc F.records (F.mkAppendedRecord p)

end JumpForest

theorem recordAt?_appendLeaf_old (F : JumpForest) (p : Nat) {u : Nat} (hu : u < F.size) :
    (F.appendLeaf p).recordAt? u = F.recordAt? u :=
  listRecordAt?_append_old F.records (F.mkAppendedRecord p) hu

theorem recordAt?_appendLeaf_new (F : JumpForest) (p : Nat) :
    (F.appendLeaf p).recordAt? F.size = some (F.mkAppendedRecord p) :=
  listRecordAt?_append_new F.records (F.mkAppendedRecord p)

theorem recordAt_appendLeaf_old (F : JumpForest) (p : Nat) {u : Nat} (hu : u < F.size) :
    (F.appendLeaf p).recordAt u = F.recordAt u := by
  unfold JumpForest.recordAt
  rw [recordAt?_appendLeaf_old F p hu]

theorem recordAt_appendLeaf_new (F : JumpForest) (p : Nat) :
    (F.appendLeaf p).recordAt F.size = F.mkAppendedRecord p := by
  unfold JumpForest.recordAt
  rw [recordAt?_appendLeaf_new F p]

theorem parentOf_appendLeaf_old (F : JumpForest) (p : Nat) {u : Nat} (hu : u < F.size) :
    (F.appendLeaf p).parentOf u = F.parentOf u := by
  unfold JumpForest.parentOf
  rw [recordAt_appendLeaf_old F p hu]

theorem depthOf_appendLeaf_old (F : JumpForest) (p : Nat) {u : Nat} (hu : u < F.size) :
    (F.appendLeaf p).depthOf u = F.depthOf u := by
  unfold JumpForest.depthOf
  rw [recordAt_appendLeaf_old F p hu]

theorem jumpOf_appendLeaf_old (F : JumpForest) (p : Nat) {u : Nat} (hu : u < F.size) :
    (F.appendLeaf p).jumpOf u = F.jumpOf u := by
  unfold JumpForest.jumpOf
  rw [recordAt_appendLeaf_old F p hu]

/-- Inductive validity of a growing `JumpForest` built from `init` by appending leaves
    under existing indices `p < F.size` across arbitrary branches. -/
inductive ValidJumpForest : JumpForest → Prop where
  | init : ValidJumpForest JumpForest.init
  | appendLeaf {F : JumpForest} {p : Nat}
      (hF : ValidJumpForest F) (hp : p < F.size) :
      ValidJumpForest (F.appendLeaf p)

namespace JumpForest

/-- Reflexive-transitive multi-step extension order by valid leaf insertions. -/
inductive Extends : JumpForest → JumpForest → Prop where
  | refl (F : JumpForest) : Extends F F
  | step {F₁ F₂ : JumpForest} {p : Nat}
      (hExt : Extends F₁ F₂) (hp : p < F₂.size) :
      Extends F₁ (F₂.appendLeaf p)

theorem Extends.size_le {F₁ F₂ : JumpForest} (h : F₁.Extends F₂) :
    F₁.size ≤ F₂.size := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step F₂ p _ _ ih =>
      have hSz := F₂.size_appendLeaf p
      omega

theorem Extends.recordAt?_eq {F₁ F₂ : JumpForest} (h : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) :
    F₂.recordAt? u = F₁.recordAt? u := by
  induction h with
  | refl => rfl
  | @step F₂ p hExt _ ih =>
      have hu₂ : u < F₂.size := Nat.lt_of_lt_of_le hu hExt.size_le
      rw [recordAt?_appendLeaf_old F₂ p hu₂]
      exact ih

theorem Extends.recordAt_eq {F₁ F₂ : JumpForest} (h : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) :
    F₂.recordAt u = F₁.recordAt u := by
  unfold JumpForest.recordAt
  rw [h.recordAt?_eq hu]

theorem Extends.parentOf_eq {F₁ F₂ : JumpForest} (h : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) :
    F₂.parentOf u = F₁.parentOf u := by
  unfold JumpForest.parentOf
  rw [h.recordAt_eq hu]

theorem Extends.depthOf_eq {F₁ F₂ : JumpForest} (h : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) :
    F₂.depthOf u = F₁.depthOf u := by
  unfold JumpForest.depthOf
  rw [h.recordAt_eq hu]

theorem Extends.jumpOf_eq {F₁ F₂ : JumpForest} (h : F₁.Extends F₂)
    {u : Nat} (hu : u < F₁.size) :
    F₂.jumpOf u = F₁.jumpOf u := by
  unfold JumpForest.jumpOf
  rw [h.recordAt_eq hu]

end JumpForest

/-! ### Concrete Witnesses: Root/Depth Zero, Merge Case (`2^2 - 1`), and Sibling Branching -/

theorem root_has_zero_fields :
    JumpForest.init.recordAt 0 = { parent := 0, depth := 0, jump := 0 } := rfl

/-- Five-node forest witnessing both a `2^2 - 1 = 3` skew merge at node `3` (`0 ← 1 ← 2 ← 3`)
    and nontrivial multi-branching via sibling `4` appended under internal node `1`. -/
def exampleBranchAndMerge : JumpForest :=
  (((JumpForest.init.appendLeaf 0).appendLeaf 1).appendLeaf 2).appendLeaf 1

theorem exampleBranchAndMerge_valid : ValidJumpForest exampleBranchAndMerge :=
  ValidJumpForest.appendLeaf
    (ValidJumpForest.appendLeaf
      (ValidJumpForest.appendLeaf
        (ValidJumpForest.appendLeaf ValidJumpForest.init (by decide))
        (by decide))
      (by decide))
    (by decide)

theorem merge_case_witness :
    exampleBranchAndMerge.recordAt 3 = { parent := 2, depth := 3, jump := 0 } := rfl

theorem branching_case_witness :
    exampleBranchAndMerge.recordAt 2 = { parent := 1, depth := 2, jump := 1 } ∧
      exampleBranchAndMerge.recordAt 4 = { parent := 1, depth := 2, jump := 1 } ∧
      exampleBranchAndMerge.recordAt 3 = { parent := 2, depth := 3, jump := 0 } :=
  ⟨rfl, rfl, rfl⟩

/-! ### Skew-Binary Block Sizes `2^k - 1` and Inductive `ForestInvariant` -/

theorem pow2_pos (k : Nat) : 0 < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
      change 0 < (2 ^ k) * 2
      omega

theorem pow2_succ (k : Nat) : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
  change (2 ^ k) * 2 = 2 ^ k + 2 ^ k
  omega

theorem pow2_strictMono {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b := by
  induction b with
  | zero => omega
  | succ b ih =>
      have hPos : 0 < 2 ^ b := pow2_pos b
      have hStep : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := pow2_succ b
      if hEq : a = b then
        rw [hEq, hStep]
        omega
      else
        have hLt : a < b := by omega
        have hIH : 2 ^ a < 2 ^ b := ih hLt
        rw [hStep]
        omega

theorem lt_of_pow2_lt {a b : Nat} (h : 2 ^ a < 2 ^ b) : a < b := by
  if hLt : a < b then
    exact hLt
  else if hEq : a = b then
    rw [hEq] at h
    omega
  else
    have hGt : b < a := by omega
    have hPowGt : 2 ^ b < 2 ^ a := pow2_strictMono hGt
    omega

/-- Skew-binary block size `2^k - 1` (`1 ≤ k`). -/
def blockSize (k : Nat) : Nat :=
  2 ^ k - 1

/-- Total depth represented by a list of block exponents. -/
def blockSum : List Nat → Nat
  | [] => 0
  | k :: rest => blockSize k + blockSum rest

def AllList (P : Nat → Prop) : List Nat → Prop
  | [] => True
  | x :: xs => P x ∧ AllList P xs

def StrictlyIncreasing : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a < b ∧ StrictlyIncreasing (b :: rest)

/-- Strictly increasing exponents from the leaf upwards, except a possible leading tie. -/
def SkewIncreasing (ks : List Nat) : Prop :=
  StrictlyIncreasing ks ∨
    ∃ k rest, ks = k :: k :: rest ∧ StrictlyIncreasing (k :: rest)

/-- Exponent-list transition when appending one leaf below an ancestor chain with exponents `ks`. -/
def skewPush : List Nat → List Nat
  | k₁ :: k₂ :: rest =>
      if k₁ = k₂ then (k₁ + 1) :: rest else 1 :: k₁ :: k₂ :: rest
  | ks => 1 :: ks

theorem blockSize_pos {k : Nat} (hk : 1 ≤ k) : 0 < blockSize k := by
  cases k with
  | zero => omega
  | succ k' =>
      unfold blockSize
      have hPos := pow2_pos k'
      have hStep := pow2_succ k'
      omega

theorem blockSize_strictMono {a b : Nat} (hab : a < b) : blockSize a < blockSize b := by
  unfold blockSize
  have hPos := pow2_pos a
  have hLt := pow2_strictMono hab
  omega

theorem blockSize_merge (k : Nat) :
    blockSize k + blockSize k + 1 = blockSize (k + 1) := by
  unfold blockSize
  have hPos := pow2_pos k
  have hStep := pow2_succ k
  omega

theorem blockSum_skewPush (ks : List Nat) :
    blockSum (skewPush ks) = blockSum ks + 1 := by
  match ks with
  | [] => rfl
  | [k₁] =>
      simp only [skewPush, blockSum]
      have h1 : blockSize 1 = 1 := rfl
      omega
  | k₁ :: k₂ :: rest =>
      simp only [skewPush]
      if hEq : k₁ = k₂ then
        rw [ite_eq_left hEq, ← hEq]
        simp only [blockSum]
        have hM := blockSize_merge k₁
        omega
      else
        rw [ite_eq_right hEq]
        simp only [blockSum]
        have h1 : blockSize 1 = 1 := rfl
        omega

theorem skewPush_ne_nil (ks : List Nat) :
    ∃ k rest, skewPush ks = k :: rest := by
  match ks with
  | [] => exact ⟨1, [], rfl⟩
  | [k₁] => exact ⟨1, [k₁], rfl⟩
  | k₁ :: k₂ :: rest =>
      simp only [skewPush]
      if hEq : k₁ = k₂ then
        rw [ite_eq_left hEq]
        exact ⟨k₁ + 1, rest, rfl⟩
      else
        rw [ite_eq_right hEq]
        exact ⟨1, k₁ :: k₂ :: rest, rfl⟩

theorem allList_pos_skewPush {ks : List Nat}
    (hAll : AllList (fun k => 1 ≤ k) ks) :
    AllList (fun k => 1 ≤ k) (skewPush ks) := by
  match ks with
  | [] => exact ⟨by omega, trivial⟩
  | [k₁] => exact ⟨by omega, hAll⟩
  | k₁ :: k₂ :: rest =>
      simp only [skewPush]
      if hEq : k₁ = k₂ then
        rw [ite_eq_left hEq]
        have hk₁ : 1 ≤ k₁ := hAll.1
        have hRest : AllList (fun k => 1 ≤ k) rest := hAll.2.2
        exact ⟨by omega, hRest⟩
      else
        rw [ite_eq_right hEq]
        exact ⟨by omega, hAll⟩

theorem skewIncreasing_skewPush {ks : List Nat}
    (hAll : AllList (fun k => 1 ≤ k) ks)
    (hSkew : SkewIncreasing ks) :
    SkewIncreasing (skewPush ks) := by
  match ks with
  | [] => exact Or.inl trivial
  | [k₁] =>
      have hk₁ : 1 ≤ k₁ := hAll.1
      if hEq1 : 1 = k₁ then
        rw [← hEq1]
        exact Or.inr ⟨1, [], rfl, trivial⟩
      else
        have hLt1 : 1 < k₁ := by omega
        exact Or.inl ⟨hLt1, trivial⟩
  | k₁ :: k₂ :: rest =>
      simp only [skewPush]
      if hEq : k₁ = k₂ then
        rw [ite_eq_left hEq]
        have hStrictTail : StrictlyIncreasing (k₁ :: rest) := by
          cases hSkew with
          | inl hS =>
              have hLt : k₁ < k₂ := hS.1
              omega
          | inr hTie =>
              let ⟨k, rest', hListEq, hST⟩ := hTie
              have hkEq : k₁ = k := congrArg headNat hListEq
              have hTail1 : k₂ :: rest = k :: rest' := congrArg tailNat hListEq
              have hRestEq : rest = rest' := congrArg tailNat hTail1
              rw [hkEq, hRestEq]
              exact hST
        cases rest with
        | nil => exact Or.inl trivial
        | cons k₃ rest'' =>
            have hLt13 : k₁ < k₃ := hStrictTail.1
            have hStrict3 : StrictlyIncreasing (k₃ :: rest'') := hStrictTail.2
            if hEq3 : k₁ + 1 = k₃ then
              rw [hEq3]
              exact Or.inr ⟨k₃, rest'', rfl, hStrict3⟩
            else
              have hLt3 : k₁ + 1 < k₃ := by omega
              exact Or.inl ⟨hLt3, hStrict3⟩
      else
        rw [ite_eq_right hEq]
        have hStrictKs : StrictlyIncreasing (k₁ :: k₂ :: rest) := by
          cases hSkew with
          | inl hS => exact hS
          | inr hTie =>
              let ⟨k, rest', hListEq, _⟩ := hTie
              have hk₁ : k₁ = k := congrArg headNat hListEq
              have hTail1 : k₂ :: rest = k :: rest' := congrArg tailNat hListEq
              have hk₂ : k₂ = k := congrArg headNat hTail1
              omega
        have hk₁Pos : 1 ≤ k₁ := hAll.1
        if hEq1 : 1 = k₁ then
          rw [← hEq1] at hStrictKs ⊢
          exact Or.inr ⟨1, k₂ :: rest, rfl, hStrictKs⟩
        else
          have hLt1 : 1 < k₁ := by omega
          exact Or.inl ⟨hLt1, hStrictKs⟩

end PaperB
