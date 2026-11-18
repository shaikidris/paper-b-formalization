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

/-- Per-node structural and skew-binary invariant relative to ghost exponent map `exps`. -/
structure NodeSpec (F : JumpForest) (exps : Nat → List Nat) (u : Nat) : Prop where
  parent_lt_size : F.parentOf u < F.size
  jump_lt_size : F.jumpOf u < F.size
  root_spec : u = 0 → F.recordAt 0 = rootRecord ∧ exps 0 = []
  pos_parent_lt : 0 < u → F.parentOf u < u
  pos_jump_le_parent : 0 < u → F.jumpOf u ≤ F.parentOf u
  pos_jump_cases : 0 < u →
    F.jumpOf u = F.parentOf u ∨ F.jumpOf u = F.jumpOf (F.jumpOf (F.parentOf u))
  pos_depth : 0 < u → F.depthOf u = F.depthOf (F.parentOf u) + 1
  pos_exps_eq : 0 < u → exps u = skewPush (exps (F.parentOf u))
  depth_eq_blockSum : F.depthOf u = blockSum (exps u)
  exps_pos : AllList (fun k => 1 ≤ k) (exps u)
  exps_skew : SkewIncreasing (exps u)
  jump_exps : ∀ k rest, exps u = k :: rest → exps (F.jumpOf u) = rest
  jump_eq_parent_of_one : ∀ rest, exps u = 1 :: rest → F.jumpOf u = F.parentOf u

/-- Global skew-binary forest invariant across all `u < F.size`. -/
structure ForestInvariant (F : JumpForest) (exps : Nat → List Nat) : Prop where
  size_pos : 0 < F.size
  nodes : ∀ u : Nat, u < F.size → NodeSpec F exps u

namespace ForestInvariant

theorem root_record {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) :
    F.recordAt 0 = rootRecord :=
  ((inv.nodes 0 inv.size_pos).root_spec rfl).1

theorem root_parent {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) : F.parentOf 0 = 0 := by
  unfold JumpForest.parentOf
  rw [inv.root_record]
  rfl

theorem root_depth {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) : F.depthOf 0 = 0 := by
  unfold JumpForest.depthOf
  rw [inv.root_record]
  rfl

theorem root_jump {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) : F.jumpOf 0 = 0 := by
  unfold JumpForest.jumpOf
  rw [inv.root_record]
  rfl

theorem jump_le_self {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) {u : Nat} (hu : u < F.size) :
    F.jumpOf u ≤ u := by
  if hPos : 0 < u then
    have spec := inv.nodes u hu
    have h1 := spec.pos_jump_le_parent hPos
    have h2 := spec.pos_parent_lt hPos
    omega
  else
    have hu0 : u = 0 := by omega
    rw [hu0, inv.root_jump]
    exact Nat.le_refl 0

theorem jump_lt_self {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) {u : Nat} (hPos : 0 < u) (hu : u < F.size) :
    F.jumpOf u < u := by
  have spec := inv.nodes u hu
  have h1 := spec.pos_jump_le_parent hPos
  have h2 := spec.pos_parent_lt hPos
  omega

theorem depth_eq_zero_iff {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) {u : Nat} (hu : u < F.size) :
    F.depthOf u = 0 ↔ u = 0 := by
  constructor
  · intro hD
    if hPos : 0 < u then
      have hStep := (inv.nodes u hu).pos_depth hPos
      omega
    else
      omega
  · intro hEq
    rw [hEq]
    exact inv.root_depth

theorem depth_jump_lt {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) {u : Nat} (hPos : 0 < u) (hu : u < F.size) :
    F.depthOf (F.jumpOf u) < F.depthOf u := by
  have specU := inv.nodes u hu
  let ⟨k, rest, hPush⟩ := skewPush_ne_nil (exps (F.parentOf u))
  have hExpsU : exps u = k :: rest := Eq.trans (specU.pos_exps_eq hPos) hPush
  have hkPos : 1 ≤ k := by
    have hAll := specU.exps_pos
    rw [hExpsU] at hAll
    exact hAll.1
  have hBPos : 0 < blockSize k := blockSize_pos hkPos
  have hExpsJ : exps (F.jumpOf u) = rest := specU.jump_exps k rest hExpsU
  have specJ := inv.nodes (F.jumpOf u) specU.jump_lt_size
  have hDU : F.depthOf u = blockSize k + blockSum rest := by
    rw [specU.depth_eq_blockSum, hExpsU]
    rfl
  have hDJ : F.depthOf (F.jumpOf u) = blockSum rest := by
    rw [specJ.depth_eq_blockSum, hExpsJ]
  omega

theorem depthOf_le_self {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) {u : Nat} (hu : u < F.size) :
    F.depthOf u ≤ u := by
  refine nat_strong_ind (P := fun w => w < F.size → F.depthOf w ≤ w) ?_ u hu
  intro w ih hw
  if hPos : 0 < w then
    have specW := inv.nodes w hw
    have hpLt : F.parentOf w < w := specW.pos_parent_lt hPos
    have hpSz : F.parentOf w < F.size := specW.parent_lt_size
    have hIH : F.depthOf (F.parentOf w) ≤ F.parentOf w := ih (F.parentOf w) hpLt hpSz
    have hStep := specW.pos_depth hPos
    omega
  else
    have hw0 : w = 0 := by omega
    rw [hw0, inv.root_depth]
    exact Nat.le_refl 0

end ForestInvariant

theorem ValidJumpForest.exists_forestInvariant {F : JumpForest}
    (hF : ValidJumpForest F) :
    ∃ exps : Nat → List Nat, ForestInvariant F exps := by
  induction hF with
  | init =>
      refine ⟨fun _ => [], ⟨by decide, ?_⟩⟩
      intro u hu
      have hSz : JumpForest.init.size = 1 := rfl
      have hu0 : u = 0 := by omega
      subst hu0
      refine
        { parent_lt_size := by decide
          jump_lt_size := by decide
          root_spec := fun _ => ⟨rfl, rfl⟩
          pos_parent_lt := fun hPos => by omega
          pos_jump_le_parent := fun hPos => by omega
          pos_jump_cases := fun hPos => by omega
          pos_depth := fun hPos => by omega
          pos_exps_eq := fun hPos => by omega
          depth_eq_blockSum := rfl
          exps_pos := trivial
          exps_skew := Or.inl trivial
          jump_exps := fun _ _ hEq => by cases hEq
          jump_eq_parent_of_one := fun _ hEq => by cases hEq }
  | @appendLeaf F p _ hp ih =>
      let ⟨exps, inv⟩ := ih
      let exps' : Nat → List Nat :=
        fun u => if u = F.size then skewPush (exps p) else exps u
      have hF'Size : (F.appendLeaf p).size = F.size + 1 := F.size_appendLeaf p
      have hExpsOld : ∀ w : Nat, w < F.size → exps' w = exps w := by
        intro w hw
        have hNe : w ≠ F.size := by omega
        exact ite_eq_right hNe
      have hExpsNew : exps' F.size = skewPush (exps p) :=
        ite_eq_left rfl
      refine ⟨exps', ⟨by omega, ?_⟩⟩
      intro u hu'
      if huOld : u < F.size then
        have specU := inv.nodes u huOld
        have hpOld : F.parentOf u < F.size := specU.parent_lt_size
        have hjOld : F.jumpOf u < F.size := specU.jump_lt_size
        have haOld : F.jumpOf (F.parentOf u) < F.size := (inv.nodes _ hpOld).jump_lt_size
        have hParEq : (F.appendLeaf p).parentOf u = F.parentOf u :=
          parentOf_appendLeaf_old F p huOld
        have hDepEq : (F.appendLeaf p).depthOf u = F.depthOf u :=
          depthOf_appendLeaf_old F p huOld
        have hJmpEq : (F.appendLeaf p).jumpOf u = F.jumpOf u :=
          jumpOf_appendLeaf_old F p huOld
        have hDepParEq :
            (F.appendLeaf p).depthOf ((F.appendLeaf p).parentOf u) =
              F.depthOf (F.parentOf u) := by
          rw [hParEq]
          exact depthOf_appendLeaf_old F p hpOld
        have hJmpParEq :
            (F.appendLeaf p).jumpOf ((F.appendLeaf p).parentOf u) =
              F.jumpOf (F.parentOf u) := by
          rw [hParEq]
          exact jumpOf_appendLeaf_old F p hpOld
        have hJmp2Eq :
            (F.appendLeaf p).jumpOf (F.jumpOf (F.parentOf u)) =
              F.jumpOf (F.jumpOf (F.parentOf u)) :=
          jumpOf_appendLeaf_old F p haOld
        refine
          { parent_lt_size := by rw [hParEq]; omega
            jump_lt_size := by rw [hJmpEq]; omega
            root_spec := fun hu0 => by
              subst hu0
              rw [recordAt_appendLeaf_old F p inv.size_pos, hExpsOld 0 inv.size_pos]
              exact specU.root_spec rfl
            pos_parent_lt := fun hPos => by rw [hParEq]; exact specU.pos_parent_lt hPos
            pos_jump_le_parent := fun hPos => by
              rw [hJmpEq, hParEq]
              exact specU.pos_jump_le_parent hPos
            pos_jump_cases := fun hPos => by
              rw [hJmpEq, hParEq, jumpOf_appendLeaf_old F p hpOld, hJmp2Eq]
              exact specU.pos_jump_cases hPos
            pos_depth := fun hPos => by
              rw [hDepEq, hDepParEq]
              exact specU.pos_depth hPos
            pos_exps_eq := fun hPos => by
              rw [hExpsOld u huOld, hParEq, hExpsOld (F.parentOf u) hpOld]
              exact specU.pos_exps_eq hPos
            depth_eq_blockSum := by
              rw [hDepEq, hExpsOld u huOld]
              exact specU.depth_eq_blockSum
            exps_pos := by rw [hExpsOld u huOld]; exact specU.exps_pos
            exps_skew := by rw [hExpsOld u huOld]; exact specU.exps_skew
            jump_exps := fun k rest hEq => by
              rw [hJmpEq, hExpsOld (F.jumpOf u) hjOld]
              rw [hExpsOld u huOld] at hEq
              exact specU.jump_exps k rest hEq
            jump_eq_parent_of_one := fun rest hEq => by
              rw [hJmpEq, hParEq]
              rw [hExpsOld u huOld] at hEq
              exact specU.jump_eq_parent_of_one rest hEq }
      else
        have huEq : u = F.size := by omega
        subst huEq
        have specP := inv.nodes p hp
        let a := F.jumpOf p
        have ha : a < F.size := specP.jump_lt_size
        have haLeP : a ≤ p := inv.jump_le_self hp
        have specA := inv.nodes a ha
        let b := F.jumpOf a
        have hb : b < F.size := specA.jump_lt_size
        have hbLeA : b ≤ a := inv.jump_le_self ha
        have specB := inv.nodes b hb
        have hRecNew : (F.appendLeaf p).recordAt F.size = F.mkAppendedRecord p :=
          recordAt_appendLeaf_new F p
        have hParNew : (F.appendLeaf p).parentOf F.size = p := by
          unfold JumpForest.parentOf
          rw [hRecNew]
          rfl
        have hDepNew : (F.appendLeaf p).depthOf F.size = F.depthOf p + 1 := by
          unfold JumpForest.depthOf
          rw [hRecNew]
          rfl
        let len1 := F.depthOf p - F.depthOf a
        let len2 := F.depthOf a - F.depthOf b
        have hJmpNew : (F.appendLeaf p).jumpOf F.size =
            if 0 < len1 ∧ len1 = len2 then b else p := by
          unfold JumpForest.jumpOf
          rw [hRecNew]
          rfl
        have hJmpA_F' : (F.appendLeaf p).jumpOf p = a := jumpOf_appendLeaf_old F p hp
        have hJmpB_F' : (F.appendLeaf p).jumpOf a = b := jumpOf_appendLeaf_old F p ha
        have hStepInvs :
            (∀ k rest, exps' F.size = k :: rest →
                exps' ((F.appendLeaf p).jumpOf F.size) = rest) ∧
              (∀ rest, exps' F.size = 1 :: rest →
                (F.appendLeaf p).jumpOf F.size = (F.appendLeaf p).parentOf F.size) := by
          rw [hExpsNew, hParNew]
          cases hExpsP : exps p with
          | nil =>
              have hDP0 : F.depthOf p = 0 := by
                rw [specP.depth_eq_blockSum, hExpsP]
                rfl
              have hNotCond : ¬ (0 < len1 ∧ len1 = len2) := by
                change ¬ (0 < F.depthOf p - F.depthOf a ∧ _)
                omega
              have hJ : (F.appendLeaf p).jumpOf F.size = p := by
                rw [hJmpNew, ite_eq_right hNotCond]
              rw [hJ, hExpsOld p hp, hExpsP]
              dsimp only [skewPush]
              refine ⟨?_, fun _ _ => rfl⟩
              intro _ _ hEq
              exact (List.cons.inj hEq).2
          | cons k₁ tail1 =>
              cases tail1 with
              | nil =>
                  have hExpsA : exps a = [] := specP.jump_exps k₁ [] hExpsP
                  have hDA0 : F.depthOf a = 0 := by
                    rw [specA.depth_eq_blockSum, hExpsA]
                    rfl
                  have ha0 : a = 0 := (inv.depth_eq_zero_iff ha).mp hDA0
                  have hb0 : b = 0 := by
                    change F.jumpOf a = 0
                    rw [ha0]
                    exact inv.root_jump
                  have hDB0 : F.depthOf b = 0 := by
                    rw [hb0]
                    exact inv.root_depth
                  have hk₁Pos : 1 ≤ k₁ := by
                    have hAll := specP.exps_pos
                    rw [hExpsP] at hAll
                    exact hAll.1
                  have hDPPos : 0 < F.depthOf p := by
                    rw [specP.depth_eq_blockSum, hExpsP]
                    have hBP := blockSize_pos hk₁Pos
                    dsimp only [blockSum]
                    omega
                  have hNotCond : ¬ (0 < len1 ∧ len1 = len2) := by
                    change ¬ (0 < F.depthOf p - F.depthOf a ∧
                      F.depthOf p - F.depthOf a = F.depthOf a - F.depthOf b)
                    omega
                  have hJ : (F.appendLeaf p).jumpOf F.size = p := by
                    rw [hJmpNew, ite_eq_right hNotCond]
                  rw [hJ, hExpsOld p hp, hExpsP]
                  dsimp only [skewPush]
                  refine ⟨?_, fun _ _ => rfl⟩
                  intro _ _ hEq
                  exact (List.cons.inj hEq).2
              | cons k₂ tl =>
                  have hAllP := specP.exps_pos
                  rw [hExpsP] at hAllP
                  have hk₁Pos : 1 ≤ k₁ := hAllP.1
                  have hk₂Pos : 1 ≤ k₂ := hAllP.2.1
                  have hExpsA : exps a = k₂ :: tl := specP.jump_exps k₁ (k₂ :: tl) hExpsP
                  have hExpsB : exps b = tl := specA.jump_exps k₂ tl hExpsA
                  have hDP : F.depthOf p = blockSize k₁ + (blockSize k₂ + blockSum tl) := by
                    rw [specP.depth_eq_blockSum, hExpsP]
                    rfl
                  have hDA : F.depthOf a = blockSize k₂ + blockSum tl := by
                    rw [specA.depth_eq_blockSum, hExpsA]
                    rfl
                  have hDB : F.depthOf b = blockSum tl := by
                    rw [specB.depth_eq_blockSum, hExpsB]
                  have hLen1 : len1 = blockSize k₁ := by
                    change F.depthOf p - F.depthOf a = blockSize k₁
                    omega
                  have hLen2 : len2 = blockSize k₂ := by
                    change F.depthOf a - F.depthOf b = blockSize k₂
                    omega
                  if hEqK : k₁ = k₂ then
                    have hCond : 0 < len1 ∧ len1 = len2 := by
                      rw [hLen1, hLen2, hEqK]
                      exact ⟨blockSize_pos hk₂Pos, rfl⟩
                    have hJ : (F.appendLeaf p).jumpOf F.size = b := by
                      rw [hJmpNew, ite_eq_left hCond]
                    have hPushEq : skewPush (k₁ :: k₂ :: tl) = (k₁ + 1) :: tl := by
                      dsimp only [skewPush]
                      exact ite_eq_left hEqK
                    rw [hJ, hExpsOld b hb, hExpsB, hPushEq]
                    refine ⟨?_, ?_⟩
                    · intro _ _ hEq
                      exact (List.cons.inj hEq).2
                    · intro _ hEq
                      have hk1Eq : k₁ + 1 = 1 := (List.cons.inj hEq).1
                      omega
                  else
                    have hSkewP := specP.exps_skew
                    rw [hExpsP] at hSkewP
                    have hLtK : k₁ < k₂ := by
                      cases hSkewP with
                      | inl hS => exact hS.1
                      | inr hTie =>
                          let ⟨k, _, hListEq, _⟩ := hTie
                          have hk₁Eq : k₁ = k := (List.cons.inj hListEq).1
                          have hTail1 := (List.cons.inj hListEq).2
                          have hk₂Eq : k₂ = k := (List.cons.inj hTail1).1
                          omega
                    have hBLt : blockSize k₁ < blockSize k₂ := blockSize_strictMono hLtK
                    have hNotCond : ¬ (0 < len1 ∧ len1 = len2) := by
                      rw [hLen1, hLen2]
                      omega
                    have hJ : (F.appendLeaf p).jumpOf F.size = p := by
                      rw [hJmpNew, ite_eq_right hNotCond]
                    have hPushEq : skewPush (k₁ :: k₂ :: tl) = 1 :: k₁ :: k₂ :: tl := by
                      dsimp only [skewPush]
                      exact ite_eq_right hEqK
                    rw [hJ, hExpsOld p hp, hExpsP, hPushEq]
                    refine ⟨?_, fun _ _ => rfl⟩
                    intro _ _ hEq
                    exact (List.cons.inj hEq).2
        refine
          { parent_lt_size := by rw [hParNew]; omega
            jump_lt_size := by
              rw [hJmpNew]
              if hC : 0 < len1 ∧ len1 = len2 then
                rw [ite_eq_left hC]; omega
              else
                rw [ite_eq_right hC]; omega
            root_spec := fun _ => by
              have hPosSz := inv.size_pos
              omega
            pos_parent_lt := fun _ => by rw [hParNew]; exact hp
            pos_jump_le_parent := fun _ => by
              rw [hJmpNew, hParNew]
              if hC : 0 < len1 ∧ len1 = len2 then
                rw [ite_eq_left hC]; omega
              else
                rw [ite_eq_right hC]; omega
            pos_jump_cases := fun _ => by
              rw [hJmpNew, hParNew, hJmpA_F', hJmpB_F']
              if hC : 0 < len1 ∧ len1 = len2 then
                rw [ite_eq_left hC]; exact Or.inr rfl
              else
                rw [ite_eq_right hC]; exact Or.inl rfl
            pos_depth := fun _ => by
              rw [hDepNew, hParNew, depthOf_appendLeaf_old F p hp]
            pos_exps_eq := fun _ => by
              rw [hExpsNew, hParNew, hExpsOld p hp]
            depth_eq_blockSum := by
              rw [hDepNew, hExpsNew, blockSum_skewPush, specP.depth_eq_blockSum]
            exps_pos := by
              rw [hExpsNew]
              exact allList_pos_skewPush specP.exps_pos
            exps_skew := by
              rw [hExpsNew]
              exact skewIncreasing_skewPush specP.exps_pos specP.exps_skew
            jump_exps := hStepInvs.1
            jump_eq_parent_of_one := hStepInvs.2 }

end PaperB
