import PaperB.FullDomScan
import PaperB.PackedStaticLayout

set_option autoImplicit false

namespace PaperB.EX15.WholeScan.PackedInput

open JumpForestCommonAncestor
open StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath
open PackedStaticLayout

universe u

/- The executable adapter reads the occupied records in the run's word image.
   The forest witness is used only in proofs, so the existential in the scan
   specification does not have to be eliminated into data. The forward map is
   used only to translate the endpoints of the dominance theorem. -/

private structure Columns {n : Nat} (row : Fin n → Fin n × Nat)
    (k : Nat) where
  parents : Array (Fin n)
  depths : Array Nat
  parents_size : parents.size = k
  depths_size : depths.size = k
  parent_at : ∀ (i : Fin n) (hi : i.val < k),
    parents[i.val]'(by omega) = (row i).1
  depth_at : ∀ (i : Fin n) (hi : i.val < k),
    depths[i.val]'(by omega) = (row i).2

private theorem push_at {β : Type} {n k : Nat} (a : Array β)
    (f : Fin n → β) (hs : a.size = k)
    (ha : ∀ (i : Fin n) (hi : i.val < k), a[i.val]'(by omega) = f i)
    (hk : k < n) (i : Fin n) (hi : i.val < k + 1) :
    (a.push (f ⟨k, hk⟩))[i.val]'(by rw [Array.size_push, hs]; exact hi) =
      f i := by
  by_cases h : i.val < k
  · have hb : i.val < a.size := by omega
    simpa only [Array.getElem_push, dite_eq_left hb] using ha i h
  · have e : i = (⟨k, hk⟩ : Fin n) := by
      apply Fin.ext
      change i.val = k
      omega
    subst i
    have hb : ¬ k < a.size := by omega
    simp only [Array.getElem_push, dite_eq_right hb]

private def pushRow {n k : Nat} {row : Fin n → Fin n × Nat}
    (a : Columns row k) (hk : k < n) : Columns row (k + 1) :=
  let v := row ⟨k, hk⟩
  { parents := a.parents.push v.1
    depths := a.depths.push v.2
    parents_size := by rw [Array.size_push, a.parents_size]
    depths_size := by rw [Array.size_push, a.depths_size]
    parent_at := push_at a.parents (fun i => (row i).1)
      a.parents_size a.parent_at hk
    depth_at := push_at a.depths (fun i => (row i).2)
      a.depths_size a.depth_at hk }

private def collect {n : Nat} (row : Fin n → Fin n × Nat)
    (k : Nat) (hk : k ≤ n) (a : Columns row k) : Columns row n :=
  if h : k < n then
    collect row (k + 1) (by omega) (pushRow a h)
  else
    (show k = n by omega) ▸ a
termination_by n - k
decreasing_by omega

private def columns {n : Nat} (row : Fin n → Fin n × Nat) : Columns row n :=
  collect row 0 (Nat.zero_le n)
    { parents := #[]
      depths := #[]
      parents_size := rfl
      depths_size := rfl
      parent_at := by intro i hi; omega
      depth_at := by intro i hi; omega }

private def makeInput {n : Nat} (hn : 0 < n)
    (row : Fin n → Fin n × Nat) : Input n :=
  let a := columns row
  { root := ⟨0, hn⟩
    parent := ⟨a.parents, a.parents_size⟩
    depth := ⟨a.depths, a.depths_size⟩ }

private theorem makeInput_parent {n : Nat} (hn : 0 < n)
    (row : Fin n → Fin n × Nat) (i : Fin n) :
    (makeInput hn row).parent.read i = (row i).1 := by
  unfold makeInput Slots.read
  exact (columns row).parent_at i i.isLt

private theorem makeInput_depth {n : Nat} (hn : 0 < n)
    (row : Fin n → Fin n × Nat) (i : Fin n) :
    (makeInput hn row).depth.read i = (row i).2 := by
  unfold makeInput Slots.read
  exact (columns row).depth_at i i.isLt

private theorem forest_pos {F : JumpForest} (h : ValidJumpForest F) :
    0 < F.size := by
  obtain ⟨_, inv⟩ := h.exists_forestInvariant
  exact inv.size_pos

private theorem forest_parent_bound {F : JumpForest} (h : ValidJumpForest F)
    {i : Nat} (hi : i < F.size) : F.parentOf i < F.size := by
  exact h.iterParent_lt_size hi 1

private theorem forest_root_parent {F : JumpForest} (hF : ValidJumpForest F) :
    F.parentOf 0 = 0 := by
  obtain ⟨_, inv⟩ := hF.exists_forestInvariant
  exact inv.root_parent

private theorem forest_root_depth {F : JumpForest} (hF : ValidJumpForest F) :
    F.depthOf 0 = 0 := by
  obtain ⟨_, inv⟩ := hF.exists_forestInvariant
  exact inv.root_depth

private theorem forest_depth_step {F : JumpForest} (hF : ValidJumpForest F)
    {i : Nat} (hi : i < F.size) (h0 : i ≠ 0) :
    F.depthOf i = F.depthOf (F.parentOf i) + 1 := by
  obtain ⟨_, inv⟩ := hF.exists_forestInvariant
  exact (inv.nodes i hi).pos_depth (Nat.pos_of_ne_zero h0)

/-- Transfer validity from the jump records to their two projected columns. -/
theorem inputOK_of_valid {n : Nat} {F : JumpForest} (hF : ValidJumpForest F)
    (hn : n = F.size) (x : Input n) (hr : x.root.val = 0)
    (hp : ∀ i, (x.parent.read i).val = F.parentOf i.val)
    (hd : ∀ i, x.depth.read i = F.depthOf i.val) : InputOK x := by
  have rootParent : x.parent.read x.root = x.root := by
    apply Fin.ext
    rw [hp x.root, hr]
    exact forest_root_parent hF
  have rootDepth : x.depth.read x.root = 0 := by
    rw [hd x.root, hr]
    exact forest_root_depth hF
  have step : ∀ i : Fin n, i ≠ x.root →
      x.depth.read i = x.depth.read (x.parent.read i) + 1 := by
    intro i hi
    have hb : i.val < F.size := by rw [← hn]; exact i.isLt
    have h0 : i.val ≠ 0 := fun e => hi (Fin.ext (e.trans hr.symm))
    rw [hd i, hd (x.parent.read i), hp i]
    exact forest_depth_step hF hb h0
  constructor
  all_goals
    try (apply And.intro <;> try (apply And.intro <;> try apply And.intro))
  all_goals
    first
    | exact rootParent
    | exact rootParent.symm
    | exact rootDepth
    | exact rootDepth.symm
    | exact step
    | intro i hi
      have e := step i hi
      first | exact e.symm | omega
    | intro i hi
      have hne : i ≠ x.root := by
        intro e
        subst i
        rw [rootDepth] at hi
        omega
      have e := step i hne
      first | exact e | exact e.symm | omega

def occupied (R : JumpWordRegion) (mem : Array Nat) : Nat :=
  readWord mem R.baseAddr

private theorem occupied_pos {R : JumpWordRegion} {mem : Array Nat}
    (h : ∃ F, JumpWordLayout R F mem) : 0 < occupied R mem := by
  obtain ⟨F, L⟩ := h
  change 0 < readWord mem R.baseAddr
  rw [L.size_word]
  exact forest_pos L.valid

private theorem word_parent_bound {R : JumpWordRegion} {mem : Array Nat}
    (h : ∃ F, JumpWordLayout R F mem) {i : Nat}
    (hi : i < occupied R mem) :
    readWord mem (R.parentAddr i) < occupied R mem := by
  obtain ⟨F, L⟩ := h
  have hb : i < F.size := by
    rw [← L.size_word]
    exact hi
  change readWord mem (R.parentAddr i) < readWord mem R.baseAddr
  rw [L.slot_parent i hb, L.size_word]
  exact forest_parent_bound L.valid hb

/-- One pass over the occupied prefix. No jump field, spare slot, or entry
    of the vertex-to-slot map is read by this adapter. -/
def ofWords (R : JumpWordRegion) (mem : Array Nat)
    (h : ∃ F, JumpWordLayout R F mem) : Input (occupied R mem) :=
  makeInput (occupied_pos h) fun i =>
    (⟨readWord mem (R.parentAddr i.val), word_parent_bound h i.isLt⟩,
      readWord mem (R.depthAddr i.val))

@[simp] theorem ofWords_root {R : JumpWordRegion} {mem : Array Nat}
    (h : ∃ F, JumpWordLayout R F mem) :
    (ofWords R mem h).root.val = 0 := rfl

theorem ofWords_parent {R : JumpWordRegion} {mem : Array Nat}
    {F : JumpForest} (L : JumpWordLayout R F mem)
    (h : ∃ J, JumpWordLayout R J mem) (i : Fin (occupied R mem)) :
    ((ofWords R mem h).parent.read i).val = F.parentOf i.val := by
  have hi : i.val < F.size := by rw [← L.size_word]; exact i.isLt
  unfold ofWords
  rw [makeInput_parent]
  exact L.slot_parent i.val hi

theorem ofWords_depth {R : JumpWordRegion} {mem : Array Nat}
    {F : JumpForest} (L : JumpWordLayout R F mem)
    (h : ∃ J, JumpWordLayout R J mem) (i : Fin (occupied R mem)) :
    (ofWords R mem h).depth.read i = F.depthOf i.val := by
  have hi : i.val < F.size := by rw [← L.size_word]; exact i.isLt
  unfold ofWords
  rw [makeInput_depth]
  exact L.slot_depth i.val hi

theorem ofWords_ok {R : JumpWordRegion} {mem : Array Nat}
    (h : ∃ F, JumpWordLayout R F mem) : InputOK (ofWords R mem h) := by
  have hex : ∃ F, JumpWordLayout R F mem := h
  obtain ⟨F, L⟩ := hex
  exact inputOK_of_valid L.valid L.size_word (ofWords R mem h) rfl
    (ofWords_parent L h) (ofWords_depth L h)

/-- Semantic parent iteration on the actual packed input, not on a tree
    reconstructed from the original-vertex map. -/
def parentIter {n : Nat} (x : Input n) : Nat → Fin n → Fin n
  | 0, v => v
  | k + 1, v => parentIter x k (x.parent.read v)

def SemanticAncestor {n : Nat} (x : Input n) (a v : Fin n) : Prop :=
  ∃ k, parentIter x k v = a

theorem parentIter_val {n : Nat} {F : JumpForest} {x : Input n}
    (hp : ∀ i, (x.parent.read i).val = F.parentOf i.val)
    (k : Nat) (v : Fin n) :
    (parentIter x k v).val = F.iterParent k v.val := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    change (parentIter x k (x.parent.read v)).val =
      F.iterParent k (F.parentOf v.val)
    rw [ih (x.parent.read v), hp v]

theorem semanticAncestor_iff_jump {n : Nat} {F : JumpForest} {x : Input n}
    (hp : ∀ i, (x.parent.read i).val = F.parentOf i.val)
    (a v : Fin n) :
    SemanticAncestor x a v ↔ IsAncestor F a.val v.val := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (parentIter_val hp k v).symm.trans (congrArg Fin.val hk)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Fin.ext ((parentIter_val hp k v).trans hk)⟩

section Scan

variable {α : Type u} {g : Digraph} {R : JumpWordRegion}
variable {r : Vertex g} {S : Vertex g → Prop} {s : ScanState}

abbrev Certified (α : Type u) {g : Digraph} (R : JumpWordRegion)
    (r : Vertex g) (S : Vertex g → Prop) (s : ScanState) : Prop :=
  ∃ F : JumpForest, Partial (packedJumpOps α R) r S F s

theorem certifiedOfSpec {P : JumpForest → Prop}
    (h : ∃ F, Partial (packedJumpOps α R) r S F s ∧ P F) :
    Certified α R r S s := by
  obtain ⟨F, I, _⟩ := h
  exact ⟨F, I⟩

private abbrev stateWords (s : ScanState) : Array Nat := s.words

private theorem partial_layout {F : JumpForest}
    (I : Partial (packedJumpOps α R) r S F s) :
    JumpWordLayout R F (stateWords s) :=
  I.layout

private theorem partial_bound {F : JumpForest}
    (I : Partial (packedJumpOps α R) r S F s)
    {v : Vertex g} (hv : S v) : readSlot s.slots v < F.size :=
  I.bounded hv

private theorem partial_dominates {F : JumpForest}
    (I : Partial (packedJumpOps α R) r S F s)
    {a v : Vertex g} (ha : S a) (hv : S v) :
    g.Dominates r a v ↔
      IsAncestor F (readSlot s.slots a) (readSlot s.slots v) := by
  have hs : g.Dominates r a v ↔
      S a ∧ IsAncestor F (readSlot s.slots a) (readSlot s.slots v) :=
    I.semantic hv a
  exact ⟨fun hd => (hs.mp hd).2, fun hA => hs.mpr ⟨ha, hA⟩⟩

private theorem scan_layout (C : Certified α R r S s) :
    ∃ F, JumpWordLayout R F (stateWords s) := by
  obtain ⟨F, I⟩ := C
  exact ⟨F, partial_layout I⟩

def scanInput (C : Certified α R r S s) : Input (occupied R (stateWords s)) :=
  ofWords R (stateWords s) (scan_layout C)

theorem scanInput_ok (C : Certified α R r S s) : InputOK (scanInput C) :=
  ofWords_ok (scan_layout C)

def scanSlot (C : Certified α R r S s) (v : Vertex g) (hv : S v) :
    Fin (occupied R (stateWords s)) :=
  ⟨readSlot s.slots v, by
    obtain ⟨F, I⟩ := C
    change readSlot s.slots v < readWord (stateWords s) R.baseAddr
    rw [(partial_layout I).size_word]
    exact partial_bound I hv⟩

theorem dominates_iff_semanticAncestor (C : Certified α R r S s)
    {a v : Vertex g} (ha : S a) (hv : S v) :
    g.Dominates r a v ↔
      SemanticAncestor (scanInput C) (scanSlot C a ha) (scanSlot C v hv) := by
  have hex : ∃ F : JumpForest, Partial (packedJumpOps α R) r S F s := C
  obtain ⟨F, I⟩ := hex
  have L := partial_layout I
  exact (partial_dominates I ha hv).trans
    (semanticAncestor_iff_jump (ofWords_parent L (scan_layout C))
      (scanSlot C a ha) (scanSlot C v hv)).symm

end Scan

/- At the original-graph call site (the module defining EX15.runGraph):

     let out := runGraph g r hacyc
     have C : Certified (OriginalOccurrence g) (graphRegion g.vertexCount)
         r (g.InitiallyReachable r) out.state :=
       certifiedOfSpec (runGraph_spec g r hacyc hL rootReach rootDom)
     let x := scanInput C
     have hx : InputOK x := scanInput_ok C

   For reachable a and v, use `dominates_iff_semanticAncestor C ha hv`.
   `out` is shared: only its word image is used to build `x`, and the
   specification contributes an erased proof, not a second scan.
-/

end PaperB.EX15.WholeScan.PackedInput
