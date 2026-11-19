import PaperB.ReachScan

namespace PaperB.CompactIds

structure Tables (n : Nat) where
  forward : Array (Option Nat)
  inverse : Array (Fin n)
  visits : Nat

def ids (n : Nat) : List (Fin n) :=
  List.ofFn (fun i => i)

def marked (marks : Array Bool) (i : Fin marks.size) : Bool :=
  marks[i.val]'i.isLt

def initial (n : Nat) : Tables n :=
  ⟨Array.replicate n none, #[], 0⟩

def step (marks : Array Bool) (t : Tables marks.size)
    (i : Fin marks.size) : Tables marks.size :=
  if marked marks i then
    ⟨t.forward.setIfInBounds i.val (some t.inverse.size),
      t.inverse.push i, t.visits + 1⟩
  else
    ⟨t.forward, t.inverse, t.visits + 1⟩

def scan (marks : Array Bool) :
    List (Fin marks.size) → Tables marks.size → Tables marks.size
  | [], t => t
  | i :: rest, t => scan marks rest (step marks t i)

def compact (marks : Array Bool) : Tables marks.size :=
  scan marks (ids marks.size) (initial marks.size)

def lookup {n : Nat} (t : Tables n) (i : Fin n) : Option Nat :=
  (t.forward[i.val]?).getD none

private theorem step_size (marks : Array Bool) (t : Tables marks.size)
    (i : Fin marks.size) : (step marks t i).forward.size = t.forward.size := by
  cases h : marked marks i <;> simp [step, h]

theorem scan_spec (marks : Array Bool) (rest : List (Fin marks.size))
    (t : Tables marks.size) :
    (scan marks rest t).visits = t.visits + rest.length ∧
    (scan marks rest t).forward.size = t.forward.size ∧
    (scan marks rest t).inverse.toList =
      t.inverse.toList ++ rest.filter (marked marks) := by
  induction rest generalizing t with
  | nil => simp [scan]
  | cons i rest ih =>
    obtain ⟨hv, hf, hi⟩ := ih (step marks t i)
    refine ⟨?_, ?_, ?_⟩
    · rw [scan, hv, List.length_cons]
      cases h : marked marks i <;>
        simp [step, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · rw [scan, hf, step_size]
    · rw [scan, hi]
      cases h : marked marks i <;>
        simp [step, h, List.filter_cons, Array.toList_push, List.append_assoc]

theorem compact_spec (marks : Array Bool) :
    (compact marks).visits = marks.size ∧
    (compact marks).forward.size = marks.size ∧
    (compact marks).inverse.toList = (ids marks.size).filter (marked marks) := by
  simpa [compact, initial, ids] using
    (scan_spec marks (ids marks.size) (initial marks.size))

-- The scan starts with an empty inverse. Each append adds one slot,
-- and the same branch issues exactly one forward set.
theorem compact_push_count (marks : Array Bool) :
    (compact marks).inverse.size = ((ids marks.size).filter (marked marks)).length := by
  simpa using congrArg List.length (compact_spec marks).2.2

def Reciprocal {n : Nat} (t : Tables n) : Prop :=
  ∀ (k : Nat) (hk : k < t.inverse.size), lookup t (t.inverse[k]'hk) = some k

private theorem read_set_eq {α : Type} (a : Array α) (i : Nat) (x : α)
    (hi : i < a.size) : (a.setIfInBounds i x)[i]? = some x := by
  exact Array.getElem?_setIfInBounds_self_of_lt (xs := a) (i := i) (a := x) hi

private theorem read_set_ne {α : Type} (a : Array α) (i j : Nat) (x : α)
    (hne : i ≠ j) (hj : j < a.size) :
    (a.setIfInBounds i x)[j]? = a[j]? := by
  apply Array.getElem?_setIfInBounds_ne (xs := a) (a := x)
  first | exact hne | exact Ne.symm hne

private theorem reciprocal_push {n : Nat} (t : Tables n) (i : Fin n)
    (hs : t.forward.size = n) (hr : Reciprocal t)
    (hf : i ∉ t.inverse.toList) :
    Reciprocal (⟨t.forward.setIfInBounds i.val (some t.inverse.size),
      t.inverse.push i, t.visits + 1⟩ : Tables n) := by
  intro k hk
  change k < (t.inverse.push i).size at hk
  change ((t.forward.setIfInBounds i.val (some t.inverse.size))[((t.inverse.push i)[k]'hk).val]?).getD
    none = some k
  by_cases h : k < t.inverse.size
  · have hne : i.val ≠ (t.inverse[k]'h).val := by
      intro e
      apply hf
      rw [Fin.ext e]
      have hl : k < t.inverse.toList.length := by simpa using h
      have hm : t.inverse.toList[k]'hl ∈ t.inverse.toList := List.getElem_mem hl
      simpa using hm
    have he : (t.inverse.push i)[k]'hk = t.inverse[k]'h := by
      simp [Array.getElem_push, h, Nat.ne_of_lt h, Ne.symm (Nat.ne_of_lt h)]
    have hb : (t.inverse[k]'h).val < t.forward.size := by
      simpa only [hs] using (t.inverse[k]'h).isLt
    rw [he, read_set_ne _ _ _ _ hne hb]
    exact hr k h
  · have hb : k < t.inverse.size + 1 := by simpa using hk
    have e : k = t.inverse.size :=
      Nat.le_antisymm (Nat.le_of_lt_succ hb) (Nat.le_of_not_gt h)
    subst k
    have he : (t.inverse.push i)[t.inverse.size]'hk = i := by
      simp [Array.getElem_push]
    have hi : i.val < t.forward.size := by simpa only [hs] using i.isLt
    rw [he, read_set_eq _ _ _ hi]
    rfl

theorem scan_reciprocal (marks : Array Bool) (rest : List (Fin marks.size)) :
    ∀ (t : Tables marks.size), t.forward.size = marks.size → Reciprocal t →
      rest.Nodup → (∀ j ∈ rest, j ∉ t.inverse.toList) →
      Reciprocal (scan marks rest t) := by
  induction rest with
  | nil =>
    intro t _ hr _ _
    exact hr
  | cons i rest ih =>
    intro t hs hr hd hf
    obtain ⟨hiRest, hdRest⟩ := List.nodup_cons.mp hd
    have hi : i ∉ t.inverse.toList := hf i (by simp)
    have hr' : Reciprocal (step marks t i) := by
      cases h : marked marks i with
      | false => simpa [step, h, Reciprocal, lookup] using hr
      | true => simpa [step, h] using reciprocal_push t i hs hr hi
    have hf' : ∀ j ∈ rest, j ∉ (step marks t i).inverse.toList := by
      intro j hj
      have hjOld : j ∉ t.inverse.toList := hf j (by simp [hj])
      have hne : j ≠ i := fun e => hiRest (e ▸ hj)
      cases h : marked marks i <;>
        simp [step, h, Array.toList_push, hjOld, hne, Ne.symm hne]
    exact ih (step marks t i) ((step_size marks t i).trans hs) hr' hdRest hf'

private theorem ofFn_nodup {α : Type} {n : Nat} (f : Fin n → α)
    (hf : ∀ i j, f i = f j → i = j) : (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
      have e : j.succ = (0 : Fin (n + 1)) :=
        hf _ _ (by first | exact hj | exact hj.symm)
      have ev := congrArg Fin.val e
      simp at ev
    · apply ih
      intro i j hij
      have e : i.succ = j.succ := hf _ _ hij
      exact Fin.ext (Nat.succ.inj (congrArg Fin.val e))

theorem compact_reciprocal (marks : Array Bool) : Reciprocal (compact marks) := by
  unfold compact
  apply scan_reciprocal
  · simp [initial]
  · intro k hk
    simp [initial] at hk
  · exact ofFn_nodup (fun i : Fin marks.size => i) (fun _ _ h => h)
  · simp [initial]

-- These are semantic and source-level operation counts, not a runtime bound.
-- `ids` materializes a list and the inverse grows by push. Inverse
-- preallocation, word-RAM costs, and adjacency translation are separate.

private theorem step_lookup_unmarked (marks : Array Bool) (t : Tables marks.size)
    (j i : Fin marks.size) (hs : t.forward.size = marks.size)
    (hi : marked marks i = false) :
    lookup (step marks t j) i = lookup t i := by
  by_cases hji : j = i
  · subst j
    simp [step, hi, lookup]
  · cases hj : marked marks j with
    | false => simp [step, hj, lookup]
    | true =>
      have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
      have hb : i.val < t.forward.size := by
        simpa only [hs] using i.isLt
      have hread :
          (t.forward.setIfInBounds j.val (some t.inverse.size))[i.val]? =
            t.forward[i.val]? :=
        read_set_ne t.forward j.val i.val (some t.inverse.size) hne hb
      simpa [step, hj, lookup] using
        congrArg (fun r : Option (Option Nat) => r.getD none) hread

theorem scan_lookup_unmarked (marks : Array Bool) (rest : List (Fin marks.size))
    (i : Fin marks.size) (hi : marked marks i = false) :
    ∀ (t : Tables marks.size), t.forward.size = marks.size →
      lookup (scan marks rest t) i = lookup t i := by
  induction rest with
  | nil =>
    intro t _
    rfl
  | cons j rest ih =>
    intro t hs
    change lookup (scan marks rest (step marks t j)) i = lookup t i
    exact (ih (step marks t j) ((step_size marks t j).trans hs)).trans
      (step_lookup_unmarked marks t j i hs hi)

theorem lookup_none_of_unmarked (marks : Array Bool) (i : Fin marks.size)
    (hi : marked marks i = false) : lookup (compact marks) i = none := by
  have hs : (initial marks.size).forward.size = marks.size := by
    simp [initial]
  unfold compact
  rw [scan_lookup_unmarked marks (ids marks.size) i hi (initial marks.size) hs]
  change ((Array.replicate marks.size (none : Option Nat))[i.val]?).getD none = none
  simp [i.isLt]

private theorem inverse_index_of_marked (marks : Array Bool) (i : Fin marks.size)
    (hi : marked marks i = true) :
    ∃ (k : Nat) (hk : k < (compact marks).inverse.size),
      (compact marks).inverse[k]'hk = i := by
  have hids : i ∈ ids marks.size := by
    unfold ids
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hm : i ∈ (compact marks).inverse.toList := by
    rw [(compact_spec marks).2.2]
    exact List.mem_filter.mpr ⟨hids, hi⟩
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hm
  have hk' : k < (compact marks).inverse.size := by
    simpa using hk
  exact ⟨k, hk', by simpa using he⟩

theorem lookup_some_iff (marks : Array Bool) (i : Fin marks.size) (k : Nat) :
    lookup (compact marks) i = some k ↔
      ∃ hk : k < (compact marks).inverse.size, (compact marks).inverse[k]'hk = i := by
  constructor
  · intro h
    cases hm : marked marks i with
    | false =>
      rw [lookup_none_of_unmarked marks i hm] at h
      cases h
    | true =>
      obtain ⟨j, hj, he⟩ := inverse_index_of_marked marks i hm
      have hr : lookup (compact marks) i = some j := by
        simpa only [he] using compact_reciprocal marks j hj
      have e : j = k := Option.some.inj (hr.symm.trans h)
      subst k
      exact ⟨hj, he⟩
  · rintro ⟨hk, he⟩
    simpa only [he] using compact_reciprocal marks k hk

theorem lookup_exists_iff_marked (marks : Array Bool) (i : Fin marks.size) :
    (∃ k : Nat, lookup (compact marks) i = some k) ↔ marked marks i = true := by
  constructor
  · rintro ⟨k, hk⟩
    cases hm : marked marks i with
    | false =>
      rw [lookup_none_of_unmarked marks i hm] at hk
      cases hk
    | true => rfl
  · intro hm
    obtain ⟨k, hk, he⟩ := inverse_index_of_marked marks i hm
    exact ⟨k, (lookup_some_iff marks i k).mpr ⟨hk, he⟩⟩

end PaperB.CompactIds
