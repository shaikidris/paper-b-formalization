import PaperB.DenseQuotientRows
import PaperB.StaticOracleTree
import PaperB.SharedLocalOrder

namespace PaperB.DenseQuotientLocalOrder

open EX51
open PaperB.DenseQuotientRows PaperB.EX16Assembly
open EX51.LocalSchedule
  (Slot Choice Entry Tag Schedule OneAt raw raw_spec schedule schedule_row
    schedule_increasing)

set_option autoImplicit false

variable {g : Digraph} {r : Fin g.vertexCount}
variable (q : OriginalReader g r)
variable {buckets : PaperB.ForestLayout.ChildLists q.count} (rows : Layout buckets)
variable (childOK : ∀ u c : Fin q.count,
  Occurs buckets u (.inr c) ↔ c ≠ q.input.root ∧ q.input.parent.read c = u)

def rootSlot (c : Fin q.count) : Slot rows.length :=
  ⟨c, rows.encode c ⟨.inl c, rfl⟩⟩

def childSlot (c : Fin q.count) (hc : c ≠ q.input.root) : Slot rows.length :=
  let p := q.input.parent.read c
  ⟨p, rows.encode p ⟨.inr c, (childOK p c).mpr ⟨hc, rfl⟩⟩⟩

/-- One shared ID lookup per input vertex. Child slots use the layout's inverse
lookup, not a search in the owner's row. -/
def pick (z : Fin g.vertexCount) : Choice rows.length :=
  match q.ids.find z with
  | none => ⟨none, none⟩
  | some c =>
      ⟨some (rootSlot q rows c),
        if hc : c ≠ q.input.root then some (childSlot q rows childOK c hc)
        else none⟩

variable (order : Array (Fin g.vertexCount))

/-- Consume the supplied Kahn ID array in its original order. -/
def build : Schedule rows.length :=
  schedule (pick q rows childOK) order.toList

theorem at_most_two (z : Fin g.vertexCount) (n : Nat) :
    (raw (pick q rows childOK) n [z]).1.length ≤ 2 := by
  simpa using (raw_spec (pick q rows childOK) [z] n).2

theorem one_at
    (noSelf : ∀ c : Fin q.count, c ≠ q.input.root → q.input.parent.read c ≠ c)
    (z : Fin g.vertexCount) (u : Fin q.count) :
    OneAt (pick q rows childOK z) u := by
  cases hf : q.ids.find z with
  | none => simp [OneAt, pick, hf]
  | some c =>
      by_cases hc : c ≠ q.input.root
      · unfold OneAt
        rintro ⟨hr, hp⟩
        have h₁ : c = u := by simpa [pick, hf, rootSlot] using hr
        have h₂ : q.input.parent.read c = u := by
          simpa [pick, hf, hc, childSlot] using hp
        exact noSelf c hc (h₂.trans h₁.symm)
      · simp [OneAt, pick, hf, hc]

theorem stable (u : Fin q.count) :
    (build q rows childOK order).rows.row u =
      (raw (pick q rows childOK) 0 order.toList).1.filter
        (fun e => decide (e.owner = u)) :=
  schedule_row (pick q rows childOK) order.toList u

theorem increasing
    (noSelf : ∀ c : Fin q.count, c ≠ q.input.root → q.input.parent.read c ≠ c)
    (u : Fin q.count) :
    (((build q rows childOK order).rows.row u).map (fun e => e.source)).Pairwise
      (· < ·) :=
  schedule_increasing (pick q rows childOK) order.toList u
    (fun z _ => one_at q rows childOK noSelf z u)

variable (rank : Fin g.vertexCount → Nat)

/-- These laws are used only in proofs. In particular `build` does not read
ranks or probe the original translation in reverse. -/
structure Laws : Prop where
  rankAt : ∀ (i : Nat) (hi : i < order.toList.length),
    rank (order.toList[i]'hi) = i
  retained : ∀ c : Fin q.count, q.ids.originals.read c ∈ order.toList
  find_iff : ∀ (z : Fin g.vertexCount) (c : Fin q.count),
    q.ids.find z = some c ↔ q.ids.originals.read c = z

private theorem raw_cons {α : Type} {B : Nat} {L : Fin B → Nat}
    (p : α → Choice L) (n : Nat) (a : α) (xs : List α) :
    (raw p n (a :: xs)).1 = (raw p n [a]).1 ++ (raw p (n + 1) xs).1 := by
  simp only [raw, List.append_nil]

private theorem raw_mem_rank {α : Type} {B : Nat} {L : Fin B → Nat}
    (p : α → Choice L) (rk : α → Nat) (xs : List α) (n : Nat)
    (hr : ∀ (i : Nat) (hi : i < xs.length), rk (xs[i]'hi) = n + i)
    (e : Entry L) :
    e ∈ (raw p n xs).1 ↔ ∃ a ∈ xs, e ∈ (raw p (rk a) [a]).1 := by
  induction xs generalizing n with
  | nil => simp [raw]
  | cons a xs ih =>
      have ha : rk a = n := by
        have h0 := hr 0 (by simp)
        change rk a = n + 0 at h0
        simpa only [Nat.add_zero] using h0
      have ht (i : Nat) (hi : i < xs.length) :
          rk (xs[i]'hi) = (n + 1) + i := by
        have hb : i + 1 < (a :: xs).length := by
          simpa only [List.length_cons] using Nat.succ_lt_succ hi
        have hn : n + (i + 1) = (n + 1) + i := by omega
        simpa only [List.getElem_cons_succ, hn] using hr (i + 1) hb
      rw [raw_cons, List.mem_append, ih (n + 1) ht]
      constructor
      · rintro (he | ⟨z, hz, he⟩)
        · exact ⟨a, by simp, by simpa only [ha] using he⟩
        · exact ⟨z, List.mem_cons.mpr (Or.inr hz), he⟩
      · rintro ⟨z, hz, he⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inl (by simpa only [ha] using he)
        · exact Or.inr ⟨z, hz, he⟩

private def entry {B : Nat} {L : Fin B → Nat}
    (s : Slot L) (tag : Tag) (n : Nat) : Entry L :=
  ⟨s.owner, s.index, tag, n⟩

def rootEntry (c : Fin q.count) (n : Nat) : Entry rows.length :=
  entry (rootSlot q rows c) .root n

def childEntry (c : Fin q.count) (hc : c ≠ q.input.root) (n : Nat) :
    Entry rows.length :=
  entry (childSlot q rows childOK c hc) .child n

private theorem singleton_iff (z : Fin g.vertexCount) (n : Nat)
    (e : Entry rows.length) :
    e ∈ (raw (pick q rows childOK) n [z]).1 ↔
      ∃ c, q.ids.find z = some c ∧
        (e = rootEntry q rows c n ∨
          ∃ hc : c ≠ q.input.root, e = childEntry q rows childOK c hc n) := by
  let P (c : Fin q.count) : Prop :=
    e = rootEntry q rows c n ∨
      ∃ hc : c ≠ q.input.root, e = childEntry q rows childOK c hc n
  change _ ↔ ∃ c, q.ids.find z = some c ∧ P c
  cases hf : q.ids.find z with
  | none =>
      simp only [raw, pick, hf]
      change e ∈ ([] : List (Entry rows.length)) ↔ _
      simp
  | some c =>
      simp only [raw, pick, hf]
      have hx : (∃ d, some c = some d ∧ P d) ↔ P c := by
        constructor
        · rintro ⟨d, hd, h⟩
          have hcd := Option.some.inj hd
          subst d
          exact h
        · exact fun h => ⟨c, rfl, h⟩
      rw [hx]
      by_cases hc : c ≠ q.input.root
      · rw [dif_pos hc]
        change e ∈ [rootEntry q rows c n, childEntry q rows childOK c hc n] ↔ P c
        simp only [List.mem_cons, List.not_mem_nil, or_false, P]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨hc, h⟩
        · rintro (h | ⟨_, h⟩)
          · exact Or.inl h
          · exact Or.inr h
      · rw [dif_neg hc]
        change e ∈ [rootEntry q rows c n] ↔ P c
        simp only [List.mem_cons, List.not_mem_nil, or_false, P]
        constructor
        · exact Or.inl
        · rintro (h | ⟨hd, _⟩)
          · exact h
          · exact (hc hd).elim

/-- Exact records, including their tags, encoded slots, and Kahn positions. -/
theorem row_entry_iff (laws : Laws q order rank) (u : Fin q.count)
    (e : Entry rows.length) :
    e ∈ (build q rows childOK order).rows.row u ↔
      e = rootEntry q rows u (rank (q.ids.originals.read u)) ∨
        ∃ (c : Fin q.count) (hc : c ≠ q.input.root),
          q.input.parent.read c = u ∧
          e = childEntry q rows childOK c hc (rank (q.ids.originals.read c)) := by
  rw [stable, List.mem_filter, decide_eq_true_eq]
  rw [raw_mem_rank (pick q rows childOK) rank order.toList 0
    (fun i hi => by simpa only [Nat.zero_add] using laws.rankAt i hi) e]
  constructor
  · rintro ⟨⟨z, _, hz⟩, hu⟩
    obtain ⟨c, hf, he⟩ := (singleton_iff q rows childOK z (rank z) e).mp hz
    have ho := (laws.find_iff z c).mp hf
    subst z
    rcases he with h | ⟨hc, h⟩
    · subst e
      change c = u at hu
      subst c
      exact Or.inl rfl
    · subst e
      exact Or.inr ⟨c, hc, hu, rfl⟩
  · rintro (h | ⟨c, hc, hp, h⟩)
    · subst e
      refine ⟨⟨q.ids.originals.read u, laws.retained u, ?_⟩, rfl⟩
      exact (singleton_iff q rows childOK _ _ _).mpr
        ⟨u, (laws.find_iff _ u).mpr rfl, Or.inl rfl⟩
    · subst e
      refine ⟨⟨q.ids.originals.read c, laws.retained c, ?_⟩, hp⟩
      exact (singleton_iff q rows childOK _ _ _).mpr
        ⟨c, (laws.find_iff _ c).mpr rfl, Or.inr ⟨hc, rfl⟩⟩

def keyOf (e : Entry rows.length) : Key q.count :=
  rows.key e.owner e.slot

private theorem rootEntry_key (c : Fin q.count) (n : Nat) :
    keyOf q rows (rootEntry q rows c n) = .inl c :=
  congrArg Subtype.val (rows.decode_encode c ⟨.inl c, rfl⟩)

private theorem childEntry_key (c : Fin q.count) (hc : c ≠ q.input.root) (n : Nat) :
    keyOf q rows (childEntry q rows childOK c hc n) = .inr c :=
  congrArg Subtype.val (rows.decode_encode (q.input.parent.read c)
    ⟨.inr c, (childOK _ c).mpr ⟨hc, rfl⟩⟩)


end PaperB.DenseQuotientLocalOrder
