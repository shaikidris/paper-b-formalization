import Std

namespace EX24

universe u

variable {α : Type u} {n : Nat}

/-- Existing incoming rows in head-ID order. Every labelled occurrence is
    retained. `src` in the gather below projects its quotient predecessor ID. -/
structure Incoming (α : Type u) (n : Nat) where
  rows : List (List α)
  length_eq : rows.length = n

def Incoming.row (x : Incoming α n) (y : Fin n) : List α :=
  x.rows[y.val]'(by simpa only [x.length_eq] using y.isLt)

private structure Stamp (n : Nat) where
  data : Array Nat
  size_eq : data.size = n

private def Stamp.zero (n : Nat) : Stamp n :=
  ⟨Array.replicate n 0, by simp⟩

@[inline] private def Stamp.read (s : Stamp n) (i : Fin n) : Nat :=
  s.data[i.val]'(by simpa only [s.size_eq] using i.isLt)

@[inline] private def Stamp.write (s : Stamp n) (i : Fin n) (g : Nat) :
    Stamp n :=
  ⟨s.data.set i.val g (by simpa only [s.size_eq] using i.isLt),
    by simpa using s.size_eq⟩

@[simp] private theorem Stamp.read_write_same
    (s : Stamp n) (i : Fin n) (g : Nat) :
    (s.write i g).read i = g := by
  have hi : i.val < s.data.size := by
    simpa only [s.size_eq] using i.isLt
  have hnew : i.val < (s.data.set i.val g hi).size := by
    simpa using hi
  change (s.data.set i.val g hi)[i.val]'hnew = g
  rw [Array.getElem_set] <;> simp

private theorem Stamp.read_write_other
    (s : Stamp n) (i j : Fin n) (g : Nat) (h : j ≠ i) :
    (s.write i g).read j = s.read j := by
  have hi : i.val < s.data.size := by
    simpa only [s.size_eq] using i.isLt
  have hj : j.val < s.data.size := by
    simpa only [s.size_eq] using j.isLt
  have hnew : j.val < (s.data.set i.val g hi).size := by
    simpa using hj
  have hij : i.val ≠ j.val := fun e => h (Fin.ext e.symm)
  change (s.data.set i.val g hi)[j.val]'hnew = s.data[j.val]'hj
  simp [Array.getElem_set, hij]

private theorem Stamp.zero_fresh (n : Nat) (i : Fin n) :
    (Stamp.zero n).read i < 1 := by
  simp [Stamp.zero, Stamp.read]

private structure RowResult (n : Nat) where
  stamp : Stamp n
  preds : List (Fin n)
  arcScans : Nat
  stampUpdates : Nat

/-- The tail-recursive inner loop. One projection and one stamp read per
    occurrence; one stamp update and one predecessor cons on a miss.
    Consing gives reverse first-occurrence order. -/
private def scan (src : α → Fin n) (g : Nat) :
    List α → Stamp n → List (Fin n) → Nat → Nat → RowResult n
  | [], s, acc, a, d => ⟨s, acc, a, d⟩
  | e :: es, s, acc, a, d =>
      let p := src e
      if s.read p = g then
        scan src g es s acc (a + 1) d
      else
        scan src g es (s.write p g) (p :: acc) (a + 1) (d + 1)

private theorem scan_spec (src : α → Fin n) (g : Nat)
    (row : List α) (s : Stamp n) (acc : List (Fin n)) (a d : Nat)
    (hs : ∀ u, s.read u ≤ g)
    (ha : ∀ u, s.read u = g ↔ u ∈ acc)
    (hn : acc.Nodup) :
    let o := scan src g row s acc a d
    (∀ u, o.stamp.read u ≤ g) ∧
    (∀ u, u ∈ o.preds ↔ u ∈ acc ∨ u ∈ row.map src) ∧
    o.preds.Nodup ∧
    o.arcScans = a + row.length ∧
    o.preds.length + d = acc.length + o.stampUpdates ∧
    o.stampUpdates + a ≤ o.arcScans + d := by
  induction row generalizing s acc a d with
  | nil =>
      simp [scan, hs, hn, Nat.add_comm]
  | cons e es ih =>
      have hlen : (a + 1) + es.length = a + (e :: es).length := by
        calc
          (a + 1) + es.length = (a + es.length) + 1 :=
            Nat.add_right_comm a 1 es.length
          _ = a + (e :: es).length := by
            simpa only [List.length_cons] using (Nat.add_assoc a es.length 1)
      by_cases h : s.read (src e) = g
      · have he : src e ∈ acc := (ha (src e)).mp h
        rcases ih s acc (a + 1) d hs ha hn with
          ⟨hb, hm, hnd, hscan, hwrite, hcost⟩
        simp only [scan, ite_eq_left h]
        refine ⟨hb, ?_, hnd, ?_, hwrite, ?_⟩
        · intro u
          rw [hm u]
          simp only [List.map_cons, List.mem_cons]
          constructor
          · intro hu
            rcases hu with hu | hu
            · exact Or.inl hu
            · exact Or.inr (Or.inr hu)
          · intro hu
            rcases hu with hu | hu | hu
            · exact Or.inl hu
            · exact Or.inl (hu.symm ▸ he)
            · exact Or.inr hu
        · exact hscan.trans hlen
        · exact Nat.le_trans (Nat.add_le_add_left (Nat.le_succ a) _) hcost
      · let t := s.write (src e) g
        have he : src e ∉ acc := fun he => h ((ha (src e)).mpr he)
        have ht : ∀ u, t.read u ≤ g := by
          intro u
          by_cases q : u = src e
          · subst u
            simp [t]
          · simpa only [t, Stamp.read_write_other s (src e) u g q] using hs u
        have hta : ∀ u, t.read u = g ↔ u ∈ src e :: acc := by
          intro u
          by_cases q : u = src e
          · subst u
            simp [t]
          · simp [t, Stamp.read_write_other s (src e) u g q, q, ha u]
        have hna : (src e :: acc).Nodup :=
          List.nodup_cons.mpr ⟨he, hn⟩
        rcases ih t (src e :: acc) (a + 1) (d + 1) ht hta hna with
          ⟨hb, hm, hnd, hscan, hwrite, hcost⟩
        simp only [scan, ite_eq_right h]
        let o := scan src g es t (src e :: acc) (a + 1) (d + 1)
        refine ⟨hb, ?_, hnd, ?_, ?_, ?_⟩
        · intro u
          rw [hm u]
          simp only [List.map_cons, List.mem_cons, or_assoc, or_left_comm]
        · exact hscan.trans hlen
        · change o.preds.length + d = acc.length + o.stampUpdates
          have hw : (o.preds.length + d) + 1 =
              (acc.length + o.stampUpdates) + 1 := by
            calc
              (o.preds.length + d) + 1 = o.preds.length + (d + 1) :=
                Nat.add_assoc _ _ _
              _ = (acc.length + 1) + o.stampUpdates := by
                simpa only [List.length_cons] using hwrite
              _ = (acc.length + o.stampUpdates) + 1 :=
                Nat.add_right_comm _ _ _
          exact Nat.succ.inj hw
        · change o.stampUpdates + a ≤ o.arcScans + d
          have hc : (o.stampUpdates + a) + 1 ≤ (o.arcScans + d) + 1 := by
            calc
              (o.stampUpdates + a) + 1 = o.stampUpdates + (a + 1) :=
                Nat.add_assoc _ _ _
              _ ≤ o.arcScans + (d + 1) := hcost
              _ = (o.arcScans + d) + 1 := (Nat.add_assoc _ _ _).symm
          exact Nat.le_of_succ_le_succ hc

/-- Sum of row lengths. Used in specifications, not called by the gather. -/
def entryCount {β : Type u} : List (List β) → Nat
  | [] => 0
  | r :: rs => r.length + entryCount rs

/-- Position-by-position correspondence; row order is unchanged. -/
inductive RowsOK (src : α → Fin n) :
    List (List α) → List (List (Fin n)) → Prop where
  | nil : RowsOK src [] []
  | cons {r rs p ps} :
      (∀ u, u ∈ p ↔ u ∈ r.map src) →
      p.Nodup →
      RowsOK src rs ps →
      RowsOK src (r :: rs) (p :: ps)

theorem RowsOK.length_eq {src : α → Fin n} {rs ps}
    (h : RowsOK src rs ps) : ps.length = rs.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

theorem RowsOK.atIndex {src : α → Fin n} {rs ps}
    (h : RowsOK src rs ps) :
    ∀ (i : Nat) (hr : i < rs.length) (hp : i < ps.length),
      (∀ u, u ∈ ps[i]'hp ↔ u ∈ (rs[i]'hr).map src) ∧
      (ps[i]'hp).Nodup := by
  induction h with
  | nil =>
      intro i hr hp
      exact (Nat.not_lt_zero i hr).elim
  | cons hm hn _ ih =>
      intro i hr hp
      cases i with
      | zero => exact ⟨hm, hn⟩
      | succ i =>
          exact ih i (Nat.lt_of_succ_lt_succ hr) (Nat.lt_of_succ_lt_succ hp)

private structure Batch (n : Nat) where
  preds : List (List (Fin n))
  arcScans : Nat
  stampUpdates : Nat

/-- Only the current stamp array is threaded forward. No row clears it,
    and neither the old nor the final stamp is stored in the output. -/
private def gatherRows (src : α → Fin n) :
    List (List α) → Nat → Stamp n → Batch n
  | [], _, _ => ⟨[], 0, 0⟩
  | row :: rest, g, s =>
      match scan src g row s [] 0 0 with
      | ⟨t, ps, a, d⟩ =>
          match gatherRows src rest (g + 1) t with
          | ⟨qs, b, f⟩ => ⟨ps :: qs, a + b, d + f⟩

private theorem gatherRows_spec (src : α → Fin n)
    (rows : List (List α)) (g : Nat) (s : Stamp n)
    (hf : ∀ u, s.read u < g) :
    let o := gatherRows src rows g s
    RowsOK src rows o.preds ∧
    o.arcScans = entryCount rows ∧
    o.stampUpdates = entryCount o.preds ∧
    o.stampUpdates ≤ o.arcScans := by
  induction rows generalizing g s with
  | nil =>
      exact ⟨RowsOK.nil, rfl, rfl, Nat.le_refl 0⟩
  | cons row rest ih =>
      have hle : ∀ u, s.read u ≤ g := fun u => Nat.le_of_lt (hf u)
      have hacc : ∀ u, s.read u = g ↔ u ∈ ([] : List (Fin n)) := by
        intro u
        simp [Nat.ne_of_lt (hf u)]
      cases hrow : scan src g row s [] 0 0 with
      | mk t ps a d =>
          have h := scan_spec src g row s [] 0 0 hle hacc (by simp)
          simp only [hrow] at h
          rcases h with ⟨hb, hm, hnd, hscan, hwrite, hcost⟩
          have ht : ∀ u, t.read u < g + 1 :=
            fun u => Nat.lt_succ_of_le (hb u)
          have ha : a = row.length := by simpa using hscan
          have hd : ps.length = d := by simpa using hwrite
          have hda : d ≤ a := by simpa using hcost
          cases hrest : gatherRows src rest (g + 1) t with
          | mk qs b f =>
              have hi := ih (g + 1) t ht
              simp only [hrest] at hi
              rcases hi with ⟨hok, hbs, hfs, hfb⟩
              simp only [gatherRows, hrow, hrest]
              refine ⟨RowsOK.cons ?_ hnd hok, ?_, ?_, ?_⟩
              · intro u
                simpa using hm u
              · change a + b = row.length + entryCount rest
                rw [ha, hbs]
              · change d + f = ps.length + entryCount qs
                rw [← hd, hfs]
              · exact Nat.add_le_add hda hfb

structure Prepared (α : Type u) (n : Nat) where
  raw : Incoming α n
  preds : List (List (Fin n))
  arcScans : Nat
  stampUpdates : Nat
  length_eq : preds.length = n

/-- Run once, then use `Prepared.head` on the result. The raw table is
    returned unchanged, not rebuilt from the predecessor lists. -/
def prepare (src : α → Fin n) (x : Incoming α n) : Prepared α n :=
  let o := gatherRows src x.rows 1 (Stamp.zero n)
  ⟨x, o.preds, o.arcScans, o.stampUpdates,
    (gatherRows_spec src x.rows 1 (Stamp.zero n) (Stamp.zero_fresh n)).1.length_eq.trans
      x.length_eq⟩

def Prepared.head (p : Prepared α n) (y : Fin n) : List (Fin n) :=
  p.preds[y.val]'(by simpa only [p.length_eq] using y.isLt)

@[simp] theorem prepare_raw (src : α → Fin n) (x : Incoming α n) :
    (prepare src x).raw = x := rfl

theorem prepare_spec (src : α → Fin n) (x : Incoming α n) :
    let p := prepare src x
    RowsOK src x.rows p.preds ∧
    p.arcScans = entryCount x.rows ∧
    p.stampUpdates = entryCount p.preds ∧
    p.stampUpdates ≤ p.arcScans :=
  gatherRows_spec src x.rows 1 (Stamp.zero n) (Stamp.zero_fresh n)

theorem prepare_head (src : α → Fin n) (x : Incoming α n) (y : Fin n) :
    let p := prepare src x
    (∀ u, u ∈ p.head y ↔ ∃ e, e ∈ p.raw.row y ∧ src e = u) ∧
    (p.head y).Nodup := by
  let p := prepare src x
  have hr : y.val < p.raw.rows.length := by
    simpa only [p.raw.length_eq] using y.isLt
  have hp : y.val < p.preds.length := by
    simpa only [p.length_eq] using y.isLt
  have h := RowsOK.atIndex (prepare_spec src x).1 y.val hr hp
  exact ⟨fun u => (h.1 u).trans List.mem_map, h.2⟩

/-!
Exact source-level accounting for one execution of `prepare`.

Let M = `entryCount x.rows` and D = `entryCount p.preds`.

  * `Stamp.zero` creates n stamp slots and initializes each once.
  * `scan` consumes M raw cons cells in total, calls `src` M times,
    and reads M stamp slots. Empty rows consume no arc and read no stamp.
  * The miss arm updates D stamp slots and constructs D predecessor
    cons cells. Including initialization, there are n + D stamp writes.
  * `gatherRows` constructs n outer output cons cells. Neither it nor
    `scan` sorts, reverses, or makes a second pass over any raw row.
    `entryCount`, `.map`, and the correctness proofs are not executed
    by `prepare`.

For words, count one payload word per stamp slot and two field words
per list cons (head and tail), with IDs and generations fitting in a
word. This gives exactly n scratch payload words and 2(n + D) output
list field words. The raw input is shared, so there is no new raw-row
storage. The sum below counts these two storage categories, not peak
heap bytes. It excludes headers, fixed-size result records and counters,
and the outer recursion's O(n) stack; the inner loop is tail recursive.
The counts are logical slot accesses, not runtime allocator, reference
count, copy-on-write, or hardware traffic counts. The executable does
not keep another version of the stamp array for use after an update.
-/

def Prepared.stampReads (p : Prepared α n) : Nat :=
  p.arcScans

def Prepared.totalStampWrites (p : Prepared α n) : Nat :=
  n + p.stampUpdates

def Prepared.stampAndListPayloadWords (p : Prepared α n) : Nat :=
  n + 2 * (n + p.stampUpdates)

theorem prepare_accounting (src : α → Fin n) (x : Incoming α n) :
    let p := prepare src x
    p.arcScans = entryCount x.rows ∧
    p.stampReads = entryCount x.rows ∧
    p.stampUpdates = entryCount p.preds ∧
    p.totalStampWrites = n + entryCount p.preds ∧
    p.stampAndListPayloadWords = n + 2 * (n + entryCount p.preds) ∧
    entryCount p.preds ≤ entryCount x.rows := by
  let p := prepare src x
  have ha : p.arcScans = entryCount x.rows := (prepare_spec src x).2.1
  have hd : p.stampUpdates = entryCount p.preds := (prepare_spec src x).2.2.1
  have hle : p.stampUpdates ≤ p.arcScans := (prepare_spec src x).2.2.2
  refine ⟨ha, ha, hd, ?_, ?_, ?_⟩
  · rw [Prepared.totalStampWrites, hd]
  · rw [Prepared.stampAndListPayloadWords, hd]
  · simpa only [ha, hd] using hle

end EX24
