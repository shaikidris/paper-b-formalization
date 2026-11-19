import PaperB.DistinctPredecessors

set_option autoImplicit false

namespace EX24

universe u v

/-- A trace of the outer copy loop. Each `cons` step pushes the existing
element, not a copy of its contents. In `buildPacked`, the element is a row. -/
inductive OuterPushes {β : Type v} :
    List β → Array β → Array β → Nat → Prop where
  | nil (a : Array β) : OuterPushes [] a a 0
  | cons {r : β} {rs : List β} {a b : Array β} {k : Nat} :
      OuterPushes rs (a.push r) b k →
      OuterPushes (r :: rs) a b (k + 1)

theorem OuterPushes.spec {β : Type v} {rs : List β}
    {a b : Array β} {k : Nat} (h : OuterPushes rs a b k) :
    b.toList = a.toList ++ rs ∧ k = rs.length := by
  induction h with
  | nil a => simp
  | cons _ ih =>
    constructor
    · simp [ih.1, List.append_assoc]
    · simp [ih.2]

private def pushOuter {β : Type v} : List β → Array β → Array β
  | [], a => a
  | r :: rs, a => pushOuter rs (a.push r)

private theorem pushOuter_trace {β : Type v} (rs : List β) (a : Array β) :
    OuterPushes rs a (pushOuter rs a) rs.length := by
  induction rs generalizing a with
  | nil => exact OuterPushes.nil a
  | cons r rs ih =>
    simpa only [pushOuter, List.length_cons] using
      (OuterPushes.cons (r := r) (a := a) (ih (a.push r)))

private def packTable {β : Type v} (cap : Nat) (rs : List β) : Array β :=
  pushOuter rs (Array.emptyWithCapacity cap)

private theorem packTable_trace {β : Type v} (cap : Nat) (rs : List β) :
    OuterPushes rs (Array.emptyWithCapacity cap) (packTable cap rs) rs.length :=
  pushOuter_trace rs (Array.emptyWithCapacity cap)

private theorem packTable_toList {β : Type v} (cap : Nat) (rs : List β) :
    (packTable cap rs).toList = rs := by
  simpa [Array.emptyWithCapacity] using (packTable_trace cap rs).spec.1

private theorem packTable_size {β : Type v} (cap : Nat) (rs : List β) :
    (packTable cap rs).size = rs.length := by
  simpa using congrArg List.length (packTable_toList cap rs)

private theorem list_get_congr {β : Type v} {as bs : List β}
    (e : as = bs) (i : Nat) (ha : i < as.length) (hb : i < bs.length) :
    as[i]'ha = bs[i]'hb := by
  cases e
  rfl

private theorem packTable_get {β : Type v} (cap : Nat) (rs : List β)
    (i : Nat) (h : i < (packTable cap rs).size) :
    (packTable cap rs)[i]'h = rs[i]'(by simpa only [packTable_size] using h) := by
  have ht : i < (packTable cap rs).toList.length := by simpa using h
  calc
    (packTable cap rs)[i]'h = (packTable cap rs).toList[i]'ht := by
      first | rfl | simp
    _ = rs[i]'(by simpa only [packTable_size] using h) :=
      list_get_congr (packTable_toList cap rs) i ht _

variable {α : Type u} {n : Nat}

structure Packed (α : Type u) (n : Nat) where
  rawRows : Array (List α)
  predRows : Array (List (Fin n))
  arcScans : Nat
  stampUpdates : Nat
  raw_size : rawRows.size = n
  pred_size : predRows.size = n

/-- One array read. The bounds proof is erased; the row is returned as-is. -/
@[inline] def Packed.rawRow (p : Packed α n) (y : Fin n) : List α :=
  p.rawRows[y.val]'(by simpa only [p.raw_size] using y.isLt)

/-- One array read, with no traversal of the table or of the returned row. -/
@[inline] def Packed.head (p : Packed α n) (y : Fin n) : List (Fin n) :=
  p.predRows[y.val]'(by simpa only [p.pred_size] using y.isLt)

/-- Run the stamp pass once and pack just the two outer row tables. The
result retains the row lists and existing counters, not the `Prepared` record
or either outer list. -/
def buildPacked (src : α → Fin n) (x : Incoming α n) : Packed α n :=
  let p := prepare src x
  { rawRows := packTable n x.rows
    predRows := packTable n p.preds
    arcScans := p.arcScans
    stampUpdates := p.stampUpdates
    raw_size := (packTable_size n x.rows).trans x.length_eq
    pred_size := (packTable_size n p.preds).trans p.length_eq }

theorem buildPacked_tables (src : α → Fin n) (x : Incoming α n) :
    (buildPacked src x).rawRows.toList = x.rows ∧
    (buildPacked src x).predRows.toList = (prepare src x).preds :=
  ⟨packTable_toList n x.rows, packTable_toList n (prepare src x).preds⟩

@[simp] theorem buildPacked_rawRow (src : α → Fin n)
    (x : Incoming α n) (y : Fin n) :
    (buildPacked src x).rawRow y = x.row y :=
  packTable_get n x.rows y.val
    (by simpa only [packTable_size, x.length_eq] using y.isLt)

@[simp] theorem buildPacked_head (src : α → Fin n)
    (x : Incoming α n) (y : Fin n) :
    (buildPacked src x).head y = (prepare src x).head y :=
  packTable_get n (prepare src x).preds y.val
    (by simpa only [packTable_size, (prepare src x).length_eq] using y.isLt)

theorem buildPacked_head_spec (src : α → Fin n) (x : Incoming α n)
    (y : Fin n) :
    (∀ u, u ∈ (buildPacked src x).head y ↔
      ∃ e, e ∈ (buildPacked src x).rawRow y ∧ src e = u) ∧
    ((buildPacked src x).head y).Nodup := by
  simpa only [buildPacked_head, buildPacked_rawRow, prepare_raw] using
    (prepare_head src x y)

/-- Counts occurrences, not distinct values. `test` can select a label,
a quotient predecessor via `src`, or any other class of original arcs. -/
theorem buildPacked_occurrences (src : α → Fin n) (x : Incoming α n)
    (y : Fin n) (test : α → Bool) :
    ((buildPacked src x).rawRow y).countP test = (x.row y).countP test :=
  congrArg (fun r : List α => r.countP test) (buildPacked_rawRow src x y)

theorem buildPacked_accounting (src : α → Fin n) (x : Incoming α n) :
    let q := buildPacked src x
    q.arcScans = entryCount x.rows ∧
    q.stampUpdates = entryCount q.predRows.toList ∧
    q.stampUpdates ≤ q.arcScans := by
  have h := prepare_spec src x
  change (prepare src x).arcScans = entryCount x.rows ∧
    (prepare src x).stampUpdates =
      entryCount (packTable n (prepare src x).preds).toList ∧
    (prepare src x).stampUpdates ≤ (prepare src x).arcScans
  rw [packTable_toList]
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/--
These are the traces of the only two `packTable` calls in `buildPacked`.
Each starts with one empty array of capacity `n` and pushes exactly `n`
row references: `n + n` top-level pushes in all. The loop is tail recursive
and its only recursive argument traversal is down the outer list. It never
matches on a row or constructs an inner cons cell. No preliminary length
traversal is needed, since `n` is already known.

This is source-level accounting, not a count of allocator or reference-count
traffic. The traces, `toList` specifications, and bounds proofs are erased.
On the packed result, each `Fin` lookup is a single constant-time array
read in the word-index model.
-/
theorem buildPacked_conversion_cost (src : α → Fin n) (x : Incoming α n) :
    OuterPushes x.rows (Array.emptyWithCapacity n)
      (buildPacked src x).rawRows n ∧
    OuterPushes (prepare src x).preds (Array.emptyWithCapacity n)
      (buildPacked src x).predRows n := by
  constructor
  · change OuterPushes x.rows (Array.emptyWithCapacity n) (packTable n x.rows) n
    simpa only [x.length_eq] using (packTable_trace n x.rows)
  · change OuterPushes (prepare src x).preds (Array.emptyWithCapacity n)
      (packTable n (prepare src x).preds) n
    simpa only [(prepare src x).length_eq] using
      (packTable_trace n (prepare src x).preds)

end EX24
