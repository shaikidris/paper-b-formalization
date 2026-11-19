-- lean-toolchain: leanprover/lean4:v4.35.0-rc3
import Std

namespace PaperB.QuotientBudget

universe u v w
variable {α : Type u} {β : Type v} {κ : Type w}

/-- Each input position emits zero or one output, even when entries repeat. -/
theorem length_filterMap_le (emit : α → Option β) (xs : List α) :
    (xs.filterMap emit).length ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    cases h : emit x with
    | none =>
      simpa [List.filterMap, h] using Nat.le_trans ih (Nat.le_succ xs.length)
    | some y =>
      simpa [List.filterMap, h] using Nat.succ_le_succ ih

/-- One bucket per enumerated key, in key order. Each bucket preserves
the order and multiplicity of its matching input occurrences. -/
def buckets [DecidableEq κ] (key : β → κ) (keys : List κ) (xs : List β) :
    List (List β) :=
  keys.map (fun k => xs.filter (fun x => decide (key x = k)))

def bucketTotal [DecidableEq κ] (key : β → κ) (keys : List κ)
    (xs : List β) : Nat :=
  ((buckets key keys xs).map List.length).sum

private theorem no_matches [DecidableEq κ] (q : κ) (keys : List κ)
    (h : q ∉ keys) :
    (keys.filter (fun k => decide (q = k))).length = 0 := by
  induction keys with
  | nil => rfl
  | cons k ks ih =>
    have hne : q ≠ k := fun e => h (List.mem_cons.mpr (Or.inl e))
    have ht : q ∉ ks := fun m => h (List.mem_cons.mpr (Or.inr m))
    simp [List.filter, hne, ih ht]

/-- A present key matches exactly one position in a duplicate-free enumeration. -/
theorem unique_match_count [DecidableEq κ] (q : κ) (keys : List κ)
    (hn : keys.Nodup) (hm : q ∈ keys) :
    (keys.filter (fun k => decide (q = k))).length = 1 := by
  induction keys with
  | nil => simp at hm
  | cons k ks ih =>
    have hh := List.nodup_cons.mp hn
    by_cases e : q = k
    · subst q
      simp [List.filter, no_matches k ks hh.1]
    · have ht : q ∈ ks := (List.mem_cons.mp hm).resolve_left e
      simp [List.filter, e, ih hh.2 ht]

private theorem bucketTotal_nil [DecidableEq κ] (key : β → κ)
    (keys : List κ) : bucketTotal key keys [] = 0 := by
  induction keys with
  | nil => rfl
  | cons k ks ih =>
    simpa only [bucketTotal, buckets, List.map_cons, List.sum_cons,
      List.filter_nil, List.length_nil, Nat.zero_add] using ih

private theorem bucketTotal_cons [DecidableEq κ] (key : β → κ)
    (keys : List κ) (x : β) (xs : List β) :
    bucketTotal key keys (x :: xs) =
      (keys.filter (fun k => decide (key x = k))).length +
        bucketTotal key keys xs := by
  induction keys with
  | nil => rfl
  | cons k ks ih =>
    simp only [bucketTotal, buckets, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    by_cases h : key x = k <;>
      simp [List.filter, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Exact accounting for complete, duplicate-free key enumeration. -/
theorem bucketTotal_eq_length [DecidableEq κ] (key : β → κ)
    (keys : List κ) (xs : List β) (hn : keys.Nodup)
    (hc : ∀ x ∈ xs, key x ∈ keys) :
    bucketTotal key keys xs = xs.length := by
  induction xs with
  | nil => exact bucketTotal_nil key keys
  | cons x xs ih =>
    have hx : key x ∈ keys := hc x (List.Mem.head xs)
    have ht : ∀ y ∈ xs, key y ∈ keys :=
      fun y hy => hc y (List.Mem.tail x hy)
    simp only [bucketTotal_cons, unique_match_count (key x) keys hn hx,
      ih ht, List.length_cons, Nat.add_comm 1]

/-- EX1.3: the grouped occurrence count is exactly the emitted count and is
bounded by the original arc occurrence count. This is not a runtime bound. -/
theorem emitted_bucket_budget [DecidableEq κ] (emit : α → Option (κ × β))
    (arcs : List α) (keys : List κ) (hn : keys.Nodup)
    (hc : ∀ p ∈ arcs.filterMap emit, p.1 ∈ keys) :
    bucketTotal Prod.fst keys (arcs.filterMap emit) = (arcs.filterMap emit).length ∧
    bucketTotal Prod.fst keys (arcs.filterMap emit) ≤ arcs.length := by
  have he := bucketTotal_eq_length Prod.fst keys (arcs.filterMap emit) hn hc
  refine ⟨he, ?_⟩
  rw [he]
  exact length_filterMap_le emit arcs

/-- One root record and at most one child record per input position. -/
theorem root_child_budget (root : α → β) (child : α → Option κ)
    (vertices : List α) :
    (vertices.map root).length + (vertices.filterMap child).length ≤
      2 * vertices.length := by
  calc
    _ ≤ vertices.length + vertices.length := by
      rw [List.length_map]
      exact Nat.add_le_add_left (length_filterMap_le child vertices) vertices.length
    _ = 2 * vertices.length := by
      rw [show (2 : Nat) = 1 + 1 from rfl, Nat.add_mul, Nat.one_mul]

end PaperB.QuotientBudget
