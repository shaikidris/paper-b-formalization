import Std

theorem flatMap_split_at_mem {α β : Type} (f : α → List β)
    {xs : List α} {x : α} (hx : x ∈ xs) :
    ∃ before after : List β, xs.flatMap f = before ++ f x ++ after := by
  obtain ⟨ys, zs, rfl⟩ := List.append_of_mem hx
  refine ⟨ys.flatMap f, zs.flatMap f, ?_⟩
  simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]

def concatMapList {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | x :: xs => f x ++ concatMapList f xs

theorem concatMapList_eq_flatMap {α β : Type} (f : α → List β) (l : List α) :
    concatMapList f l = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [concatMapList, List.flatMap_cons, ih]

theorem mem_concatMapList_iff {α β : Type} (f : α → List β) (l : List α) (y : β) :
    y ∈ concatMapList f l ↔ ∃ x : α, x ∈ l ∧ y ∈ f x := by
  rw [concatMapList_eq_flatMap]
  exact List.mem_flatMap

theorem concatMapList_congr {α β : Type} {f g : α → List β} {l : List α}
    (hEq : ∀ x : α, x ∈ l → f x = g x) :
    concatMapList f l = concatMapList g l := by
  revert hEq
  induction l with
  | nil =>
    intro _
    rfl
  | cons x xs ih =>
    intro hEq
    have hHead : f x = g x := hEq x (by simp)
    have hTail : ∀ z : α, z ∈ xs → f z = g z := by
      intro z hz
      exact hEq z (List.mem_cons.mpr (Or.inr hz))
    simp only [concatMapList, hHead, ih hTail]

theorem exists_split_concatMapList {α β : Type} (f : α → List β) :
    ∀ {l : List α} {c : α}, c ∈ l →
      ∃ before after : List β, concatMapList f l = before ++ f c ++ after := by
  intro l c hc
  rw [concatMapList_eq_flatMap]
  exact flatMap_split_at_mem f hc
