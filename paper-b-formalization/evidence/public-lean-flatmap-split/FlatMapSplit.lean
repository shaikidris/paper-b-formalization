import Std

theorem flatMap_split_at_mem {α β : Type} (f : α → List β)
    {xs : List α} {x : α} (hx : x ∈ xs) :
    ∃ before after : List β, xs.flatMap f = before ++ f x ++ after := by
  obtain ⟨ys, zs, rfl⟩ := List.append_of_mem hx
  refine ⟨ys.flatMap f, zs.flatMap f, ?_⟩
  simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]
