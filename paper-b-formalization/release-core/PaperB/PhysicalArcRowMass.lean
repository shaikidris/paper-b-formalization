import PaperB.ActualSiblingEmitter
import PaperB.FiniteSiblingBudget
import PaperB.DensePhysicalArcCounts

namespace PaperB

private theorem physicalRows_mem_ofFn {α : Type} {n : Nat}
    (f : Fin n → α) (i : Fin n) : f i ∈ List.ofFn f := by
  apply List.mem_iff_getElem.mpr
  refine ⟨i.val, by simpa only [List.length_ofFn] using i.isLt, ?_⟩
  simp only [List.getElem_ofFn]

private theorem physicalRows_nodup_ofFn {α : Type} {n : Nat}
    (f : Fin n → α) (hf : ∀ i j, f i = f j → i = j) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hm
        obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
        let j : Fin n := ⟨i, by simpa only [List.length_ofFn] using hi⟩
        have hj : f j.succ = f 0 := by
          simpa only [List.getElem_ofFn, Function.comp_def] using he
        have hv := congrArg Fin.val (hf j.succ 0 hj)
        simp only [Fin.val_succ, Fin.val_zero] at hv <;> omega
      · apply ih
        intro i j he
        apply Fin.ext
        have hv := congrArg Fin.val (hf i.succ j.succ he)
        change i.val + 1 = j.val + 1 at hv
        omega

private theorem physicalRows_remove_owner {α : Type}
    (w : α → Nat) (a : α) (ys : List α)
    (hy : ys.Nodup) (ha : a ∈ ys) :
    ∃ zs : List α, zs.Nodup ∧
      (∀ b, b ∈ zs ↔ b ∈ ys ∧ b ≠ a) ∧
      (ys.map w).sum = w a + (zs.map w).sum := by
  classical
  induction ys with
  | nil => simp at ha
  | cons y ys ih =>
      obtain ⟨hny, hys⟩ := List.nodup_cons.mp hy
      by_cases hya : y = a
      · subst y
        refine ⟨ys, hys, ?_, rfl⟩
        intro b
        constructor
        · intro hb
          refine ⟨List.mem_cons.mpr (Or.inr hb), ?_⟩
          intro hba
          subst b
          exact hny hb
        · rintro ⟨hb, hne⟩
          exact (List.mem_cons.mp hb).resolve_left hne
      · have ha' : a ∈ ys :=
          (List.mem_cons.mp ha).resolve_left (Ne.symm hya)
        obtain ⟨zs, hzs, hz, hw⟩ := ih hys ha'
        refine ⟨y :: zs, List.nodup_cons.mpr ⟨?_, hzs⟩, ?_, ?_⟩
        · intro hb
          exact hny ((hz y).mp hb).1
        · intro b
          simp only [List.mem_cons, hz]
          constructor
          · rintro (rfl | ⟨hb, hn⟩)
            · exact ⟨Or.inl rfl, hya⟩
            · exact ⟨Or.inr hb, hn⟩
          · rintro ⟨hb, hn⟩
            rcases hb with he | hb
            · exact Or.inl he
            · exact Or.inr ⟨hb, hn⟩
        · simp only [List.map_cons, List.sum_cons, hw]
          omega

/-- Restrict a sum by removing owner indices, not occurrences within rows. -/
private theorem physicalRows_split_sum {α : Type}
    (w : α → Nat) (xs ys : List α) (hx : xs.Nodup) (hy : ys.Nodup)
    (hsub : ∀ b, b ∈ xs → b ∈ ys) :
    ∃ zs : List α, (∀ b, b ∈ zs → b ∈ ys ∧ b ∉ xs) ∧
      (ys.map w).sum = (xs.map w).sum + (zs.map w).sum := by
  induction xs generalizing ys with
  | nil => exact ⟨ys, by simp, by simp⟩
  | cons a xs ih =>
      obtain ⟨hna, hxs⟩ := List.nodup_cons.mp hx
      obtain ⟨ys', hys', hm, hs⟩ :=
        physicalRows_remove_owner w a ys hy
          (hsub a (List.mem_cons.mpr (Or.inl rfl)))
      have hsub' : ∀ b, b ∈ xs → b ∈ ys' := by
        intro b hb
        refine (hm b).mpr ⟨hsub b (List.mem_cons.mpr (Or.inr hb)), ?_⟩
        intro hba
        subst b
        exact hna hb
      obtain ⟨zs, hz, hsum⟩ := ih ys' hxs hys' hsub'
      refine ⟨zs, ?_, ?_⟩
      · intro b hb
        obtain ⟨hyb, hnb⟩ := hz b hb
        obtain ⟨hyb', hba⟩ := (hm b).mp hyb
        exact ⟨hyb', fun hc => hnb ((List.mem_cons.mp hc).resolve_left hba)⟩
      · simp only [List.map_cons, List.sum_cons, hs, hsum, Nat.add_assoc]

private theorem physicalRows_sum_zero {α : Type}
    (w : α → Nat) (xs : List α) (h : ∀ x, x ∈ xs → w x = 0) :
    (xs.map w).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (List.mem_cons.mpr (Or.inl rfl))
      have hs := ih (fun a ha => h a (List.mem_cons.mpr (Or.inr ha)))
      simp only [List.map_cons, List.sum_cons, hx, hs, Nat.zero_add]

private theorem physicalRows_filter_length_le {α : Type}
    (p : α → Bool) (xs : List α) : (xs.filter p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases h : p x <;> simp [List.filter, h] <;> omega

namespace Digraph.GlobalSibling

variable {g : Digraph} {K : Nat}

/-- The physical scatter has exactly one row entry per retained occurrence,
including parallel occurrences. This sum ranges over all original owner IDs. -/
theorem emitAll_total_original_row_lengths (T : Getters g K) :
    (List.ofFn (fun d : Vertex g => ((emitAll T).1.row d).length)).sum =
      (retained T).length := by
  let s := (emitAll T).1
  have hrows : List.ofFn (fun d : Vertex g => s.row d) = s.cells.toList := by
    apply List.ext_getElem
    · simp [s.size_eq]
    · intro i hi hj
      simp [List.getElem_ofFn, EX51.Rows.row]
  calc
    _ = (s.cells.toList.map List.length).sum := by
      rw [← hrows]
      simp only [List.map_ofFn, Function.comp_def]
      rfl
    _ = EX51.Storage.rowMass s := by rw [EX51.Storage.rowMass_eq_cells_sum]
    _ = (retained T).length :=
      EX51.Storage.groupMap_rowMass
        (fun a : Arc g => T.parentOf a.2) (fun a => (locate T a).1) (retained T)

theorem retained_length_le_arcCount (T : Getters g K) :
    (retained T).length ≤ g.arcCount := by
  rw [retained_eq_filter, ← originalArcOccurrences_length_eq_arcCount_forSiblingBudget g]
  exact physicalRows_filter_length_le _ _

/-- Any duplicate-free selection of original owners has total row size at
most `g.arcCount`. The sum is exact if no nonempty row is omitted. -/
theorem emitAll_sum_nodup_row_lengths (T : Getters g K)
    (owners : List (Vertex g)) (hn : owners.Nodup) :
    let total := (owners.map (fun d => ((emitAll T).1.row d).length)).sum
    total ≤ g.arcCount ∧
      ((∀ d : Vertex g, 0 < ((emitAll T).1.row d).length → d ∈ owners) →
        total = (retained T).length) := by
  let w (d : Vertex g) := ((emitAll T).1.row d).length
  let all := List.ofFn (fun d : Vertex g => d)
  have hall : all.Nodup := physicalRows_nodup_ofFn _ (fun _ _ h => h)
  obtain ⟨rest, hrest, hsplit⟩ :=
    physicalRows_split_sum w owners all hn hall
      (fun d _ => physicalRows_mem_ofFn (fun v : Vertex g => v) d)
  have htotal : (all.map w).sum = (retained T).length := by
    simpa only [all, List.map_ofFn, Function.comp_def] using
      emitAll_total_original_row_lengths T
  have hle : (owners.map w).sum ≤ (retained T).length := by omega
  refine ⟨Nat.le_trans hle (retained_length_le_arcCount T), ?_⟩
  intro cover
  have hz : (rest.map w).sum = 0 := by
    apply physicalRows_sum_zero
    intro d hd
    by_cases hp : 0 < w d
    · exact False.elim ((hrest d hd).2 (cover d hp))
    · omega
  change (owners.map w).sum = (retained T).length
  omega

end Digraph.GlobalSibling

end PaperB
