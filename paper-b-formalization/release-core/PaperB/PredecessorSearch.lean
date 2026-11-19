import PaperB.ExitPaths
import PaperB.PrefixProbe

namespace PaperB.PredecessorSearch

open LabelledQuotient PrefixProbe

/-- Zero is the true sentinel; index `k + 1` tests list entry `k`.
    An out-of-range lookup is false, including at the upper sentinel. -/
def prefixTest {H : LabelledQuotient}
    (ancestors : List (CutPair H)) (passes : CutPair H → Bool) : Nat → Bool
  | 0 => true
  | k + 1 =>
    match ancestors[k]? with
    | some B => passes B
    | none => false

theorem prefixTest_real {H : LabelledQuotient}
    (ancestors : List (CutPair H)) (passes : CutPair H → Bool)
    (k : Nat) (hk : k < ancestors.length) :
    prefixTest ancestors passes (k + 1) = passes ancestors[k] := by
  simp [prefixTest, List.getElem?_eq_getElem hk]

theorem prefixTest_end {H : LabelledQuotient}
    (ancestors : List (CutPair H)) (passes : CutPair H → Bool) :
    prefixTest ancestors passes (ancestors.length + 1) = false := by
  simp [prefixTest]

/-- `isPred` selects the predecessors of the fixed target `y`. -/
theorem prefixTest_mono {H : LabelledQuotient}
    (ancestors : List (CutPair H)) (passes : CutPair H → Bool)
    (isPred : Fin H.vertexCount → Prop)
    (nested : List.Pairwise (fun B P => ∀ v, P.Mem v → H.Lost B v) ancestors)
    (correct : ∀ B, passes B = true ↔ ∀ u, isPred u → H.Lost B u) :
    ∀ a b : Nat, 0 ≤ a → a ≤ b → b ≤ ancestors.length + 1 →
      prefixTest ancestors passes b = true →
      prefixTest ancestors passes a = true := by
  intro a b _ hab _ hbTrue
  cases a with
  | zero => rfl
  | succ a =>
    cases b with
    | zero => omega
    | succ b =>
      by_cases hb : b < ancestors.length
      · have ha : a < ancestors.length := by omega
        by_cases heq : a = b
        · subst a
          exact hbTrue
        · have hlt : a < b := by omega
          have included := (List.pairwise_iff_getElem.mp nested) a b ha hb hlt
          have hPassB : passes ancestors[b] = true :=
            (prefixTest_real ancestors passes b hb).symm.trans hbTrue
          have hPassA : passes ancestors[a] = true :=
            (correct ancestors[a]).2 (fun u hu =>
              lost_of_nested_endpoints included ((correct ancestors[b]).1 hPassB u hu))
          exact (prefixTest_real ancestors passes a ha).trans hPassA
      · have hnone : ancestors.length ≤ b := by omega
        simp [prefixTest, List.getElem?_eq_none hnone] at hbTrue

def run {H : LabelledQuotient}
    (ancestors : List (CutPair H)) (passes : CutPair H → Bool) : Nat × Nat :=
  searchLog (prefixTest ancestors passes) 0 (ancestors.length + 1)

/-- Every real index is `k + 1` for some `k < ancestors.length`. -/
theorem run_spec {H : LabelledQuotient}
    (ancestors : List (CutPair H)) (passes : CutPair H → Bool)
    (isPred : Fin H.vertexCount → Prop)
    (nested : List.Pairwise (fun B P => ∀ v, P.Mem v → H.Lost B v) ancestors)
    (correct : ∀ B, passes B = true ↔ ∀ u, isPred u → H.Lost B u) :
    let cut := (run ancestors passes).1
    cut ≤ ancestors.length ∧
      prefixTest ancestors passes cut = true ∧
      prefixTest ancestors passes (cut + 1) = false ∧
      ∀ (k : Nat) (hk : k < ancestors.length),
        (passes ancestors[k] = true ↔ k + 1 ≤ cut) ∧
        (passes ancestors[k] = false ↔ cut < k + 1) ∧
        ((∀ u, isPred u → H.Lost ancestors[k] u) ↔ k + 1 ≤ cut) := by
  dsimp only [run]
  obtain ⟨_, hlt, hcut, hnext, hclass⟩ :=
    searchLog_spec (prefixTest ancestors passes) 0 (ancestors.length + 1)
      (by omega) rfl (prefixTest_end ancestors passes)
      (prefixTest_mono ancestors passes isPred nested correct)
  refine ⟨by omega, hcut, hnext, ?_⟩
  intro k hk
  have hc := hclass (k + 1) (by omega) (by omega)
  rw [prefixTest_real ancestors passes k hk] at hc
  exact ⟨hc.1, hc.2, (correct ancestors[k]).symm.trans hc.1⟩

/-- This bounds probes only, not the cost of list lookup or evaluating `passes`. -/
theorem run_count_le {H : LabelledQuotient}
    (ancestors : List (CutPair H)) (passes : CutPair H → Bool) :
    (run ancestors passes).2 ≤ Nat.log2 (ancestors.length + 1) + 1 := by
  simpa only [run, Nat.sub_zero] using
    (searchLog_count_le (prefixTest ancestors passes) 0 (ancestors.length + 1))

end PaperB.PredecessorSearch
