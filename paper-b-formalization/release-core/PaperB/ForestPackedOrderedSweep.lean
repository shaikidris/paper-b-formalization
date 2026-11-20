import PaperB.ForestActualFull
import PaperB.ForestFixedBankSortExact

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.ForestDictionary

open PaperB.LabelledQuotient PaperB.ForestHead
open PaperB.PairLookup PaperB.PairLookup.KeyMerge PaperB.PairDictionary.FixedBank

private def initialBanks (xs : List Key) : Array Key :=
  let bank0 := xs.toArray
  bank0 ++ Array.replicate bank0.size (0, 0)

private theorem initialBanks_size (xs : List Key) :
    (initialBanks xs).size = 2 * xs.length := by
  simp [initialBanks] <;> omega

private theorem initialKeys (xs : List Key) :
    keysAt (initialBanks xs) (initialBanks_size xs) false 0 xs.length (by simp) =
      xs := by
  apply List.ext_getElem
  · simp [keysAt]
  · intro i hi hj
    have hsize := initialBanks_size xs
    simp only [keysAt, List.getElem_ofFn]
    change (initialBanks xs)[0 + (0 + i)]'(by omega) = xs[i]
    simp only [Nat.zero_add, initialBanks]
    rw [Array.getElem_append_left] <;> simp [*]

private theorem extractKeys {k : Nat} (a : Array Key) (ha : a.size = 2 * k)
    (n : Nat) (hn : n ≤ k) :
    (a.extract 0 n).toList = keysAt a ha false 0 n (by simpa using hn) := by
  have hs : (a.extract 0 n).size = n := by
    simp only [Array.size_extract, Nat.sub_zero]
    omega
  apply List.ext_getElem
  · simp only [keysAt, List.length_ofFn, Array.length_toList, hs]
  · intro i hi hj
    have hin : i < n := by simpa only [Array.length_toList, hs] using hi
    simp only [Array.getElem_toList, Array.getElem_extract, keysAt, List.getElem_ofFn]
    change _ = a[0 + (0 + i)]'(by omega)
    simp

private def packedKeys (xs : List Key) : Array Key :=
  let out := runPacked xs.length false (initialBanks xs) (initialBanks_size xs)
  out.bank.extract 0 out.count

private theorem packedKeys_spec (xs : List Key) :
    Increasing (packedKeys xs).toList ∧
      ∀ z : Key, z ∈ (packedKeys xs).toList ↔ z ∈ xs := by
  let out := runPacked xs.length false (initialBanks xs) (initialBanks_size xs)
  have he : (packedKeys xs).toList = out.keys :=
    extractKeys out.bank out.size_eq out.count out.count_le
  have h := runPacked_spec xs.length false (initialBanks xs) (initialBanks_size xs)
  rw [he]
  exact ⟨h.1, fun z => (h.2 z).trans (by rw [initialKeys xs])⟩

private theorem key_irrefl (x : Key) : ¬ lexLess x x := by
  rcases x with ⟨a, b⟩
  change ¬ (a < a ∨ (a = a ∧ b < b))
  omega

-- Equal support forces equal heads, then equal tail support.
private theorem increasing_unique {xs ys : List Key}
    (hx : Increasing xs) (hy : Increasing ys)
    (hm : ∀ k : Key, k ∈ xs ↔ k ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have h := (hm y).mpr (List.mem_cons.mpr (Or.inl rfl))
      simp at h
  | cons x xs ih =>
    cases ys with
    | nil =>
      have h := (hm x).mp (List.mem_cons.mpr (Or.inl rfl))
      simp at h
    | cons y ys =>
      have he : x = y := by
        by_cases h : x = y
        · exact h
        · have hxy := (hm x).mp (List.mem_cons.mpr (Or.inl rfl))
          have hyx := (hm y).mpr (List.mem_cons.mpr (Or.inl rfl))
          have hxr := (List.mem_cons.mp hxy).resolve_left h
          have hyr := (List.mem_cons.mp hyx).resolve_left (fun e => h e.symm)
          exact False.elim (key_irrefl x
            (lexLess_trans (hx.head y hyr) (hy.head x hxr)))
      subst y
      apply congrArg (List.cons x)
      apply ih hx.tail hy.tail
      intro k
      by_cases hk : k = x
      · subst k
        have hnx : x ∉ xs := fun h => key_irrefl x (hx.head x h)
        have hny : x ∉ ys := fun h => key_irrefl x (hy.head x h)
        simp [hnx, hny]
      · simpa only [List.mem_cons, hk, false_or] using hm k

private theorem packedKeys_eq (xs : List Key) :
    packedKeys xs = KeyMerge.dictionary xs := by
  have hp := packedKeys_spec xs
  have hr := KeyMerge.build_spec xs
  have he := increasing_unique hp.1 hr.increasing
    (fun k => (hp.2 k).trans (hr.mem_iff k).symm)
  simpa [KeyMerge.dictionary] using congrArg (fun l : List Key => l.toArray) he

/-- Collect once, sort in the two banks, and extract the occupied output prefix. -/
def packedDictionary {H : LabelledQuotient} (p : Rows H)
    (code : CutPair H → Key) : Array Key :=
  packedKeys (collect p code)

theorem packedDictionary_eq {H : LabelledQuotient} (p : Rows H)
    (code : CutPair H → Key) :
    packedDictionary p code = dictionary p code :=
  packedKeys_eq (collect p code)

theorem packedDictionary_spec {H : LabelledQuotient} (p : Rows H)
    (code : CutPair H → Key) :
    StrictSorted (packedDictionary p code) ∧
      (∀ k : Key, k ∈ (packedDictionary p code).toList ↔
        ∃ (y : Vertex H) (q : CutPair H),
          preparedKey H (p.row y) = some q ∧ code q = k) ∧
      (packedDictionary p code).size ≤ H.vertexCount := by
  rw [packedDictionary_eq]
  exact dictionary_spec p code

end PaperB.ForestDictionary

namespace EX24.PreparedSweep

open PaperB EX24.PreStep PaperB.LabelledQuotient PaperB.ForestHead PaperB.Jumps
open PaperB.PairLookup

private def orderedWith {H : LabelledQuotient} (large : 3 ≤ H.vertexCount)
    (d : Array Key) (hd : StrictSorted d) : Config H :=
  let base : Config H :=
    { region := ConcreteInit.region H.vertexCount
      dict := d
      sorted := hd
      code := orderedPairCode
      code_inj := by
        intro a b h
        rcases a with ⟨a₁, a₂, _, _, _⟩
        rcases b with ⟨b₁, b₂, _, _, _⟩
        have h₁ : a₁ = b₁ := Fin.ext (congrArg Prod.fst h)
        have h₂ : a₂ = b₂ := Fin.ext (congrArg Prod.snd h)
        subst b₁
        subst b₂
        rfl
      vertexIndex := Fin.val
      vertexIndex_inj := fun h => Fin.ext h
      zeroKey := SmallQuotient.sentinelDefaultCutPair H large
      atDepth := fun _ _ _ _ => 0
      ancestor := fun _ _ _ _ => false }
  base.usePackedWords

private theorem orderedWith_congr {H : LabelledQuotient}
    (large : 3 ≤ H.vertexCount) {d e : Array Key}
    (hd : StrictSorted d) (he : StrictSorted e) (h : d = e) :
    orderedWith large d hd = orderedWith large e he := by
  cases h
  rfl

def packedOrderedConfig {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (large : 3 ≤ H.vertexCount) : Config H :=
  orderedWith large (ForestDictionary.packedDictionary p orderedPairCode)
    (ForestDictionary.packedDictionary_spec p orderedPairCode).1

theorem packedOrderedConfig_eq {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (large : 3 ≤ H.vertexCount) :
    packedOrderedConfig p large = orderedConfig p large :=
  orderedWith_congr large
    (ForestDictionary.packedDictionary_spec p orderedPairCode).1
    (ForestDictionary.dictionary_spec p orderedPairCode).1
    (ForestDictionary.packedDictionary_eq p orderedPairCode)

def runOrderedPacked {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat) (large : 3 ≤ H.vertexCount) :
    Option (State H × Log H) :=
  fromRoot (packedOrderedConfig p large) rank
    (ConcreteInit.initImage H.vertexCount).1 H.vertexCount
    (orderedRows p data size_data)

theorem runOrderedPacked_eq {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat) (large : 3 ≤ H.vertexCount) :
    runOrderedPacked p data size_data rank large = runOrdered p data size_data rank large := by
  simp only [runOrderedPacked, runOrdered, packedOrderedConfig_eq]

end EX24.PreparedSweep
