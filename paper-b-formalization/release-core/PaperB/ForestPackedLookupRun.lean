import PaperB.ForestPackedAfterHit
import PaperB.RamPairHitRow

namespace PaperB.RetainedProperLoss

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.ForestSlimIndex
open PaperB.Machine (Word)
open PaperB.WordOps (zero)
open PaperB.RamProgram
open _root_.EX24.PreparedSweep

private def startPair {bits cap : Nat} (fit : cap ≤ 2 ^ bits)
    (a size b x y : Word bits) : RamProgram.State (ThreeCalls.layout bits cap fit) where
  regs := Array.ofFn fun i : Fin 16 =>
    if i = 7 then a else if i = 8 then size else if i = 9 then b
    else if i = 11 then x else if i = 12 then y else zero bits
  data := #[]
  pc := 0
  regs_size := by simp
  data_size := rfl

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : OrderedReaderResult p data size_data rank large)

/-- The existing fixed search program runs on the dictionary of the actual
word image. The remaining constant-size calculation reads its other banks. -/
theorem packed_dictionary_run {bits : Nat}
    (cap : 1 + 18 * H.vertexCount < 2 ^ bits) (q : CutPair H) (v : Nat) :
    let w := packWordColumns r cap
    let rep := packWordColumns_dictionary_represents r cap
    let fit := Nat.le_of_lt rep.valid.capacity
    have one : 1 < 2 ^ bits := by omega
    let A := FlatPairDictionary.firstSlice w.dictionary rep.valid
    let B := FlatPairDictionary.secondSlice w.dictionary rep.valid
    let x : Word bits := ⟨q.fst.val, by have := q.fst.isLt; omega⟩
    let y : Word bits := ⟨q.snd.val, by have := q.snd.isLt; omega⟩
    let state := startPair fit A.base ⟨A.len, by have h := A.fits; omega⟩ B.base x y
    let input :
        RamProgram.Input (ThreeCalls.layout bits w.dictionary.size fit) :=
      ⟨w.dictionary, rfl⟩
    let fuel := 33 * OracleContract.L H.vertexCount + 39
    ∃ out,
      run (ThreeCalls.EqualityTail.checkedProgram fit one (ThreeCalls.concreteSetup bits one))
          input fuel state = some out ∧
      out.executed ≤ fuel ∧
      (let hit := if ThreeCalls.setupReg out.finalState 0 = (⟨1, one⟩ : Word bits)
                  then some (ThreeCalls.setupReg out.finalState 3).val else none
       w.afterHit rep.valid hit (encodeBackPair (some q)) v = (ofOrderedReader r).contains q v) := by
  intro w rep fit one A B x y state input fuel
  let narrow :
      RamProgram.Input (Predecessor.layout bits w.dictionary.size fit) :=
    ⟨w.dictionary, rfl⟩
  let c := FlatPairDictionary.workerColumns narrow.words rep
  have regs (i : Fin 16) :
      ThreeCalls.setupReg state i =
        if i = 7 then A.base else if i = 8 then (⟨A.len, by have h := A.fits; omega⟩ : Word bits)
        else if i = 9 then B.base else if i = 11 then x else if i = 12 then y else zero bits := by
    unfold ThreeCalls.setupReg state startPair
    simp only [Array.getElem_ofFn]
  obtain ⟨out, hrun, _, _, hhit⟩ :=
    ThreeCalls.pair_search_correct_from_pc0_with_index (i := narrow) (j := input) fit one c
      (dict_sorted r) x y rfl state rfl
      (by rw [regs]; rfl) (by rw [regs]; rfl) (by rw [regs]; rfl)
      (by rw [regs]; rfl) (by rw [regs]; rfl)
      (by rw [regs]; rfl) (by rw [regs]; rfl)
  have hsize := ofOrderedReader_dict_size_le r
  have hlog : Nat.log2 ((ofOrderedReader r).dict.size + 1) ≤
      Nat.log2 (H.vertexCount + 1) := by
    apply (Nat.le_log2 (by omega : H.vertexCount + 1 ≠ 0)).mpr
    exact Nat.le_trans (Nat.log2_self_le (by omega)) (Nat.add_le_add_right hsize 1)
  have wider :
      33 * (Nat.log2 ((ofOrderedReader r).dict.size + 1) + 1) + 39 ≤ fuel := by
    dsimp only [fuel, OracleContract.L]
    omega
  have hrun' := run_stable_of_le wider hrun
  refine ⟨out, hrun', run_executed_le hrun', ?_⟩
  dsimp only at hhit ⊢
  rw [show (if ThreeCalls.setupReg out.finalState 0 = (⟨1, one⟩ : Word bits)
      then some (ThreeCalls.setupReg out.finalState 3).val else none) =
      (PairLookup.lookup (ofOrderedReader r).dict (x.val, y.val)).1 by
      simpa only [decide_eq_true_eq] using hhit]
  exact packWordColumns_afterHit r cap q v

end PaperB.RetainedProperLoss
