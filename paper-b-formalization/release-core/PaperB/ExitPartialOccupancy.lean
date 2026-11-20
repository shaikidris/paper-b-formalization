import PaperB.ExitPriorBase

namespace PaperB.ExitMap.JumpMapRoute.StoredExit

open PaperB.Machine (Word)
open PaperB.StoredPacking
open PaperB.ExitMap.Retention
open CheckedFold
open PriorBase (run accumulated)
open PaperB.BuiltExit (zero)

/-- A partially filled arena. Live indices are logical forest slots;
no depth or record invariant is imposed on dead slots or spare capacity. -/
structure PartialOccupied {bits endpoints : Nat} (mem : Array (Word bits))
    (R : Region bits mem.size) (F : JumpForest) (ref : Nat → CheckedFold.Stored)
    (w : Width bits (max R.slots endpoints)) (live : Nat → Prop) : Prop where
  size_le : F.size ≤ R.slots
  valid : ValidJumpForest F
  live_lt_size : ∀ u, live u → u < F.size
  depth : ∀ v : Fin R.slots, live v.val →
    (mem[(R.depthAddr v).val]'(R.depthMem v)).val = F.depthOf v.val
  parent_eq : ∀ u, live u → (ref u).parent = F.parentOf u
  jump_eq : ∀ u, live u → (ref u).jump = F.jumpOf u
  parent_live : ∀ u, live u → live (F.parentOf u)
  jump_live : ∀ u, live u → live (F.jumpOf u)
  maps : ∀ v : Fin R.slots, live v.val →
    MapBound endpoints (ref v.val).parentMap ∧ MapBound endpoints (ref v.val).jumpMap
  packed : ∀ (v : Fin R.slots), live v.val →
    ∀ (hr : (storedCodec w.tags).valid (ref v.val)) (i : Fin 18),
      mem[R.base.val + 18 * v.val + i.val]'(by
        have hm := R.recordMem v
        have hi := i.isLt
        omega) = (storedCodec w.tags).encode (ref v.val) hr i

section Exact

variable {bits endpoints : Nat} {mem : Array (Word bits)}
  {R : Region bits mem.size} {F : JumpForest} {ref : Nat → CheckedFold.Stored}
  {w : Width bits (max R.slots endpoints)} {live : Nat → Prop}

theorem depth_exact_live (ok : PartialOccupied mem R F ref w live) {u : Nat}
    (hu : live u) : depthAt mem R u = F.depthOf u := by
  have h : u < R.slots := Nat.lt_of_lt_of_le (ok.live_lt_size u hu) ok.size_le
  simpa only [depthAt, dif_pos h] using ok.depth ⟨u, h⟩ hu

theorem record_exact_live (ok : PartialOccupied mem R F ref w live) {u : Nat}
    (hu : live u) : recordAt mem R w.tags u = ref u := by
  have hF := ok.live_lt_size u hu
  have h : u < R.slots := Nat.lt_of_lt_of_le hF ok.size_le
  let v : Fin R.slots := ⟨u, h⟩
  have hp : (ref u).parent < R.slots := by
    rw [ok.parent_eq u hu]
    exact Nat.lt_of_lt_of_le (ok.valid.parentOf_lt_size hF) ok.size_le
  have hj : (ref u).jump < R.slots := by
    rw [ok.jump_eq u hu]
    exact Nat.lt_of_lt_of_le (ok.valid.jumpOf_lt_size hF) ok.size_le
  have hm := ok.maps v hu
  have hr := stored_fits w (ref u) hp hj hm.1 hm.2
  rw [recordAt, dif_pos h]
  exact readStoredAt_exact w.tags mem R.base u (R.recordAddr v)
    (R.recordMem v) (ref u) hr (ok.packed v hu hr)

private theorem aux_exact_live (ok : PartialOccupied mem R F ref w live)
    (d budget : Nat) {u : Nat} {acc : Map} {steps : Nat} (hu : live u) :
    foldFusedAux (depthAt mem R) (recordAt mem R w.tags) d budget u acc steps =
      foldFusedAux F.depthOf ref d budget u acc steps := by
  conv => lhs; rw [foldFusedAux]
  conv => rhs; rw [foldFusedAux]
  rw [depth_exact_live ok hu]
  by_cases h : steps < budget ∧ d < F.depthOf u
  · have hj : live (ref u).jump := by
      rw [ok.jump_eq u hu]
      exact ok.jump_live u hu
    have hp : live (ref u).parent := by
      rw [ok.parent_eq u hu]
      exact ok.parent_live u hu
    have he : selectAtDepth (depthAt mem R) d (recordAt mem R w.tags u) =
        selectAtDepth F.depthOf d (ref u) := by
      rw [record_exact_live ok hu]
      simp only [selectAtDepth, depth_exact_live ok hj]
    have hv : live (selectAtDepth F.depthOf d (ref u)).dst := by
      by_cases ht : d ≤ F.depthOf (ref u).jump
      · simpa [selectAtDepth, CheckedFold.Stored.select, ht] using hj
      · simpa [selectAtDepth, CheckedFold.Stored.select, ht] using hp
    simp only [dif_pos h, he]
    exact aux_exact_live ok d budget hv
  · simp only [dif_neg h]
termination_by budget - steps
decreasing_by
  have hb := h.1
  omega

theorem foldStored_exact_live (ok : PartialOccupied mem R F ref w live)
    {u : Nat} (hu : live u) (d : Nat) :
    foldStored mem R w.tags u d = foldFused F ref u d := by
  change foldFusedAux (depthAt mem R) (recordAt mem R w.tags) d
      (depthAt mem R u - d) u Map.identity 0 =
    foldFusedAux F.depthOf ref d (F.depthOf u - d) u Map.identity 0
  rw [depth_exact_live ok hu]
  exact aux_exact_live ok d (F.depthOf u - d) hu

theorem foldStored_steps_le_live (ok : PartialOccupied mem R F ref w live)
    (route : StoreOK F ref) {u n : Nat}
    (hu : live u) (hn : F.numInserted ≤ n) (d : Nat) :
    (foldStored mem R w.tags u d).steps ≤ 3 * ceilLog2 (n + 2) := by
  rw [foldStored_exact_live ok hu d]
  exact foldFused_steps_le route ok.valid (ok.live_lt_size u hu) hn d

/-- The packed callback uses the same accumulated map and the single
prior-base cell selected by the caller. -/
theorem run_exact_fold_live (ok : PartialOccupied mem R F ref w live)
    {u : Nat} (hu : live u) (d : Nat)
    (prior : Array (Option Values)) (v : Fin prior.size) :
    run mem R w.tags prior v u d =
      Map.eval (accumulated (foldFused F ref u d))
        ((prior[v.val]'(v.isLt)).getD zero) := by
  simp only [run, foldStored_exact_live ok hu d]

theorem run_exact_base_live (ok : PartialOccupied mem R F ref w live)
    {u : Nat} (hu : live u) (d : Nat)
    (prior : Array (Option Values)) (v : Fin prior.size) (seed : Values)
    (hbase : prior[v.val]'(v.isLt) = some seed) :
    run mem R w.tags prior v u d =
      Map.eval (accumulated (foldFused F ref u d)) seed := by
  simp only [run_exact_fold_live ok hu d prior v, hbase, Option.getD]

/-- The initial depth lookup and the single prior-base cell are charged
separately from the packed worker. -/
theorem run_read_charge_live (ok : PartialOccupied mem R F ref w live)
    (route : StoreOK F ref) {u n : Nat}
    (hu : live u) (hn : F.numInserted ≤ n) (d : Nat) :
    ∃ c, WordCharge (depthAt mem R) (recordAt mem R w.tags) d
        (depthAt mem R u - d) u 0 c ∧
      1 + c ≤ 20 * (foldStored mem R w.tags u d).steps + 2 ∧
      1 + c + 1 ≤ 60 * ceilLog2 (n + 2) + 3 := by
  obtain ⟨c, hc, hwords⟩ := foldStored_wordReads mem R w.tags u d
  have hsteps := foldStored_steps_le_live ok route hu hn d
  exact ⟨c, hc, hwords, by omega⟩

end Exact

end PaperB.ExitMap.JumpMapRoute.StoredExit
