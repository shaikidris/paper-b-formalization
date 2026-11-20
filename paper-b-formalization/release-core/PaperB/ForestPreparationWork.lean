import PaperB.ForestInputPrepStorage

-- Append at file scope after the preparation declarations.
namespace PaperB.PreparationWorkChecks

set_option maxHeartbeats 100000

private theorem supplied_length (H : LabelledQuotient) :
    (ForestIncomingRaw.supplied H).length = H.arcCount := by
  rw [ForestIncomingRaw.length_supplied,
    ForestPreparedBuild.arcTotal_eq_arcCount]

private theorem emitted_length (H : LabelledQuotient) :
    ForestIncomingPrep.mapCalls H (ForestIncomingRaw.prepare H) =
      H.arcCount := by
  rw [ForestIncomingPrep.mapCalls_prepare, supplied_length]

private theorem prepare_work (H : LabelledQuotient) :
    (ForestIncomingRaw.prepare H).2 =
      ⟨H.vertexCount, H.arcCount, H.arcCount, H.arcCount, H.vertexCount⟩ := by
  unfold ForestIncomingRaw.prepare
  rw [EX51.groupMap_work, supplied_length]

private theorem epoch_visits (H : LabelledQuotient)
    (cover : ForestIncomingPrep.Cover H) :
    (ForestIncomingPrep.build H cover).visits = H.arcCount := by
  rw [ForestIncomingPrep.visits_supplied, supplied_length]

-- One unit per requested fill slot, enumerated head, fold step,
-- row read, row write, and element mapped. This is a charge, not a counter.
private def sourceCharge (H : LabelledQuotient)
    (p : ForestIncomingRaw.Prepared H) : Nat :=
  let heads := (List.finRange H.vertexCount).length
  H.vertexCount + heads + heads + heads + heads +
    ForestIncomingPrep.mapCalls H p

private theorem source_charge_prepare (H : LabelledQuotient) :
    sourceCharge H (ForestIncomingRaw.prepare H) =
      5 * H.vertexCount + H.arcCount := by
  simp only [sourceCharge, List.length_finRange, emitted_length] <;> omega

private def groupCharge : EX51.Work → Nat
  | ⟨init, scatterRead, scatterWrite, reverse, finish⟩ =>
    init + scatterRead + scatterWrite + reverse + finish

-- Supply charges head enumeration, the outer fold, and the arc scans.
-- Grouping and epoch visits use the counters returned by the actual routines.
theorem preparation_charge_bound (H : LabelledQuotient)
    (cover : ForestIncomingPrep.Cover H) :
    let heads := (List.finRange H.vertexCount).length
    heads + heads + ForestIncomingRaw.arcTotal H +
      groupCharge (ForestIncomingRaw.prepare H).2 +
      sourceCharge H (ForestIncomingRaw.prepare H) +
      (ForestIncomingPrep.build H cover).visits ≤
        9 * (H.vertexCount + H.arcCount) := by
  dsimp only
  rw [ForestPreparedBuild.arcTotal_eq_arcCount, prepare_work,
    source_charge_prepare, epoch_visits]
  simp only [List.length_finRange, groupCharge] <;> omega

end PaperB.PreparationWorkChecks
