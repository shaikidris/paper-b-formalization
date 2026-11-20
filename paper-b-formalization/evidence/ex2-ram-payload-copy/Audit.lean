import PaperB.RamSliceCopy

#print axioms SliceCopy.Prefix.advance
#print axioms PaperB.RamProgram.step_add_at
#print axioms PaperB.RamProgram.indexedDataRead_steps
#print axioms PaperB.RamSliceCopy.copy_steps
#print axioms PaperB.RamSliceCopy.standalone_exact
#print axioms PaperB.RetainedProperLoss.WordColumns.seal_payload_run
#print axioms PaperB.ForestPreparedBuild.buildWordsFromOrder_seal_budget

section
open PaperB.RamProgram
open PaperB.RamSliceCopy

private abbrev L := layout 4 0 4 (by decide) (by decide)
private def input : Input L := ⟨#[], rfl⟩
private def state (count : Fin 16) : State L :=
  ⟨#[0, count, 0, 2, 1, 0, 0], #[5, 9, 10, 11], 0, rfl, rfl⟩

example : ((run (standalone 4 0 4 (by decide) (by decide)) input 16
      (state 2)).map fun r => (r.finalState.data, r.executed)) =
      some (#[5, 9, 5, 9], 16) := by decide

example : run (standalone 4 0 4 (by decide) (by decide)) input 15 (state 2) =
      none := by rfl

example : ((run (standalone 4 0 4 (by decide) (by decide)) input 2
      (state 0)).map fun r => (r.finalState.data, r.executed)) =
      some (#[5, 9, 10, 11], 2) := by decide

end
