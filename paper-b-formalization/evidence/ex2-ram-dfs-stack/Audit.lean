import PaperB.RamForestStack

#print axioms PaperB.RamProgram.step_sub_at
#print axioms PaperB.RamForestStack.push_steps
#print axioms PaperB.RamForestStack.pop_steps
#print axioms PaperB.RamForestStack.enter_steps
#print axioms PaperB.RamForestStack.commandWord_exit_node
#print axioms PaperB.RamForestStack.Finish.stack_word_fits
#print axioms PaperB.RamForestStack.Finish.stackFits
#print axioms PaperB.RamForestStack.Finish.exact_stackOperations

section
open PaperB.RamProgram
open PaperB.RamForestStack

private abbrev L : Layout 4 := ⟨5, 0, 4, by decide, by decide⟩
private def input : Input L := ⟨#[], rfl⟩
private def state : State L := ⟨#[0, 1, 9, 1, 0], #[2, 3, 4, 5], 0, rfl, rfl⟩
private def program : Program L :=
  (pushCode 0 1 2 3 4 ++ popCode 0 1 2 3 ++ [Instr.halt]).toArray

example : (run program input 7 state).map (fun r =>
    (r.executed, (reg r.finalState 0).val, (reg r.finalState 2).val,
      r.finalState.data)) = some (7, 0, 9, #[2, 9, 4, 5]) := by decide

end
