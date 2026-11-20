import PaperB.RamPushChildRow

#print axioms PaperB.RamPushChildRow.push_row_steps
#print axioms PaperB.RamPushChildRow.encode_children_stack

section
open PaperB.RamProgram
open PaperB.RamPushChildRow
private abbrev L : Layout 4 := ⟨8, 0, 9, by decide, by decide⟩
private def inp : Input L := ⟨#[], rfl⟩
private def regs : Registers 8 := ⟨id, fun _ _ h => h⟩
private def prog : Program L := (codeBlock regs 0 ++ [Instr.halt]).toArray
private def state : State L :=
  ⟨#[1, 4, 3, 0, 0, 1, 0, 0], #[1, 2, 3, 7, 9, 14, 13, 12, 11], 0, rfl, rfl⟩

example : (run prog inp 26 state).map (fun r =>
    (r.executed, (reg r.finalState 0).val, (reg r.finalState 2).val,
      r.finalState.data)) = some (26, 4, 0, #[1, 2, 3, 7, 9, 3, 2, 1, 11]) := by decide

end
