import PaperB.RamConcreteSetup

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PaperB.RamProgram.ThreeCalls.EqualityTail

open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb)

private def wzero {bits : Nat} (hb : 1 < 2 ^ bits) : Word bits :=
  ⟨0, by omega⟩

def wone {bits : Nat} (hb : 1 < 2 ^ bits) : Word bits :=
  ⟨1, hb⟩

def flag {bits : Nat} (hb : 1 < 2 ^ bits) (b : Bool) : Word bits :=
  if b then wone hb else wzero hb

/-- Instruction offsets are relative to PC 60. The two loads use the
original, read-only input array. -/
def tailCell {bits : Nat} (hb : 1 < 2 ^ bits) : Nat → Instr bits 16
  | 0  => .imm 1 (wzero hb)
  | 1  => .branchLt 1 0 62 75
  | 2  => .imm 2 (wone hb)
  | 3  => .sub 3 0 2
  | 4  => .add 3 13 3
  | 5  => .add 4 7 3
  | 6  => .loadInput 5 4
  | 7  => .add 4 9 3
  | 8  => .loadInput 6 4
  | 9  => .branchLt 5 11 75 70
  | 10 => .branchLt 11 5 75 71
  | 11 => .branchLt 6 12 75 72
  | 12 => .branchLt 12 6 75 73
  | 13 => .imm 0 (wone hb)
  | 14 => .halt
  | 15 => .imm 0 (wzero hb)
  | _  => .halt

variable {bits cap : Nat}

private def linkedCell (hcap : cap ≤ 2 ^ bits) (hb : 1 < 2 ^ bits)
    (setup : Setup bits) (p : Fin 77) : Instr bits 16 :=
  if hp : p.val < 60 then
    (program hcap setup)[p.val]'(by
      rw [program_size]
      omega)
  else
    tailCell hb (p.val - 60)

/-- Keep exactly the old instructions at PCs 0–59, replacing the old halt
at PC 60 with the validation tail. The layout is unchanged. -/
def checkedProgram (hcap : cap ≤ 2 ^ bits) (hb : 1 < 2 ^ bits)
    (setup : Setup bits) : Program (layout bits cap hcap) :=
  Array.ofFn (linkedCell hcap hb setup)

variable (hcap : cap ≤ 2 ^ bits) (hb : 1 < 2 ^ bits) (setup : Setup bits)

@[simp] theorem checkedProgram_size : (checkedProgram hcap hb setup).size = 77 := by
  simp only [checkedProgram, Array.size_ofFn]

theorem fetch_prefix {p : Nat} (hp : p < 60) :
    (checkedProgram hcap hb setup)[p]? = (program hcap setup)[p]? := by
  have h77 : p < 77 := by omega
  have hOld : p < (program hcap setup).size := by
    rw [program_size]
    omega
  simp only [checkedProgram, getElem?_def, Array.size_ofFn, h77, hOld,
    dif_pos, Array.getElem_ofFn, linkedCell, Fin.val_mk, hp]

theorem fetch_tail {p : Nat} (hl : 60 ≤ p) (hh : p < 77) :
    (checkedProgram hcap hb setup)[p]? = some (tailCell hb (p - 60)) := by
  have hn : ¬ p < 60 := by omega
  simp only [checkedProgram, getElem?_def, Array.size_ofFn, hh, dif_pos,
    Array.getElem_ofFn, linkedCell, Fin.val_mk, hn, dite_false]

end PaperB.RamProgram.ThreeCalls.EqualityTail
