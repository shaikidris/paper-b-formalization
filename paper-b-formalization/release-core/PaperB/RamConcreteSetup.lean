import PaperB.RamThreeCalls

set_option autoImplicit false

namespace PaperB.RamProgram.ThreeCalls

open PaperB.Machine (Word)
open PaperB.WordOps (zero sub ltb)

def setupOne (bits : Nat) (hone : 1 < 2 ^ bits) : Word bits :=
  ⟨1, hone⟩

/-- At PC 4, unsigned `x < 1` is exactly the saved `x = 0` case. -/
def firstSetup (bits : Nat) (hone : 1 < 2 ^ bits) :
    Vector (Instr bits 16) 8 :=
  #v[.imm 0 (zero bits),
     .mov 1 8,
     .mov 2 7,
     .imm 6 (setupOne bits hone),
     .branchLt 11 6 20 5,
     .mov 3 11,
     .sub 3 3 6,
     .goto 8]

def secondSetup (bits : Nat) (hone : 1 < 2 ^ bits) :
    Vector (Instr bits 16) 8 :=
  #v[.mov 13 0,
     .imm 0 (zero bits),
     .mov 1 8,
     .mov 2 7,
     .mov 3 11,
     .imm 6 (setupOne bits hone),
     .goto 27,
     .goto 28]

def thirdSetup (bits : Nat) (hone : 1 < 2 ^ bits) :
    Vector (Instr bits 16) 8 :=
  #v[.mov 14 0,
     .add 2 9 13,
     .sub 1 14 13,
     .mov 3 12,
     .imm 0 (zero bits),
     .imm 6 (setupOne bits hone),
     .goto 47,
     .goto 48]

def concreteSetup (bits : Nat) (hone : 1 < 2 ^ bits) : Setup bits :=
  #v[firstSetup bits hone, secondSetup bits hone, thirdSetup bits hone]

def setupReg {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (s : State (layout bits cap hcap)) (r : Fin 16) : Word bits :=
  s.regs[r.val]'(by simpa only [s.regs_size] using r.isLt)

/-- The exact state change of a setup register write, including the PC. -/
def setupWriteNext {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (s : State (layout bits cap hcap)) (r : Fin 16) (w : Word bits) :
    State (layout bits cap hcap) :=
  { s with
    regs := s.regs.set r.val w (by simpa only [s.regs_size] using r.isLt)
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

section
variable {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
variable {s : State (layout bits cap hcap)}
variable {code : Program (layout bits cap hcap)}
variable {input : Input (layout bits cap hcap)}

private theorem setupReg_write_same (r : Fin 16) (w : Word bits) :
    setupReg (setupWriteNext s r w) r = w := by
  simp [setupReg, setupWriteNext, Array.getElem_set]

private theorem setupReg_write_ne {r q : Fin 16} (hne : r.val ≠ q.val)
    (w : Word bits) :
    setupReg (setupWriteNext s r w) q = setupReg s q := by
  simp [setupReg, setupWriteNext, Array.getElem_set, hne, Ne.symm hne]

private theorem setup_imm_at {d : Fin 16} {w : Word bits}
    (hf : code[s.pc]? = some (.imm d w)) (ht : s.pc + 1 < code.size) :
    step code input s = some (.next (setupWriteNext s d w)) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
      some (Transition.next (setupWriteNext s d w)) else none) = _
  rw [if_pos ht]

private theorem setup_mov_at {d a : Fin 16}
    (hf : code[s.pc]? = some (.mov d a)) (ht : s.pc + 1 < code.size) :
    step code input s = some (.next (setupWriteNext s d (setupReg s a))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
      some (Transition.next (setupWriteNext s d (setupReg s a))) else none) = _
  rw [if_pos ht]

private theorem setup_sub_at {d a b : Fin 16}
    (hf : code[s.pc]? = some (.sub d a b)) (ht : s.pc + 1 < code.size) :
    step code input s =
      some (.next (setupWriteNext s d (sub (setupReg s a) (setupReg s b)))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
      some (Transition.next (setupWriteNext s d (sub (setupReg s a) (setupReg s b))))
      else none) = _
  rw [if_pos ht]

end

/-- On the nonzero branch, the word subtraction computes the natural predecessor. -/
theorem setup_sub_one_val {bits : Nat} (hone : 1 < 2 ^ bits)
    (x : Word bits) (hx : x.val ≠ 0) :
    (sub x (setupOne bits hone)).val = x.val - 1 := by
  have hxlt := x.isLt
  have hlt : x.val - 1 < 2 ^ bits := by omega
  have he : 2 ^ bits + x.val - 1 = (x.val - 1) + 2 ^ bits := by omega
  change (2 ^ bits + x.val - 1) % (2 ^ bits) = x.val - 1
  rw [he, Nat.add_mod]
  simp only [Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hlt]

/-- Exactly five steps to PC 20 when saved `x` is zero, leaving r3 untouched;
otherwise exactly eight steps to PC 8 with r3 set to `x - 1`.
The state expressions specify all register writes and leave data unchanged. -/
theorem run_first_setup {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    (hone : 1 < 2 ^ bits) (input : Input (layout bits cap hcap))
    (s : State (layout bits cap hcap)) (hpc : s.pc = 0) :
    let code := program hcap (concreteSetup bits hone)
    let one := setupOne bits hone
    let x := setupReg s 11
    let s1 := setupWriteNext s 0 (zero bits)
    let s2 := setupWriteNext s1 1 (setupReg s 8)
    let s3 := setupWriteNext s2 2 (setupReg s 7)
    let s4 := setupWriteNext s3 6 one
    let s5 := { s4 with pc := 5 }
    let s6 := setupWriteNext s5 3 x
    let s7 := setupWriteNext s6 3 (sub x one)
    if x.val = 0 then
      Steps code input 5 s { s4 with pc := 20 }
    else
      Steps code input 8 s { s7 with pc := 8 } := by
  intro code one x s1 s2 s3 s4 s5 s6 s7
  have hsize : code.size = 61 := program_size hcap (concreteSetup bits hone)
  have hp1 : s1.pc = 1 := by
    change s.pc + 1 = 1
    rw [hpc]
  have hp2 : s2.pc = 2 := by
    change s1.pc + 1 = 2
    rw [hp1]
  have hp3 : s3.pc = 3 := by
    change s2.pc + 1 = 3
    rw [hp2]
  have hp4 : s4.pc = 4 := by
    change s3.pc + 1 = 4
    rw [hp3]
  have hp5 : s5.pc = 5 := rfl
  have hp6 : s6.pc = 6 := rfl
  have hp7 : s7.pc = 7 := rfl

  have f0 : code[s.pc]? = some (.imm 0 (zero bits)) := by
    rw [hpc] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (0 : Fin 8)
  have f1 : code[s1.pc]? = some (.mov 1 8) := by
    rw [hp1] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (1 : Fin 8)
  have f2 : code[s2.pc]? = some (.mov 2 7) := by
    rw [hp2] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (2 : Fin 8)
  have f3 : code[s3.pc]? = some (.imm 6 one) := by
    rw [hp3] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (3 : Fin 8)
  have f4 : code[s4.pc]? = some (.branchLt 11 6 20 5) := by
    rw [hp4] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (4 : Fin 8)

  have hr8 : setupReg s1 8 = setupReg s 8 := by
    simp (disch := decide) only [s1, setupReg_write_ne]
  have hr7 : setupReg s2 7 = setupReg s 7 := by
    simp (disch := decide) only [s2, s1, setupReg_write_ne]
  have hx4 : setupReg s4 11 = x := by
    simp (disch := decide) only [s4, s3, s2, s1, x, setupReg_write_ne]
  have ho4 : setupReg s4 6 = one := by
    simp only [s4, setupReg_write_same]

  have e0 : step code input s = some (.next s1) :=
    setup_imm_at (s := s) (input := input) f0 (by rw [hpc, hsize] <;> decide)
  have e1 : step code input s1 = some (.next s2) := by
    simpa only [hr8] using
      (setup_mov_at (s := s1) (input := input) f1 (by rw [hp1, hsize] <;> decide))
  have e2 : step code input s2 = some (.next s3) := by
    simpa only [hr7] using
      (setup_mov_at (s := s2) (input := input) f2 (by rw [hp2, hsize] <;> decide))
  have e3 : step code input s3 = some (.next s4) :=
    setup_imm_at (s := s3) (input := input) f3 (by rw [hp3, hsize] <;> decide)

  have hcmp : ltb (setupReg s4 11) (setupReg s4 6) = decide (x.val = 0) := by
    rw [hx4, ho4]
    change decide (x.val < 1) = decide (x.val = 0)
    by_cases hz : x.val = 0
    · have hl : x.val < 1 := by omega
      simp [hz, hl]
    · have hl : ¬ x.val < 1 := by omega
      simp [hz, hl]
  have hb :
      (if ltb (setupReg s4 11) (setupReg s4 6) then 20 else 5) < code.size := by
    rw [hsize]
    split <;> decide
  have e4 :
      step code input s4 =
        some (.next { s4 with
          pc := if ltb (setupReg s4 11) (setupReg s4 6) then 20 else 5 }) :=
    step_branchLt_at (s := s4) (input := input) f4 hb

  by_cases hz : x.val = 0
  · rw [if_pos hz]
    have ez : step code input s4 = some (.next { s4 with pc := 20 }) := by
      simpa [hcmp, hz] using e4
    exact Steps.cons e0
      (Steps.cons e1 (Steps.cons e2 (Steps.cons e3 (Steps.cons ez (Steps.zero _)))))
  · rw [if_neg hz]
    have en : step code input s4 = some (.next s5) := by
      simpa [hcmp, hz, s5] using e4
    have f5 : code[s5.pc]? = some (.mov 3 11) := by
      rw [hp5] <;>
        exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (5 : Fin 8)
    have f6 : code[s6.pc]? = some (.sub 3 3 6) := by
      rw [hp6] <;>
        exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (6 : Fin 8)
    have f7 : code[s7.pc]? = some (.goto 8) := by
      rw [hp7] <;>
        exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (7 : Fin 8)
    have hx5 : setupReg s5 11 = x := hx4
    have ho5 : setupReg s5 6 = one := ho4
    have hx6 : setupReg s6 3 = x := by
      simp only [s6, setupReg_write_same]
    have ho6 : setupReg s6 6 = one := by
      simp (disch := decide) only [s6, setupReg_write_ne, ho5]
    have e5 : step code input s5 = some (.next s6) := by
      simpa only [hx5] using
        (setup_mov_at (s := s5) (input := input) f5 (by rw [hp5, hsize] <;> decide))
    have e6 : step code input s6 = some (.next s7) := by
      simpa only [hx6, ho6] using
        (setup_sub_at (s := s6) (input := input) f6 (by rw [hp6, hsize] <;> decide))
    have e7 : step code input s7 = some (.next { s7 with pc := 8 }) :=
      step_goto_at (s := s7) (input := input) f7 (by rw [hsize] <;> decide)
    exact Steps.cons e0
      (Steps.cons e1 (Steps.cons e2 (Steps.cons e3 (Steps.cons en
        (Steps.cons e5 (Steps.cons e6 (Steps.cons e7 (Steps.zero _))))))))

end PaperB.RamProgram.ThreeCalls
