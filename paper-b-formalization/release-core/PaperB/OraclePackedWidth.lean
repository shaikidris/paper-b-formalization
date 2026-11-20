import PaperB.OracleContract
import Lean

set_option autoImplicit false

namespace BinaryCapacity

def logWidth (n : Nat) : Nat := Nat.log2 (n + 1) + 1

theorem base_fits (n : Nat) : n + 1 < 2 ^ logWidth n := by
  unfold logWidth
  exact Nat.lt_log2_self

theorem cap_fits (n k slack : Nat) (hk : k ≤ 2 ^ slack) :
    k * (n + 1) < 2 ^ (logWidth n + slack) := by
  have hp : 0 < (2 : Nat) ^ slack := Nat.pow_pos (by decide)
  calc
    k * (n + 1) ≤ 2 ^ slack * (n + 1) := Nat.mul_le_mul_right _ hk
    _ < 2 ^ slack * 2 ^ logWidth n :=
      Nat.mul_lt_mul_of_pos_left (base_fits n) hp
    _ = 2 ^ (logWidth n + slack) := by
      rw [Nat.pow_add, Nat.mul_comm (2 ^ slack) (2 ^ logWidth n)]

end BinaryCapacity

namespace PaperB.OracleContract

/-- A physically measured linear payload fits the fixed-slack word width. -/
theorem linear_payload_fits (wordSlack n m factor cells : Nat)
    (hFactor : factor ≤ 2 ^ wordSlack) (hCells : cells ≤ factor * (n + m + 1)) :
    cells < 2 ^ wordBits wordSlack n m :=
  Nat.lt_of_le_of_lt hCells (BinaryCapacity.cap_fits (n + m) factor wordSlack hFactor)

end PaperB.OracleContract
