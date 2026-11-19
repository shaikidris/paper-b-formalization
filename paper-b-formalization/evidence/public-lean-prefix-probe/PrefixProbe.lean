import Std

namespace PrefixProbe

def search (p : Nat → Bool) : Nat → Nat → Nat → Nat × Nat
  | 0, lo, _ => (lo, 0)
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then (lo, 0)
      else
        let mid := lo + (hi - lo) / 2
        if p mid then
          let r := search p fuel mid hi
          (r.1, r.2 + 1)
        else
          let r := search p fuel lo mid
          (r.1, r.2 + 1)

theorem search_count_le (p : Nat → Bool) (fuel lo hi : Nat) :
    (search p fuel lo hi).2 ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero =>
      simp [search]
  | succ fuel ih =>
      simp only [search]
      split
      · exact Nat.zero_le _
      · split
        · exact Nat.succ_le_succ (ih _ _)
        · exact Nat.succ_le_succ (ih _ _)

end PrefixProbe
