import GridGraphs.Constructions.ResidueTwo.LowerZipper

namespace GridGraphs.ResidueTwoLower

/-- Number of physical marks in the first `w` columns. -/
def rowCount (p : Nat → Bool) (w : Nat) := ((Finset.range w).filter fun j => p j).card

theorem rowCount_succ (p : Nat → Bool) (w : Nat) :
    rowCount p (w+1) = rowCount p w + (if p w then 1 else 0) := by
  simp [rowCount,Finset.range_add_one,Finset.filter_insert]
  split <;> simp_all

/-- Closed prefix sum of a regular row whose left tip is `3*a`.
Using a prefix sum also handles a rail cut through the middle of a pitch. -/
theorem regular_prefix (a w : Nat) :
    rowCount (regular (3*a)) w =
      min ((w+2)/3) (a+1) + ((w+1)/3-(a+1)) := by
  induction w with
  | zero => simp [rowCount]
  | succ w ih =>
    rw [rowCount_succ,ih]
    simp only [regular,leftRail,rightRail,Bool.or_eq_true,Bool.and_eq_true,
      decide_eq_true_eq,beq_iff_eq]
    split <;> omega

end GridGraphs.ResidueTwoLower
