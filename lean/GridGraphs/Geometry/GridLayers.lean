import GridGraphs.Accounting.LinearWaste

/-! # Coordinate layers of a square grid -/

namespace GridGraphs

/-- The boundary of the once-cropped square, in the original grid coordinates. -/
def IsNextRing {n : Nat} (v : GridVertex n n) : Prop :=
  1 ≤ v.1.val ∧ v.1.val ≤ n - 2 ∧ 1 ≤ v.2.val ∧ v.2.val ≤ n - 2 ∧
    (v.1.val = 1 ∨ v.1.val = n - 2 ∨ v.2.val = 1 ∨ v.2.val = n - 2)

end GridGraphs
