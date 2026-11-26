import Mathlib

namespace GridGraphs.MissingArmCuts

/-- Transfer a lower bound on the length of a constant run through
`d` successive interfaces. `step` is the physical catalogue implication. -/
theorem erosion (L : Nat → Nat) (d : Nat)
    (step : ∀ i < d, L i ≤ L (i+1) + 2) : L 0 ≤ L d + 2*d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := ih (fun i hi => step i (by omega))
    have h' := step d (by omega)
    omega

theorem fringe (L : Nat → Nat) (d : Nat)
    (step : ∀ i < d, L i ≤ L (i+1) + 2) (last : L d ≤ 1) :
    L 0 ≤ 2*d+1 := by
  have h := erosion L d step
  omega

/-- Six separately charged seam closures already exceed the budget. -/
theorem repeats (b t : Nat) (cost : b*(39+14*t) ≤ 198+72*t) : b ≤ 5 := by
  by_contra! bad
  have h := Nat.mul_le_mul_right (39+14*t) (show 6 ≤ b by omega)
  omega

end GridGraphs.MissingArmCuts
