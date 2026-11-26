import Mathlib

namespace GridGraphs.CollarPeel

def C (k : ℤ) := 3*k^2+5*k+(3*k-13)/10

theorem increment (k : ℤ) :
    C k - C (k-2) = 4*(3*k+1)-6 + ((3*k-13)/10-(3*(k-2)-13)/10) := by
  unfold C
  ring

theorem rounding (k : ℤ) :
    0 ≤ (3*k-13)/10-(3*(k-2)-13)/10 ∧
    (3*k-13)/10-(3*(k-2)-13)/10 ≤ 1 := by omega

/-- `a` of the last removed ring's marks have been recovered in the crop. -/
theorem transfer (k M small ann f a : ℤ)
    (crop : M ≤ small + ann + f - a) (cap : ann ≤ 4*(3*k+1)-9) :
    M-C k ≤ small-C (k-2) - (3 + ((3*k-13)/10-(3*(k-2)-13)/10) - (f-a)) := by
  have h := increment k
  omega

theorem fourLayers (k M small ann other recovered : ℤ)
    (cap : ann ≤ 8*(3*k+1)-40)
    (crop : M ≤ small + ann + other - recovered) :
    M-C k ≤ small-C (k-4) - 5 + other - recovered := by
  have h : C k - C (k-4) = 8*(3*k+1)-36 +
      ((3*k-13)/10-(3*(k-4)-13)/10) := by unfold C; ring
  omega

end GridGraphs.CollarPeel
