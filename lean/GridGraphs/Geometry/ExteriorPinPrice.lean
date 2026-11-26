import Mathlib

namespace GridGraphs.ExteriorPinPrice

/-- In each chain the cap partitions together can lose at most one of
the s independent pin constraints for free. Across both chains a paid
site occurs in at most three windows. -/
theorem chainDebit (s north₀ south₀ north₁ south₁ debit : ℤ)
    (h₀ : s-1 ≤ north₀+south₀) (h₁ : s-1 ≤ north₁+south₁)
    (cover : north₀+south₀+north₁+south₁ ≤ 3*debit) :
    2*(s-1) ≤ 3*debit := by omega

/-- Comparison after subtracting the common n² term. With n=3k+1
three times the comb minus n² is 9k - 1 + 3 floor((3k-13)/10). -/
theorem tallOffPhase (k h s coupon excess : ℤ) (size : 1000 ≤ 3*k+1)
    (height : 3*k+1 ≤ 2*h) (pins : 2 ≤ s)
    (rank : 2*(s-1) ≤ 3*coupon)
    (wingBound : 2*excess ≤ 8*(3*k+1)+64-2*s-2*coupon-3*h) :
    excess < 9*k-1+3*((3*k-13)/10) := by omega

end GridGraphs.ExteriorPinPrice
