import Mathlib

namespace GridGraphs.DiagonalStripeArm

/-- The four arms counted here are disjoint, including at their central ends. -/
theorem cheap_arm {a b c d : ℕ} (h : a + b + c + d ≤ 9) :
    a ≤ 2 ∨ b ≤ 2 ∨ c ≤ 2 ∨ d ≤ 2 := by omega

/-- Local uniformity extends along an unbounded arm: each consecutive
pair of windows shares at least one nonexceptional word. -/
theorem glue {α β : Type*} (word : α → β) (win : ℕ → Set α)
    (phase : ℕ → β) (L : ℕ)
    (constant : ∀ i ≤ L, ∀ x ∈ win i, word x = phase i)
    (meet : ∀ i < L, ∃ x, x ∈ win i ∧ x ∈ win (i+1)) :
    ∀ i ≤ L, ∀ x ∈ win i, word x = phase 0 := by
  have hp : ∀ i ≤ L, phase i = phase 0 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      obtain ⟨x, h, h'⟩ := meet i (by omega)
      exact (constant (i+1) hi x h').symm.trans
        ((constant i (by omega) x h).trans (ih (by omega)))
  intro i hi x hx
  exact (constant i hi x hx).trans (hp i hi)

/-- Comparison used for each rational sector-dual certificate. The
quadratic Newton coefficients agree, so strictness persists at every step. -/
theorem newton_strict {a b c d e : ℚ} (ha : a < b) (hc : c ≤ d) (t : ℕ) :
    a + (t : ℚ)*c + (t.choose 2 : ℚ)*e <
    b + (t : ℚ)*d + (t.choose 2 : ℚ)*e := by
  have h := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α := ℚ) t)
  linarith

end GridGraphs.DiagonalStripeArm

namespace GridGraphs.RailSeam

/-- Integer rounding in the two separated-cap case. The inputs are
the two cap prices, the interpolated seam price at 9/10 or 7/10
(here 7/10), and the physical score decomposition. -/
theorem two_separated_caps {k r n a b h A B M c d : ℤ}
    (hr : r = k+1) (hn : n=3*k+1) (hh : a+b+h+2=n)
    (cap₁ : 10*(A-a*r)+7*c ≤ 3*k+7*r-13)
    (cap₂ : 10*(B-b*r)+7*d ≤ 3*k+7*r-13)
    (seam : 10*(M-h*r) ≤ 7*(c+d-r-1)) :
    A+B+M+2*r ≤ 3*k^2+5*k+(3*k-13)/10 := by
  have z : 10*(A+B+M+2*r-(3*k^2+5*k)) ≤ 3*k-16 := by
    have eq : (a+b+h+2)*r=n*r := by rw [hh]
    rw [hr,hn] at eq
    rw [hr] at cap₁ cap₂ seam ⊢
    nlinarith
  omega

end GridGraphs.RailSeam
