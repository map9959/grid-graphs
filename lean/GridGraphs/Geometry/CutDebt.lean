import Mathlib

namespace GridGraphs.CutDebt

/-- Merging components is not payment. `owed` only decreases when labels
actually reach a tooth; `classes` may decrease earlier. -/
theorem pay_at_tooth (loss base born paid owed₀ owed₁ classes₀ classes₁ : Int)
    (transfer : base + born ≤ loss + classes₁ - classes₀)
    (ledger : owed₁ = owed₀ + born - paid) :
    base + paid + (owed₁ - classes₁) - (owed₀ - classes₀) ≤ loss := by omega

/-- No identical endpoint assumption: even on a proper subinterval the
unpaid endpoint potential is preserved. -/
theorem telescope (loss bill pot : Nat → Int) (m n : Nat)
    (step : ∀ i, bill i + pot (i+1) - pot i ≤ loss i) :
    (∑ j ∈ Finset.range n, bill (m+j)) + pot (m+n) - pot m ≤
      ∑ j ∈ Finset.range n, loss (m+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h := step (m+n)
    rw [Nat.add_succ, Nat.succ_eq_add_one (m+n)]
    omega

theorem budget1 (t births extra east long : Int)
    (h : 6*(39+14*t)+20+3*east+10*long+2*births+extra ≤ 3*(198+72*t)) :
    2*births+extra+3*east+10*long ≤ 340+132*t := by omega

theorem budget2 (t births extra east long : Int)
    (h : 5*(39+14*t)+28+4*east+11*long+2*births+extra ≤ 3*(198+72*t)) :
    2*births+extra+4*east+11*long ≤ 371+146*t := by omega

theorem traffic (t excess east edge : Int)
    (h : 198+72*t ≤ 4*(39+14*t)+2-east+6*excess-edge) :
    40+16*t+east+edge ≤ 6*excess := by omega

end GridGraphs.CutDebt
