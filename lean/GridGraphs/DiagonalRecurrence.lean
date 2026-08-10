import GridGraphs.DiagonalFormula

/-!
# The diagonal recurrence

This file gives an arithmetic route to the diagonal formula. It is independent
of the waste and construction hypotheses used in `DiagonalFormula`.
-/

namespace GridGraphs

/-- The proposed three-step recurrence for the diagonal maximum, including its
single exceptional decrement at side length seventeen. -/
structure DiagonalRecurrence : Prop where
  three : maxPreserved 3 3 = 4
  four : maxPreserved 4 4 = 8
  five : maxPreserved 5 5 = 11
  step : ∀ n : Nat, 6 ≤ n →
    maxPreserved n n =
      maxPreserved (n - 3) (n - 3) + 2 * n - (if n = 17 then 1 else 0)

private theorem diagonalFormulaP_recurrence (n : Nat) (hn : 6 ≤ n) :
    diagonalFormulaP n =
      diagonalFormulaP (n - 3) + 2 * n - (if n = 17 then 1 else 0) := by
  let k := n / 3
  have hn_decomp : n = 3 * k + n % 3 := by
    dsimp [k]
    omega
  have hmod : n % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases hr : n % 3
  · have hk : 2 ≤ k := by omega
    obtain ⟨j, hkj⟩ := Nat.exists_eq_add_of_le hk
    have hkj' : k = j + 2 := by omega
    rw [hkj'] at hn_decomp
    rw [hn_decomp]
    simp only [Nat.add_zero]
    rw [diagonalFormulaP_three_mul (j + 2) (by omega)]
    have hsub : 3 * (j + 2) - 3 = 3 * (j + 1) := by omega
    rw [hsub, diagonalFormulaP_three_mul (j + 1) (by omega)]
    simp only [if_neg (by omega : 3 * (j + 2) ≠ 17)]
    ring_nf
    omega
  · have hk : 2 ≤ k := by omega
    obtain ⟨j, hkj⟩ := Nat.exists_eq_add_of_le hk
    have hkj' : k = j + 2 := by omega
    rw [hkj'] at hn_decomp
    rw [hn_decomp]
    rw [diagonalFormulaP_three_mul_add_one (j + 2)]
    have hsub : 3 * (j + 2) + 1 - 3 = 3 * (j + 1) + 1 := by omega
    rw [hsub, diagonalFormulaP_three_mul_add_one (j + 1)]
    simp only [if_neg (by omega : 3 * (j + 2) + 1 ≠ 17)]
    ring_nf
    omega
  · have hk : 2 ≤ k := by omega
    obtain ⟨j, hkj⟩ := Nat.exists_eq_add_of_le hk
    have hkj' : k = j + 2 := by omega
    rw [hkj'] at hn_decomp
    rw [hn_decomp]
    have hsub : 3 * (j + 2) + 2 - 3 = 3 * (j + 1) + 2 := by omega
    rw [hsub]
    by_cases hj : j + 2 < 5
    · rw [diagonalFormulaP_three_mul_add_two_lt_five (j + 2) hj]
      rw [diagonalFormulaP_three_mul_add_two_lt_five (j + 1) (by omega)]
      simp only [if_neg (by omega : 3 * (j + 2) + 2 ≠ 17)]
      ring_nf
      omega
    · by_cases heq : j + 2 = 5
      · have hj3 : j = 3 := by omega
        subst j
        rw [diagonalFormulaP_three_mul_add_two_ge_five 5 (by omega)]
        rw [diagonalFormulaP_three_mul_add_two_lt_five 4 (by omega)]
        simp
      · rw [diagonalFormulaP_three_mul_add_two_ge_five (j + 2) (by omega)]
        rw [diagonalFormulaP_three_mul_add_two_ge_five (j + 1) (by omega)]
        simp only [if_neg (by omega : 3 * (j + 2) + 2 ≠ 17)]
        ring_nf
        omega

/-- The three base values and the exceptional three-step recurrence determine
the diagonal maximum at every side length at least three. -/
theorem maxPreserved_eq_diagonalFormulaP_of_recurrence
    (h : DiagonalRecurrence) :
    ∀ n : Nat, 3 ≤ n → maxPreserved n n = diagonalFormulaP n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn3 : n = 3
      · subst n
        simpa [diagonalFormulaP_three_mul 1 (by omega)] using h.three
      by_cases hn4 : n = 4
      · subst n
        simpa [diagonalFormulaP_three_mul_add_one 1] using h.four
      by_cases hn5 : n = 5
      · subst n
        simpa [diagonalFormulaP_three_mul_add_two_lt_five 1 (by omega)] using h.five
      have hn6 : 6 ≤ n := by omega
      rw [h.step n hn6, diagonalFormulaP_recurrence n hn6]
      rw [ih (n - 3) (by omega) (by omega)]

end GridGraphs
