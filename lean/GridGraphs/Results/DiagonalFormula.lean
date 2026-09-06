import GridGraphs.Results.DiagonalUpper
import GridGraphs.Constructions.ResidueOne.ResidueOneMax
import GridGraphs.Constructions.ResidueZero.ResidueZeroLocalGeometry
import GridGraphs.Constructions.Finite.FiniteDiagonalConstructions

/-!
# The conditional diagonal formula

This file packages the remaining upper-bound and construction obligations as
named propositions and derives the proposed formula from them.
-/

namespace GridGraphs

open SimpleGraph

/-- The proposed number of preserved vertices on the diagonal square. -/
def diagonalFormulaP (n : Nat) : Nat := n * n - q n

/-- Every diagonal spanning tree has cotree incidence waste at least `n + 2`. -/
def UniversalDiagonalWasteBound : Prop :=
  ∀ (n : Nat), 3 ≤ n →
    ∀ (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph n n) T →
        n + 2 ≤ incidenceWaste (gridGraph n n \ T)

/-- Equality in the universal waste bound can occur only in residue one. -/
def WasteEqualityOnlyResidueOne : Prop :=
  ∀ (n : Nat), 3 ≤ n →
    ∀ (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph n n) T →
        incidenceWaste (gridGraph n n \ T) = n + 2 → n % 3 = 1

/-- In the stable residue-two range, the next possible waste value is excluded. -/
def ResidueTwoNearEqualityExcluded : Prop :=
  ∀ (k : Nat), 5 ≤ k →
    ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) ≠
          (3 * k + 2) + 5

/-- Constructions attain the proposed value at every nontrivial side length. -/
def MatchingDiagonalConstructions : Prop :=
  ∀ (n : Nat), 3 ≤ n → diagonalFormulaP n ≤ maxPreserved n n

private theorem div_three_mul_add (k r : Nat) (hr : r < 3) :
    (3 * k + r) / 3 = k := by
  omega

private theorem mod_three_mul_add (k r : Nat) (hr : r < 3) :
    (3 * k + r) % 3 = r := by
  omega

@[simp] theorem diagonalFormulaP_three_mul (k : Nat) (hk : 1 ≤ k) :
    diagonalFormulaP (3 * k) = 3 * k ^ 2 + 3 * k - 2 := by
  have hdiv : (3 * k) / 3 = k := by omega
  have hmod : (3 * k) % 3 = 0 := by omega
  have hq : q (3 * k) = 6 * k ^ 2 - 3 * k + 2 := by
    simp [q, hdiv, hmod]
  unfold diagonalFormulaP
  rw [hq]
  have hmul : (3 * k) * (3 * k) = 9 * k ^ 2 := by ring
  rw [hmul]
  have hleft : 3 * k ≤ 6 * k ^ 2 := by nlinarith
  have hright : 2 ≤ 3 * k ^ 2 + 3 * k := by nlinarith
  omega

@[simp] theorem diagonalFormulaP_three_mul_add_one (k : Nat) :
    diagonalFormulaP (3 * k + 1) = 3 * k ^ 2 + 5 * k := by
  unfold diagonalFormulaP q
  rw [div_three_mul_add k 1 (by omega), mod_three_mul_add k 1 (by omega)]
  simp only
  have hsub : 6 * k ^ 2 + k + 1 ≤ (3 * k + 1) * (3 * k + 1) := by
    nlinarith
  ring_nf
  omega

@[simp] theorem diagonalFormulaP_three_mul_add_two_lt_five
    (k : Nat) (hk : k < 5) :
    diagonalFormulaP (3 * k + 2) = 3 * k ^ 2 + 7 * k + 1 := by
  unfold diagonalFormulaP q
  rw [div_three_mul_add k 2 (by omega), mod_three_mul_add k 2 (by omega)]
  simp only [if_neg (by omega : ¬5 ≤ k)]
  have hsub : 6 * k ^ 2 + 5 * k + 3 ≤
      (3 * k + 2) * (3 * k + 2) := by
    nlinarith
  ring_nf
  omega

@[simp] theorem diagonalFormulaP_three_mul_add_two_ge_five
    (k : Nat) (hk : 5 ≤ k) :
    diagonalFormulaP (3 * k + 2) = 3 * k ^ 2 + 7 * k := by
  unfold diagonalFormulaP q
  rw [div_three_mul_add k 2 (by omega), mod_three_mul_add k 2 (by omega)]
  simp only [if_pos hk]
  have hsub : 6 * k ^ 2 + 5 * k + 4 ≤
      (3 * k + 2) * (3 * k + 2) := by
    nlinarith
  ring_nf
  omega

/-- The residue-one component of the construction hypothesis is unconditional. -/
theorem matchingDiagonalConstructions_residueOne (k : Nat) (hk : 1 ≤ k) :
    diagonalFormulaP (3 * k + 1) ≤
      maxPreserved (3 * k + 1) (3 * k + 1) := by
  rw [diagonalFormulaP_three_mul_add_one]
  exact residueOne_le_maxPreserved k hk

/-- The stable residue-zero component of the construction hypothesis is
unconditional. -/
theorem matchingDiagonalConstructions_residueZero (k : Nat) (hk : 7 ≤ k) :
    diagonalFormulaP (3 * k) ≤ maxPreserved (3 * k) (3 * k) := by
  rw [diagonalFormulaP_three_mul k (by omega)]
  exact residueZero_le_maxPreserved k hk

/-- The `3 x 3` residue-zero construction is unconditional. -/
theorem matchingDiagonalConstructions_three :
    diagonalFormulaP 3 ≤ maxPreserved 3 3 := by
  rw [show 3 = 3 * 1 by omega, diagonalFormulaP_three_mul 1 (by omega)]
  simpa using four_le_maxPreserved_three_three

/-- The six finite residue-zero constructions are unconditional. -/
theorem matchingDiagonalConstructions_residueZeroFinite
    (k : Nat) (hk1 : 1 ≤ k) (hk7 : k < 7) :
    diagonalFormulaP (3 * k) ≤ maxPreserved (3 * k) (3 * k) := by
  interval_cases k
  · simpa [diagonalFormulaP_three_mul 1 (by omega)] using
      four_le_maxPreserved_three_three
  · simpa [diagonalFormulaP_three_mul 2 (by omega)] using
      sixteen_le_maxPreserved_six_six
  · simpa [diagonalFormulaP_three_mul 3 (by omega)] using
      thirtyFour_le_maxPreserved_nine_nine
  · simpa [diagonalFormulaP_three_mul 4 (by omega)] using
      fiftyEight_le_maxPreserved_twelve_twelve
  · simpa [diagonalFormulaP_three_mul 5 (by omega)] using
      eightyEight_le_maxPreserved_fifteen_fifteen
  · simpa [diagonalFormulaP_three_mul 6 (by omega)] using
      oneHundredTwentyFour_le_maxPreserved_eighteen_eighteen

/-- The residue-two constructions through side length twenty are
unconditional. -/
theorem matchingDiagonalConstructions_residueTwoThroughTwenty
    (k : Nat) (hk1 : 1 ≤ k) (hk7 : k < 7) :
    diagonalFormulaP (3 * k + 2) ≤
      maxPreserved (3 * k + 2) (3 * k + 2) := by
  interval_cases k
  · simpa [diagonalFormulaP_three_mul_add_two_lt_five 1 (by omega)] using
      eleven_le_maxPreserved_five_five
  · simpa [diagonalFormulaP_three_mul_add_two_lt_five 2 (by omega)] using
      twentySeven_le_maxPreserved_eight_eight
  · simpa [diagonalFormulaP_three_mul_add_two_lt_five 3 (by omega)] using
      fortyNine_le_maxPreserved_eleven_eleven
  · simpa [diagonalFormulaP_three_mul_add_two_lt_five 4 (by omega)] using
      seventySeven_le_maxPreserved_fourteen_fourteen
  · simpa [diagonalFormulaP_three_mul_add_two_ge_five 5 (by omega)] using
      oneHundredTen_le_maxPreserved_seventeen_seventeen
  · simpa [diagonalFormulaP_three_mul_add_two_ge_five 6 (by omega)] using
      oneHundredFifty_le_maxPreserved_twenty_twenty

/-- The only remaining construction obligation is the stable residue-two tail
starting at side length twenty-three. -/
structure RemainingMatchingDiagonalConstructions : Prop where
  residueTwoTail :
    ∀ (k : Nat), 7 ≤ k →
      diagonalFormulaP (3 * k + 2) ≤
        maxPreserved (3 * k + 2) (3 * k + 2)

/-- The remaining finite and residue-two obligations combine with the completed
families to give all matching diagonal constructions. -/
theorem matchingDiagonalConstructions_of_remaining
    (h : RemainingMatchingDiagonalConstructions) :
    MatchingDiagonalConstructions := by
  intro n hn
  let k := n / 3
  have hn_decomp : n = 3 * k + n % 3 := by
    dsimp [k]
    omega
  have hmod : n % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases hr : n % 3
  · rw [hn_decomp]
    simp only [Nat.add_zero]
    by_cases hk7 : k < 7
    · exact matchingDiagonalConstructions_residueZeroFinite k (by omega) hk7
    · exact matchingDiagonalConstructions_residueZero k (by omega)
  · rw [hn_decomp]
    exact matchingDiagonalConstructions_residueOne k (by omega)
  · rw [hn_decomp]
    by_cases hk7 : k < 7
    · exact matchingDiagonalConstructions_residueTwoThroughTwenty k (by omega) hk7
    · exact h.residueTwoTail k (by omega)

private theorem diagonalFormula_residue_zero
    (hbound : UniversalDiagonalWasteBound)
    (hconstructions : MatchingDiagonalConstructions)
    (k : Nat) (hk : 1 ≤ k) :
    maxPreserved (3 * k) (3 * k) = diagonalFormulaP (3 * k) := by
  rw [diagonalFormulaP_three_mul k hk]
  apply maxPreserved_three_mul_eq_of_forall_incidenceWaste_ge k hk
  · exact hbound (3 * k) (by omega)
  · simpa [diagonalFormulaP_three_mul k hk] using
      hconstructions (3 * k) (by omega)

private theorem diagonalFormula_residue_one
    (hbound : UniversalDiagonalWasteBound) (k : Nat) (hk : 1 ≤ k) :
    maxPreserved (3 * k + 1) (3 * k + 1) =
      diagonalFormulaP (3 * k + 1) := by
  rw [diagonalFormulaP_three_mul_add_one]
  exact maxPreserved_residueOne_eq_of_forall_incidenceWaste_ge k hk
    (hbound (3 * k + 1) (by omega))

private theorem diagonalFormula_residue_two_lt_five
    (hbound : UniversalDiagonalWasteBound)
    (hequality : WasteEqualityOnlyResidueOne)
    (hconstructions : MatchingDiagonalConstructions)
    (k : Nat) (hk1 : 1 ≤ k) (hk5 : k < 5) :
    maxPreserved (3 * k + 2) (3 * k + 2) =
      diagonalFormulaP (3 * k + 2) := by
  rw [diagonalFormulaP_three_mul_add_two_lt_five k hk5]
  apply maxPreserved_three_mul_add_two_eq_of_forall_incidenceWaste_ge k
  · exact hbound (3 * k + 2) (by omega)
  · intro T _ hT heq
    have := hequality (3 * k + 2) (by omega) T hT heq
    rw [mod_three_mul_add k 2 (by omega)] at this
    omega
  · simpa [diagonalFormulaP_three_mul_add_two_lt_five k hk5] using
      hconstructions (3 * k + 2) (by omega)

private theorem diagonalFormula_residue_two_ge_five
    (hbound : UniversalDiagonalWasteBound)
    (hequality : WasteEqualityOnlyResidueOne)
    (hnear : ResidueTwoNearEqualityExcluded)
    (hconstructions : MatchingDiagonalConstructions)
    (k : Nat) (hk : 5 ≤ k) :
    maxPreserved (3 * k + 2) (3 * k + 2) =
      diagonalFormulaP (3 * k + 2) := by
  rw [diagonalFormulaP_three_mul_add_two_ge_five k hk]
  apply maxPreserved_three_mul_add_two_revised_eq_of_forall_incidenceWaste_ge
    k hk
  · exact hbound (3 * k + 2) (by omega)
  · intro T _ hT heq
    have := hequality (3 * k + 2) (by omega) T hT heq
    rw [mod_three_mul_add k 2 (by omega)] at this
    omega
  · exact hnear k hk
  · simpa [diagonalFormulaP_three_mul_add_two_ge_five k hk] using
      hconstructions (3 * k + 2) (by omega)

/-- The four stated hypotheses imply the diagonal formula at every side length
at least three. -/
theorem maxPreserved_eq_diagonalFormulaP
    (hbound : UniversalDiagonalWasteBound)
    (hequality : WasteEqualityOnlyResidueOne)
    (hnear : ResidueTwoNearEqualityExcluded)
    (hconstructions : MatchingDiagonalConstructions) :
    ∀ n : Nat, 3 ≤ n → maxPreserved n n = diagonalFormulaP n := by
  intro n hn
  let k := n / 3
  have hn_decomp : n = 3 * k + n % 3 := by
    dsimp [k]
    omega
  have hmod : n % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases hr : n % 3
  · rw [hn_decomp]
    simp only [Nat.add_zero]
    apply diagonalFormula_residue_zero hbound hconstructions
    omega
  · rw [hn_decomp]
    apply diagonalFormula_residue_one hbound
    omega
  · rw [hn_decomp]
    have hk1 : 1 ≤ k := by omega
    by_cases hk : k < 5
    · exact diagonalFormula_residue_two_lt_five
        hbound hequality hconstructions k hk1 hk
    · exact diagonalFormula_residue_two_ge_five
        hbound hequality hnear hconstructions k (by omega)

/-- With all finite constructions and the residue-zero/residue-one families
discharged, only the stable residue-two construction tail is needed by the
final formula theorem. -/
theorem maxPreserved_eq_diagonalFormulaP_of_remaining
    (hbound : UniversalDiagonalWasteBound)
    (hequality : WasteEqualityOnlyResidueOne)
    (hnear : ResidueTwoNearEqualityExcluded)
    (hconstructions : RemainingMatchingDiagonalConstructions) :
    ∀ n : Nat, 3 ≤ n → maxPreserved n n = diagonalFormulaP n :=
  maxPreserved_eq_diagonalFormulaP hbound hequality hnear
    (matchingDiagonalConstructions_of_remaining hconstructions)

end GridGraphs
