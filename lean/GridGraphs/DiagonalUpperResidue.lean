import GridGraphs.DiagonalFormula

/-!
# Residue-local diagonal upper bounds

The conditional upper side is split into the weakest residue-local statements
used by the arithmetic transfer to `maxPreserved`.
-/

namespace GridGraphs

open SimpleGraph

/-- The residue-zero family retains the exact `n + 2` waste requirement. -/
def ResidueZeroExactWasteRequirement : Prop :=
  ∀ (k : Nat), 1 ≤ k →
    ∀ (T : SimpleGraph (GridVertex (3 * k) (3 * k))) [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k) (3 * k)) T →
        3 * k + 2 ≤ incidenceWaste (gridGraph (3 * k) (3 * k) \ T)

/-- In residue one, only the linear lower bound `W ≥ n` is assumed. -/
def ResidueOneLinearWasteRequirement : Prop :=
  ∀ (k : Nat), 1 ≤ k →
    ∀ (T : SimpleGraph (GridVertex (3 * k + 1) (3 * k + 1)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 1) (3 * k + 1)) T →
        3 * k + 1 ≤
          incidenceWaste (gridGraph (3 * k + 1) (3 * k + 1) \ T)

/-- In residue two, only the linear lower bound `W ≥ n` is assumed. -/
def ResidueTwoLinearWasteRequirement : Prop :=
  ∀ (k : Nat), 1 ≤ k →
    ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        3 * k + 2 ≤
          incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T)

/-- Equality at `W = n + 2` is excluded in residue two. -/
def ResidueTwoExactWasteExcluded : Prop :=
  ∀ (k : Nat), 1 ≤ k →
    ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) ≠
          (3 * k + 2) + 2

/-- In the stable residue-two range, `W = n + 5` is also excluded. -/
def StableResidueTwoNearWasteExcluded : Prop :=
  ∀ (k : Nat), 5 ≤ k →
    ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) ≠
          (3 * k + 2) + 5

/-- The cotree identity upgrades the residue-one linear bound to `W ≥ n + 2`. -/
theorem residueOne_enoughWaste_of_linear
    (hlinear : ResidueOneLinearWasteRequirement) (k : Nat) (hk : 1 ≤ k)
    (T : SimpleGraph (GridVertex (3 * k + 1) (3 * k + 1)))
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 1) (3 * k + 1)) T) :
    (3 * k + 1) + 2 ≤
      incidenceWaste (gridGraph (3 * k + 1) (3 * k + 1) \ T) := by
  have hw := grid_cotree_incidenceWaste_identity (by omega) (by omega) hT
  have hD := D_expand (m := 3 * k + 1) (n := 3 * k + 1)
    (by omega) (by omega)
  have hge := hlinear k hk T hT
  have hsquare : (3 * k + 1) * (3 * k + 1) =
      9 * k ^ 2 + 6 * k + 1 := by ring
  rw [hsquare] at hw hD
  omega

/-- The cotree identity upgrades the residue-two linear bound to `W ≥ n + 2`. -/
theorem residueTwo_enoughWaste_of_linear
    (hlinear : ResidueTwoLinearWasteRequirement) (k : Nat) (hk : 1 ≤ k)
    (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T) :
    (3 * k + 2) + 2 ≤
      incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) := by
  have hw := grid_cotree_incidenceWaste_identity (by omega) (by omega) hT
  have hD := D_expand (m := 3 * k + 2) (n := 3 * k + 2)
    (by omega) (by omega)
  have hge := hlinear k hk T hT
  have hsquare : (3 * k + 2) * (3 * k + 2) =
      9 * k ^ 2 + 12 * k + 4 := by ring
  rw [hsquare] at hw hD
  omega

/-- In residue zero, the cotree identity rules out equality at `W = n + 2`. -/
theorem residueZero_exactWaste_ne
    (k : Nat) (hk : 1 ≤ k)
    (T : SimpleGraph (GridVertex (3 * k) (3 * k))) [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k) (3 * k)) T) :
    incidenceWaste (gridGraph (3 * k) (3 * k) \ T) ≠ 3 * k + 2 := by
  have hw := grid_cotree_incidenceWaste_identity (by omega) (by omega) hT
  have hD := D_expand (m := 3 * k) (n := 3 * k) (by omega) (by omega)
  have hsquare : (3 * k) * (3 * k) = 9 * k ^ 2 := by ring
  rw [hsquare] at hw hD
  omega

/-- Near-exact residue-zero operational upper bound. -/
theorem maxPreserved_residueZero_le_of_exactWaste
    (hzero : ResidueZeroExactWasteRequirement) (k : Nat) (hk : 1 ≤ k) :
    maxPreserved (3 * k) (3 * k) ≤ 3 * k ^ 2 + 3 * k - 2 :=
  maxPreserved_three_mul_le_of_forall_incidenceWaste_ge k hk (hzero k hk)

/-- The linear residue-one waste requirement gives the exact operational value. -/
theorem maxPreserved_residueOne_eq_of_linearWaste
    (hone : ResidueOneLinearWasteRequirement) (k : Nat) (hk : 1 ≤ k) :
    maxPreserved (3 * k + 1) (3 * k + 1) = 3 * k ^ 2 + 5 * k :=
  maxPreserved_residueOne_eq_of_forall_incidenceWaste_ge k hk
    (residueOne_enoughWaste_of_linear hone k hk)

/-- Near-exact residue-two upper bound after excluding `W = n + 2`. -/
theorem maxPreserved_residueTwo_le_of_linearWaste
    (htwo : ResidueTwoLinearWasteRequirement)
    (hne : ResidueTwoExactWasteExcluded) (k : Nat) (hk : 1 ≤ k) :
    maxPreserved (3 * k + 2) (3 * k + 2) ≤ 3 * k ^ 2 + 7 * k + 1 :=
  maxPreserved_three_mul_add_two_le_of_forall_incidenceWaste_ge k
    (residueTwo_enoughWaste_of_linear htwo k hk) (hne k hk)

/-- Stable near-exact residue-two upper bound after also excluding `W = n + 5`. -/
theorem maxPreserved_residueTwo_stable_le_of_linearWaste
    (htwo : ResidueTwoLinearWasteRequirement)
    (hne : ResidueTwoExactWasteExcluded)
    (hnear : StableResidueTwoNearWasteExcluded) (k : Nat) (hk : 5 ≤ k) :
    maxPreserved (3 * k + 2) (3 * k + 2) ≤ 3 * k ^ 2 + 7 * k :=
  maxPreserved_three_mul_add_two_revised_le_of_forall_incidenceWaste_ge
    k hk (residueTwo_enoughWaste_of_linear htwo k (by omega))
      (hne k (by omega)) (hnear k hk)

/-- The five minimal upper-side assumptions, together with the remaining
construction tail, assemble the full diagonal formula. -/
theorem maxPreserved_eq_diagonalFormulaP_of_residue_requirements
    (hzero : ResidueZeroExactWasteRequirement)
    (hone : ResidueOneLinearWasteRequirement)
    (htwo : ResidueTwoLinearWasteRequirement)
    (hne : ResidueTwoExactWasteExcluded)
    (hnear : StableResidueTwoNearWasteExcluded)
    (hconstructions : RemainingMatchingDiagonalConstructions) :
    ∀ n : Nat, 3 ≤ n → maxPreserved n n = diagonalFormulaP n := by
  apply maxPreserved_eq_diagonalFormulaP_of_remaining _ _ _ hconstructions
  · intro n hn
    let k := n / 3
    have hn_decomp : n = 3 * k + n % 3 := by
      dsimp [k]
      omega
    have hmod : n % 3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases hr : n % 3
    · rw [hn_decomp]
      simp only [Nat.add_zero]
      exact hzero k (by omega)
    · rw [hn_decomp]
      exact residueOne_enoughWaste_of_linear hone k (by omega)
    · rw [hn_decomp]
      exact residueTwo_enoughWaste_of_linear htwo k (by omega)
  · intro n hn
    let k := n / 3
    have hn_decomp : n = 3 * k + n % 3 := by
      dsimp [k]
      omega
    have hmod : n % 3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases hr : n % 3
    · rw [hn_decomp]
      simp only [Nat.add_zero]
      intro T _ hT heq
      exact (residueZero_exactWaste_ne k (by omega) T hT heq).elim
    · rw [hn_decomp]
      simp
    · rw [hn_decomp]
      intro T _ hT heq
      exact (hne k (by omega) T hT heq).elim
  · exact hnear

end GridGraphs
