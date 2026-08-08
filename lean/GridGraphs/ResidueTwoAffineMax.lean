import GridGraphs.ResidueTwoAffineStep
import GridGraphs.ConstructionCertificate

/-!
# Connectivity obligation and consequences for the affine residue-two family

The exact remaining topological statement is exposed as a ranked, rooted
certificate.  Everything after that statement, including dual connectivity
and the lower bound on `maxPreserved`, is proved unconditionally from such a
certificate.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The exact unresolved topological proposition for one affine member. -/
def ResidueTwoAffineDualConnectivity (k : Nat) : Prop :=
  (uuDualGraph (uResidueTwoAffine k)).Connected

/-- The precise symbolic connectivity obligation for one affine member. -/
def ResidueTwoAffineRankedConnectivity (k : Nat) : Prop :=
  Nonempty (RankedParentCertificate (uuDualGraph (uResidueTwoAffine k)))

/-- A ranked certificate closes the U-U dual connectivity obligation. -/
theorem uResidueTwoAffine_dual_connected_of_ranked
    (k : Nat) (h : ResidueTwoAffineRankedConnectivity k) :
    ResidueTwoAffineDualConnectivity k := by
  exact h.some.connected

/-- Exact size of the complement of the affine U pattern. -/
theorem uResidueTwoAffine_compl_card (k : Nat) (hk : 5 ≤ k) :
    ((Finset.univ : Finset (GridVertex (3 * k + 2) (3 * k + 2))) \
      uResidueTwoAffine k).card = 3 * k ^ 2 + 6 * k + 5 := by
  rw [Finset.card_sdiff, Finset.inter_univ, uResidueTwoAffine_card k hk]
  have htotal :
      Fintype.card (GridVertex (3 * k + 2) (3 * k + 2)) =
        (3 * k + 2) * (3 * k + 2) := by
    unfold GridVertex
    simp
  rw [Finset.card_univ, htotal]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  ring_nf
  omega

/-- The affine construction gives the claimed lower bound from the exact dual
connectivity proposition. -/
theorem residueTwoAffine_le_maxPreserved_of_dual_connected
    (k : Nat) (hk : 5 ≤ k) (h : ResidueTwoAffineDualConnectivity k) :
    3 * k ^ 2 + 6 * k + 5 ≤
      maxPreserved (3 * k + 2) (3 * k + 2) := by
  rw [← uResidueTwoAffine_compl_card k hk]
  exact compl_card_le_maxPreserved_of_uuDual_connected
    (by omega) (by omega) (uResidueTwoAffine k) h

/-- Ranked connectivity is a concrete sufficient certificate for the bound. -/
theorem residueTwoAffine_le_maxPreserved_of_ranked (k : Nat) (hk : 5 ≤ k)
    (h : ResidueTwoAffineRankedConnectivity k) :
    3 * k ^ 2 + 6 * k + 5 ≤
      maxPreserved (3 * k + 2) (3 * k + 2) :=
  residueTwoAffine_le_maxPreserved_of_dual_connected k hk
    (uResidueTwoAffine_dual_connected_of_ranked k h)

/-- Exact dual connectivity for the family yields the uniform bound. -/
theorem residueTwoAffine_uniform_le_maxPreserved_of_dual_connected
    (h : ∀ k, 5 ≤ k → ResidueTwoAffineDualConnectivity k) :
    ∀ k, 5 ≤ k → 3 * k ^ 2 + 6 * k + 5 ≤
      maxPreserved (3 * k + 2) (3 * k + 2) := by
  intro k hk
  exact residueTwoAffine_le_maxPreserved_of_dual_connected k hk (h k hk)

/-- A family of ranked certificates yields the uniform residue-two bound. -/
theorem residueTwoAffine_uniform_le_maxPreserved
    (h : ∀ k, 5 ≤ k → ResidueTwoAffineRankedConnectivity k) :
    ∀ k, 5 ≤ k → 3 * k ^ 2 + 6 * k + 5 ≤
      maxPreserved (3 * k + 2) (3 * k + 2) := by
  intro k hk
  exact residueTwoAffine_le_maxPreserved_of_ranked k hk (h k hk)

/-- The explicit affine base and the four one-step geometry obligations suffice
for the uniform residue-two lower bound. -/
theorem residueTwoAffine_uniform_le_maxPreserved_of_stepGeometry
    (steps : ∀ k, 5 ≤ k → ResidueTwoAffineStepGeometry k) :
    ∀ k, 5 ≤ k → 3 * k ^ 2 + 6 * k + 5 ≤
      maxPreserved (3 * k + 2) (3 * k + 2) :=
  residueTwoAffine_uniform_le_maxPreserved_of_dual_connected
    (uResidueTwoAffine_dual_connected_of_stepGeometry steps)

end GridGraphs
