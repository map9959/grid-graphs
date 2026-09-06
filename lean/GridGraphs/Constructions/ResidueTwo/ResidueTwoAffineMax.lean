import GridGraphs.Constructions.ResidueTwo.ResidueTwoAffineStep
import GridGraphs.Constructions.ConstructionCertificate

/-!
# Lower bound from the affine residue-two family

The symbolic width-three geometry proves dual connectivity at every width, so
the exact complement cardinality gives an unconditional near-target lower
bound.
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

/-- The stable residue-two target exceeds the affine score by exactly `k-5`.
This identifies the construction gap without hiding it in asymptotic notation. -/
theorem residueTwoAffine_target_eq_compl_card_add_gap (k : Nat) (hk : 5 ≤ k) :
    3 * k ^ 2 + 7 * k =
      ((Finset.univ : Finset (GridVertex (3 * k + 2) (3 * k + 2))) \
        uResidueTwoAffine k).card + (k - 5) := by
  rw [uResidueTwoAffine_compl_card k hk]
  omega

/-- One affine width-three step gains `6k+9` preserved vertices, one fewer
than the `6k+10` gain required by the exact stable target. -/
theorem uResidueTwoAffine_compl_card_step (k : Nat) (hk : 5 ≤ k) :
    ((Finset.univ : Finset (GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2))) \
        uResidueTwoAffine (k + 1)).card =
      ((Finset.univ : Finset (GridVertex (3 * k + 2) (3 * k + 2))) \
        uResidueTwoAffine k).card + (6 * k + 9) := by
  rw [uResidueTwoAffine_compl_card (k + 1) (by omega),
    uResidueTwoAffine_compl_card k hk]
  ring

theorem residueTwoStableTarget_step (k : Nat) :
    3 * (k + 1) ^ 2 + 7 * (k + 1) =
      (3 * k ^ 2 + 7 * k) + (6 * k + 10) := by
  ring

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
theorem residueTwoAffine_uniform_le_maxPreserved_of_ranked
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

/-- Unconditional arbitrary-width lower bound supplied by the symbolic affine
step geometry. -/
theorem residueTwoAffine_uniform_le_maxPreserved :
    ∀ k, 5 ≤ k → 3 * k ^ 2 + 6 * k + 5 ≤
      maxPreserved (3 * k + 2) (3 * k + 2) :=
  residueTwoAffine_uniform_le_maxPreserved_of_dual_connected
    uResidueTwoAffine_dual_connected

end GridGraphs
