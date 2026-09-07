import GridGraphs.Accounting.CarrierLayers.FourCarrier.ShallowImage

/-! # The fixed-map loss closes all widths except seventeen

The actual image partition gives `K+J >= k+2`, while `J<=2` and `K+D=5`.
Thus any remaining counterexample has `k=5`, `J=2`, `K=5`, and `D=0`.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

theorem four_pure_image_loss_bound {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 4) :
    k + 2 ≤ (12 * k + 4 - ((F.filter IsGridBoundary).card + (F.filter IsNextRing).card)) +
      (shallowSidePreimages (by omega) F s).card := by
  have hmap := layers_add_side_holes_le_deep_add_shallow_image (by omega) F hacyc s
  have hd := (four_pure_missing_side_shallow_eq_one hk F hacyc s hmissing hf hp).2
  have hq := (four_pure_missing_side_profile hk F hacyc s hmissing hf hp).2.1
  have hholes := side_holes_add_roots (by omega) F s
  rw [hd] at hmap
  omega

/-- The entire four-pure missing-side branch satisfies the target at `k>=6`. -/
theorem card_le_target_of_four_pure_missing_side_ge_six {k : Nat} (hk : 6 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hp : (pureBoundaryCarriers F).card = 4) : F.card ≤ 3 * k ^ 2 + 7 * k := by
  by_contra h
  have hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card := by omega
  have hK := four_pure_image_loss_bound (by omega) F hacyc s hmissing hf hp
  have hJ := shallow_side_preimages_card_le_two (by omega) F hacyc s hmissing hf hp
  have hD := four_pure_missing_side_deficit_eq_five (by omega) F hacyc s hmissing hf hp
  omega

/-- Exact residual physical losses, not merely an abstract numerical profile. -/
theorem four_pure_missing_side_last_losses {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 4) :
    k = 5 ∧ (shallowSidePreimages (by omega) F s).card = 2 ∧
      12 * k + 4 - ((F.filter IsGridBoundary).card + (F.filter IsNextRing).card) = 5 ∧
      (3 * k - 2) * (k - 1) -
        (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card = 0 := by
  have hK := four_pure_image_loss_bound hk F hacyc s hmissing hf hp
  have hJ := shallow_side_preimages_card_le_two hk F hacyc s hmissing hf hp
  have hD := four_pure_missing_side_deficit_eq_five hk F hacyc s hmissing hf hp
  omega

end GridGraphs.CarrierLayers.FourCarrier
