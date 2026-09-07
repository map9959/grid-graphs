import GridGraphs.Accounting.CarrierLayers.FourCarrier.EndpointCost

/-! # Saturated roots at weighted off-side cost at most four

Endpoint exclusion leaves exactly enough room for the phase `2,5,...,3k-1`.
These conclusions use the weighted off-side sum, not a near-tight global budget.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- The paper's `W` agrees with the actual weighted off-side sum in this
branch; in particular its ledger upper bound is four. -/
theorem four_pure_offside_deficiency_le_four {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 4) :
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 4 := by
  have hslack := four_pure_missing_side_slack hk F hacyc s hmissing hf hp
  have hpart := offside_deficiency_add_side_holes (by omega) F s
  have hholes := side_holes_add_roots (by omega) F s
  dsimp only at hslack
  omega

/-- Saturation under `W<=4` has the exact phase `2,5,...,3k-1`, independently
of the pure-carrier count and score. Both endpoint positions have been excluded
by the five-unit weighted corner charge, not by a `b=2k+3` theorem. -/
theorem saturated_missing_side_exact_phase {k : Nat} (hk : 3 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hq : (F.filter (OnOpenSide s)).card = k)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 4) :
    ∀ v, OnOpenSide s v → (v ∈ F ↔ ∃ i < k, sidePosition s v = 3 * i + 2) := by
  classical
  let A := F.filter (OnOpenSide s)
  let S := A.image (sidePosition s)
  have hcard : S.card = k := by
    rw [card_image_iff.mpr, hq]
    intro u hu v hv he
    exact sidePosition_injective (mem_filter.mp hu).2 (mem_filter.mp hv).2 he
  have hbound : ∀ x ∈ S, 2 ≤ x ∧ x < 3 * k := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    have h := root_positions_of_offside_deficiency_le_four (by omega) F hacyc s hmissing hW
      v (mem_filter.mp hv).1 (mem_filter.mp hv).2
    simpa only [Nat.add_sub_cancel] using h
  have hspace : ∀ x ∈ S, ∀ y ∈ S, x < y → x + 3 ≤ y := by
    intro x hx y hy hlt
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
    obtain ⟨w, hw, hwr, huw⟩ := missing_side_root_inward (by omega) F hacyc s hmissing
      u (mem_filter.mp hu).1 (mem_filter.mp hu).2
    obtain ⟨z, hz, hzr, hvz⟩ := missing_side_root_inward (by omega) F hacyc s hmissing
      v (mem_filter.mp hv).1 (mem_filter.mp hv).2
    exact radial_pair_spacing (by omega) F hacyc s
      (mem_filter.mp hu).1 (mem_filter.mp hv).1 hw hz
      (mem_filter.mp hu).2 (mem_filter.mp hv).2 hwr hzr huw hvz hlt
  have hphase := tight_three_spaced_positions (by omega) S hcard hbound hspace
  intro v hvs
  rw [← hphase]
  constructor
  · intro hv
    exact mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, hvs⟩, rfl⟩
  · intro hv
    obtain ⟨u, hu, he⟩ := mem_image.mp hv
    have huv := sidePosition_injective (mem_filter.mp hu).2 hvs he
    exact huv ▸ (mem_filter.mp hu).1

end GridGraphs.CarrierLayers.FourCarrier
