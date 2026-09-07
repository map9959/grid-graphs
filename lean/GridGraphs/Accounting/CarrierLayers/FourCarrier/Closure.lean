import GridGraphs.Accounting.CarrierLayers.FourCarrier.SecondRootBoundary

/-! # Closing the four-pure missing-side one-excess branch

The image budget excludes `k>=6`. At the residual `k=5` equality, two
shallow preimages force a deep second-position root. Zero total deep deficit
fills its radial axis, contradicting the checked boundary six-cycle.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- No feasible missing-side counterexample has exactly four pure carriers,
throughout the stable range, including the exceptional width seventeen. -/
theorem four_pure_missing_side_counterexample_false {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 4) : False := by
  classical
  obtain ⟨_, hJ, _, hD⟩ := four_pure_missing_side_last_losses hk F hacyc s hmissing hf hp
  have hd := (four_pure_missing_side_shallow_eq_one hk F hacyc s hmissing hf hp).2
  have hcap := (physical_deficit_identity (by omega) F hacyc).2.1
  have hwidth : 3 * k + 2 - 4 = 3 * k - 2 := by omega
  rw [hd, hwidth] at hcap
  have htotal : (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card =
      (3 * k + 2 - 4) *
        (Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).ConnectedComponent -
          (pureBoundaryCarriers F).card - (nextRingCarriers F).card) := by
    rw [hd, hwidth]
    omega
  obtain ⟨u, hus, hup, huN⟩ := deep_second_root_of_two_shallow_preimages hk F hacyc s hmissing hf hp
    (by omega)
  let C := ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk u
  have hu : u ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have huP : C ∉ pureBoundaryCarriers F := fun h => hmissing C h u hu hus
  have hfull := deep_carrier_full_of_total_equality (by omega) F hacyc htotal C huP huN
  let t : Fin (3 * k + 2) := ⟨sidePosition s u.val, by have := sidePosition_bounds hus; omega⟩
  have ht : 2 ≤ t.val ∧ t.val + 2 < 3 * k + 2 := by dsimp [t]; omega
  have hts : OnOpenSide s (sideChart s (t, ⟨0, by omega⟩)) :=
    (sideChart_openSide s _).mpr (by dsimp [t]; omega)
  have hut : u.val = sideChart s (t, ⟨0, by omega⟩) :=
    sidePosition_injective hus hts (by rw [sideChart_position])
  have h2 := full_deep_root_axis (by omega) F hacyc s C u hu t hut ht hfull
    (⟨2, by omega⟩ : Fin (3 * k + 2)) (by dsimp; omega)
  have h3 := full_deep_root_axis (by omega) F hacyc s C u hu t hut ht hfull
    (⟨3, by omega⟩ : Fin (3 * k + 2)) (by dsimp; omega)
  have hW := four_pure_offside_deficiency_eq_three hk F hacyc s hmissing hf hp
  exact second_root_full_axis_false (by omega) F hacyc s hmissing (by omega) t
    (by dsimp [t]; omega) (hut ▸ u.property) h2 h3

/-- Sharp target bound for the entire four-pure missing-side branch. -/
theorem card_le_target_of_four_pure_missing_side {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card = 4)
    (hmissing : ∃ s : Fin 4, ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) : F.card ≤ 3 * k ^ 2 + 7 * k := by
  obtain ⟨s, hs⟩ := hmissing
  by_contra hf
  exact four_pure_missing_side_counterexample_false hk F hacyc s hs (by omega) hp

/-- Any remaining missing-side counterexample has exactly three pure carriers.
This does not exclude that separate branch or settle the all-covered case. -/
theorem missing_side_counterexample_pure_eq_three {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (hmissing : ∃ s : Fin 4, ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) : (pureBoundaryCarriers F).card = 3 := by
  obtain ⟨s, hs⟩ := hmissing
  rcases missing_side_pure_cases hk F hacyc s hs hf with hp | hp
  · exact hp
  · exact (four_pure_missing_side_counterexample_false hk F hacyc s hs hf hp).elim

end GridGraphs.CarrierLayers.FourCarrier
