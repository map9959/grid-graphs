import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostThreeMixedBound
import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.RectangleEdgeCover
import GridGraphs.Accounting.CarrierLayers.FourCarrier.Closure

/-! # Closing the entire missing-side branch

At W3 the extra off-side hole is left unclassified. Its two incident frame
edges give a sufficient joint defect allowance, even at k=5. W2 and W4
were already excluded, and FourCarrier closes the remaining pure-count case.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- Full W3 closure with three pure carriers. No extra-hole adjacency,
canonical frame orientation, or one-edge defect assumption is required. -/
theorem card_le_target_of_three_pure_cost_three {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  by_contra h
  have hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card := by omega
  have hprofile := three_pure_missing_side_two_profiles hk F hacyc s hmissing hf hp
  dsimp only at hprofile
  have hnonpure : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent - 3 ≤ k + 1 := by omega
  have hmass := cost_three_pure_mass hk F hacyc s hmissing hW
  have hforest := nonpure_forest_ledger F hacyc
  rw [hp, hmass] at hforest
  have hcover := nonpure_edges_le_rectangle_of_containment F s
    (fun u hu => (cost_three_nonpure_rectangle_iff hk F hacyc s hmissing hW u hu).mp)
  have hedge := hcover.trans (cost_three_mixed_edge_bound hk F hacyc s hmissing hf hp hW)
  have hbound : F.card ≤ 10 * k + 4 + (k - 1) * (3 * k - 1) := by omega
  have hk1 : k - 1 + 1 = k := by omega
  have hk3 : 3 * k - 1 + 1 = 3 * k := by omega
  have hmul : (k - 1) * (3 * k - 1) + 4 * k = 3 * k ^ 2 + 1 := by
    nlinarith only [hk1, hk3]
  omega

/-- Every feasible three-pure missing-side set satisfies the sharp target,
with no off-side cost assumption. -/
theorem card_le_target_of_three_pure_missing_side {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hmissing : ∃ s : Fin 4, ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  obtain ⟨s, hs⟩ := hmissing
  by_contra h
  have hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card := by omega
  have hW := three_pure_missing_side_cost_eq_three hk F hacyc s hs hf hp
  have ht := card_le_target_of_three_pure_cost_three hk F hacyc s hs hp hW
  omega

/-- Sharp target bound for every feasible missing-side set throughout k>=5.
The pure-carrier count is unrestricted. -/
theorem card_le_target_of_missing_side {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hmissing : ∃ s : Fin 4, ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  by_contra h
  have hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card := by omega
  have hp := missing_side_counterexample_pure_eq_three hk F hacyc hmissing hf
  have ht := card_le_target_of_three_pure_missing_side hk F hacyc hp hmissing
  omega

/-- Any stable counterexample is now all-covered by actual pure carriers. -/
theorem counterexample_all_sides_covered {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    ∀ s : Fin 4, ∃ C ∈ pureBoundaryCarriers F, ∃ v ∈ C.supp, OnOpenSide s v.val := by
  intro s
  by_contra h
  push Not at h
  have ht := card_le_target_of_missing_side hk F hacyc ⟨s, h⟩
  omega

end GridGraphs.CarrierLayers.ThreeCarrier
