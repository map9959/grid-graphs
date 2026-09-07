import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoEdgeLedger

/-! # Full W2 missing-side closure

The enlarged rectangle includes root spokes and shallow horizontal carriers.
Its actual FF edges obey the height-independent mixed bound. The forest
ledger then excludes W2, including k=5, without an equality exception.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- Every feasible W2 missing-side set satisfies the sharp target. There is
no prescribed pure count, root phase, deep count, rod list, or connectedness
hypothesis: a counterexample would derive p=3 and all geometric inputs. -/
theorem card_le_target_of_cost_two_missing_side {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  by_contra h
  have hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card := by omega
  have hpge := stable_counterexample_three_le_pure_carriers hk F hacyc hf
  have hple := pure_carriers_le_offside_holes_add_one (by omega) F s hmissing
  have hholes := (cost_two_boundary (by omega) F hacyc s hW).2.1
  have hp : (pureBoundaryCarriers F).card = 3 := by omega
  have hprofile := three_pure_missing_side_exact_profile hk F hacyc s hmissing hf hp
  dsimp only at hprofile
  have hnonpure : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent - 3 ≤ k + 2 := by omega
  have hmass := cost_two_pure_mass hk F hacyc s hmissing hW
  have hforest := nonpure_forest_ledger F hacyc
  rw [hp, hmass] at hforest
  have hedge := (cost_two_nonpure_edges_le_rectangle hk F hacyc s hmissing hW).trans
    (cost_two_mixed_edge_bound hk F hacyc s hmissing hf hp hW)
  have hbound : F.card ≤ 10 * k + 4 + (k - 1) * (3 * k - 1) := by omega
  have hk1 : k - 1 + 1 = k := by omega
  have hk3 : 3 * k - 1 + 1 = 3 * k := by omega
  have hmul : (k - 1) * (3 * k - 1) + 4 * k = 3 * k ^ 2 + 1 := by
    nlinarith only [hk1, hk3]
  omega

/-- Only weighted off-side costs three and four remain in the three-pure
missing-side counterexample branch. W2 is no longer a surviving profile. -/
theorem three_pure_missing_side_cost_three_or_four {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3) :
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3 ∨
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 4 := by
  have hcost := (three_pure_missing_side_root_cost hk F hacyc s hmissing hf hp).2
  have hne : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≠ 2 := by
    intro hW
    have ht := card_le_target_of_cost_two_missing_side hk F hacyc s hmissing hW
    omega
  omega

end GridGraphs.CarrierLayers.ThreeCarrier
