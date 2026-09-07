import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.Closure
import GridGraphs.Accounting.CarrierLayers.Annulus.Upper

/-! # The remaining global counterexamples are all-covered

Missing-side closure upgrades the annulus carrier and excess budgets from
conditional coverage statements to global statements at every positive excess.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

/-- Every stable counterexample has at least four pure carriers and at least
`k+4` induced preserved components. This does not exclude the all-covered case. -/
theorem stable_counterexample_pure_and_induced {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    4 ≤ (pureBoundaryCarriers F).card ∧
      k + 4 ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent := by
  have hcovered := ThreeCarrier.counterexample_all_sides_covered hk F hacyc hf
  obtain ⟨_, _, _, hp⟩ := distinct_pure_carriers_of_all_open_sides_covered
    (by omega) F hacyc hcovered
  exact ⟨hp, Annulus.counterexample_components_ge_of_four_pure hk F hacyc hf hp⟩

/-- Global excess budget after excluding all missing-side counterexamples. -/
theorem stable_excess_budget {k excess : Nat} (hk : 5 ≤ k) (he : 1 ≤ excess)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + excess ≤ F.card) :
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) +
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent + 3 * excess ≤ 2 * k + 8 := by
  have hp := (stable_counterexample_pure_and_induced hk F hacyc (by omega)).1
  exact Annulus.counterexample_budget_of_four_pure hk he F hacyc hf hp

end GridGraphs.CarrierLayers
