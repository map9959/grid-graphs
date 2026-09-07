import GridGraphs.Accounting.CarrierLayers.FourCarrier.FiveCarriers

/-! # Excluding saturated roots in the four-carrier branch

The endpoint and five-carrier arguments remove `q=k`. The global capacity
reduction then gives the unique remaining four-pure missing-side profile.
This is not yet an exclusion of that remaining one-excess profile.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- A missing side with at most four pure carriers and at most four weighted
off-side units cannot have `k` roots. No score or connectedness premise is used. -/
theorem missing_side_roots_lt_of_pure_le_four {k : Nat} (hk : 3 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hp : (pureBoundaryCarriers F).card ≤ 4)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 4) :
    (F.filter (OnOpenSide s)).card < k := by
  have hq := missing_side_preserved_card_le (by omega) F hacyc s hmissing
  by_contra h
  have hsat : (F.filter (OnOpenSide s)).card = k := by omega
  have hfive := saturated_missing_side_five_pure hk F hacyc s hmissing hsat hW
  omega

/-- Every four-pure missing-side counterexample has exactly
`f=T+1`, `q=k-1`, `r=k+4`, `c=1`, `b=2k+4`, and at most one shallow nonpure
carrier. The former `q<k` geometric premise has been discharged. -/
theorem four_pure_missing_side_profile {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 4) :
    F.card = 3 * k ^ 2 + 7 * k + 1 ∧
      (F.filter (OnOpenSide s)).card = k - 1 ∧
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent = k + 4 ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent = 1 ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 4 ∧
      (nextRingCarriers F).card ≤ 1 := by
  have hW := four_pure_offside_deficiency_le_four hk F hacyc s hmissing hf hp
  have hq := missing_side_roots_lt_of_pure_le_four (by omega) F hacyc s hmissing
    (by omega) hW
  exact ⟨(missing_side_exact_slack hk F hacyc s hmissing hf).1,
    four_pure_unsaturated_profile hk F hacyc s hmissing hf hp hq⟩

end GridGraphs.CarrierLayers.FourCarrier
