import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoClosure
import GridGraphs.Accounting.CarrierLayers.Annulus.Counterexamples
import GridGraphs.Accounting.CarrierLayers.FourCarrier.ShallowRequired

/-! # Eliminating W4 and reducing W3 to two actual profiles

The global annulus gain gives at least k deep carriers. A connected missing
side with a root deficit needs a shallow carrier, excluding r=k+3,c=1 at p=3.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- Minimal induced count and ambient connectedness are incompatible with a
three-pure missing-side counterexample. No off-side cost is prescribed. -/
theorem card_le_target_of_three_pure_minimal_connected {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hr : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 3)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 1) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  by_contra h
  have hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card := by omega
  have hq := (three_pure_missing_side_root_cost hk F hacyc s hmissing hf hp).1
  have hdeep := Annulus.counterexample_deep_carriers_ge hk F hacyc hf
  have hshallow := shallow_pos_of_connected_missing_side_root_deficit (by omega)
    F hacyc s hmissing hq hc
  change k ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
    (↑F : Set _)).ConnectedComponent - (pureBoundaryCarriers F).card -
    (nextRingCarriers F).card at hdeep
  omega

/-- W4 is closed: its rigid profile has r=k+3,c=1, while the global deep
bound forces h=0 and connected root deficit forces h>=1. -/
theorem card_le_target_of_three_pure_cost_four {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 4) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  by_contra h
  have hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card := by omega
  obtain ⟨_, hr, hc, _, _⟩ := three_pure_cost_four_rigidity hk F hacyc s hmissing hf hp hW
  have ht := card_le_target_of_three_pure_minimal_connected hk F hacyc s hmissing hp hr hc
  omega

/-- Every remaining three-pure missing-side counterexample has W=3. -/
theorem three_pure_missing_side_cost_eq_three {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3) :
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3 := by
  rcases three_pure_missing_side_cost_three_or_four hk F hacyc s hmissing hf hp with h | h
  · exact h
  · have ht := card_le_target_of_three_pure_cost_four hk F hacyc s hmissing hp h
    omega

/-- Exact remaining profiles: q=k-1,b=2k+4,d=k, and either
`(r,c,h)=(k+3,2,0)` or `(k+4,1,1)`. In particular the W3,m=2 branch is gone.
The shallow and deep counts refer to actual induced components. -/
theorem three_pure_missing_side_two_profiles {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3) :
    let q := (F.filter (OnOpenSide s)).card
    let r := Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent
    let c := Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent
    let h := (nextRingCarriers F).card
    F.card = 3 * k ^ 2 + 7 * k + 1 ∧ q = k - 1 ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 4 ∧
      r - 3 - h = k ∧
      ((r = k + 3 ∧ c = 2 ∧ h = 0) ∨ (r = k + 4 ∧ c = 1 ∧ h = 1)) := by
  have hW := three_pure_missing_side_cost_eq_three hk F hacyc s hmissing hf hp
  have hweight := offside_deficiency_eq_sub F s
  have hprofile := three_pure_missing_side_exact_profile hk F hacyc s hmissing hf hp
  dsimp only at hprofile ⊢
  have hdeep := Annulus.counterexample_deep_carriers_ge hk F hacyc hf
  change k ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
    (↑F : Set _)).ConnectedComponent - (pureBoundaryCarriers F).card -
    (nextRingCarriers F).card at hdeep
  have hconnected : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 1 → 1 ≤ (nextRingCarriers F).card := by
    intro hc
    exact shallow_pos_of_connected_missing_side_root_deficit (by omega) F hacyc s hmissing
      (by omega) hc
  omega

end GridGraphs.CarrierLayers.ThreeCarrier
