import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.SaturatedCorners

/-! # The three-carrier one-excess gap profile

Root deficit is strictly positive, not an assumed paper premise. The weighted
off-side cost is two, three, or four; cost four has a unique numerical profile.
This does not exclude those remaining profiles or assume a deep count of `k+1`.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- The actual weighted off-side sum equals the paper's natural subtraction
`b-(3k-q)`, without feasibility or a missing-carrier premise. -/
theorem offside_deficiency_eq_sub {k : Nat}
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2))) (s : Fin 4) :
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) =
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) -
        (3 * k - (F.filter (OnOpenSide s)).card) := by
  have hpart := offside_deficiency_add_side_holes (by omega) F s
  have hholes := side_holes_add_roots (by omega) F s
  omega

/-- Every three-pure missing-side counterexample has `q<k` and `2<=W<=4`.
The ledger first supplies `W<=5`; only then is saturated-root geometry used. -/
theorem three_pure_missing_side_root_cost {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3) :
    (F.filter (OnOpenSide s)).card < k ∧
      2 ≤ boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
        ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
        ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 4 := by
  obtain ⟨_, z, w, gamma, hr, hW, hc, hslack⟩ :=
    missing_side_exact_slack hk F hacyc s hmissing hf
  have hweight := offside_deficiency_eq_sub F s
  have hW5 : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 5 := by omega
  have hq := missing_side_roots_lt hk F hacyc s hmissing hf hp hW5
  have hglobal := stable_counterexample_induced_components_ge hk F hacyc hf
  omega

/-- Exact natural slacks with a positive root deficit. `h` is the actual
shallow nonpure count. Only the checked bound `h+m<=z+1` is claimed here,
not the stronger paper inequality `h+m<=z`. -/
theorem three_pure_missing_side_exact_profile {k : Nat} (hk : 5 ≤ k)
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
    let W := boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) - (3 * k - q)
    let m := k - q
    let z := r - q - 3
    let w := W - 2
    let gamma := c - 1
    F.card = 3 * k ^ 2 + 7 * k + 1 ∧
      q + m = k ∧ r = q + 3 + z ∧ W = 2 + w ∧ c = 1 + gamma ∧
      z + w + gamma = 3 ∧ 1 ≤ m ∧ m ≤ z ∧ z ≤ 3 ∧ w ≤ 2 ∧
      (nextRingCarriers F).card + m ≤ z + 1 := by
  dsimp only
  obtain ⟨hfe, z, w, gamma, hr, hW, hc, hslack⟩ :=
    missing_side_exact_slack hk F hacyc s hmissing hf
  have hq := (three_pure_missing_side_root_cost hk F hacyc s hmissing hf hp).1
  have hglobal := stable_counterexample_induced_components_ge hk F hacyc hf
  have hdeep := counterexample_deep_carriers_ge hk F hacyc hf
  omega

/-- Cost four is rigid: `(q,r,c,b)=(k-1,k+3,1,2k+5)` and at most one
actual shallow nonpure carrier. This is a necessary profile, not exclusion. -/
theorem three_pure_cost_four_rigidity {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 4) :
    (F.filter (OnOpenSide s)).card = k - 1 ∧
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent = k + 3 ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent = 1 ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 5 ∧
      (nextRingCarriers F).card ≤ 1 := by
  have hprofile := three_pure_missing_side_exact_profile hk F hacyc s hmissing hf hp
  have hweight := offside_deficiency_eq_sub F s
  dsimp only at hprofile
  omega

/-- Ordinary off-side holes are at least two, so corner holes use only the
residual slack `W-2`. At cost two this forces exactly two ordinary holes
and no corner holes. No path-run equality is assumed. -/
theorem three_pure_offside_hole_slack {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hp : (pureBoundaryCarriers F).card = 3) :
    let u := ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card
    let j := ((univ \ F).filter BoundarySix.Corner).card
    let W := boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) -
      (3 * k - (F.filter (OnOpenSide s)).card)
    2 ≤ u ∧ W = u + j ∧ j ≤ W - 2 ∧ (W = 2 → u = 2 ∧ j = 0) := by
  dsimp only
  have hpath := pure_carriers_le_offside_holes_add_one (by omega) F s hmissing
  have hweight := offside_deficiency_eq_holes_add_corners (by omega) F s
  have hsub := offside_deficiency_eq_sub F s
  omega

end GridGraphs.CarrierLayers.ThreeCarrier
