import GridGraphs.Accounting.CarrierLayers.FourCarrier.Ledger

/-! # Deep-capacity reductions for the four-carrier branch

These reductions use the actual shallow-carrier count and the fixed boundary
map. No equivariance of that map or local gap-cycle conclusion is assumed.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- The counterexample needs at least `k-1` carriers that reach the deep layer,
regardless of its pure-carrier count or boundary coverage. -/
theorem counterexample_deep_carriers_ge {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    k - 1 ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent -
      (pureBoundaryCarriers F).card - (nextRingCarriers F).card := by
  have hcap := card_le_perimeter_add_remaining_deep_capacity (by omega) F hacyc
  by_contra h
  have hsub : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent -
      (pureBoundaryCarriers F).card - (nextRingCarriers F).card ≤ k - 2 := by omega
  have hm := Nat.mul_le_mul_left (3 * k + 2 - 4) hsub
  have hk2 : k - 2 + 2 = k := by omega
  have hn : 3 * k + 2 - 4 + 2 = 3 * k := by omega
  have hper : 4 * (3 * k + 2) - 4 = 12 * k + 4 := by omega
  rw [hper] at hcap
  nlinarith

/-- The fixed-map unused-hole bound excludes the minimal deep count when
there are no shallow carriers, without assuming `p=3`. -/
theorem missing_side_no_shallow_nonpure_ge {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hzero : (nextRingCarriers F).card = 0) :
    k ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent - (pureBoundaryCarriers F).card := by
  have hq := missing_side_preserved_card_le (by omega) F hacyc s hmissing
  have hholes := side_holes_add_roots (by omega) F s
  have hholesLower : 2 * k ≤ ((univ \ F).filter (OnOpenSide s)).card := by omega
  have hlayers := layers_add_side_holes_le_perimeter_add_nonpure (by omega) F hacyc hzero s
  have hcap := card_le_layers_without_nextRing_carriers (by omega) F hacyc
  rw [hzero, Nat.sub_zero] at hcap
  by_contra h
  have hd : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent - (pureBoundaryCarriers F).card ≤ k - 1 := by omega
  have hm := Nat.mul_le_mul_left (3 * k + 2 - 4) hd
  have hk1 : k - 1 + 1 = k := by omega
  have hn : 3 * k + 2 - 4 + 2 = 3 * k := by omega
  have hper : 4 * (3 * k + 2) - 4 = 12 * k + 4 := by omega
  rw [hper] at hlayers
  nlinarith

/-- A missing-side counterexample always needs at least `k` nonpure carriers.
With shallow carriers this follows from deep capacity; without them it follows
from the actual boundary-injection image loss. -/
theorem missing_side_nonpure_ge {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    k ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent - (pureBoundaryCarriers F).card := by
  by_cases hz : (nextRingCarriers F).card = 0
  · exact missing_side_no_shallow_nonpure_ge hk F hacyc s hmissing hf hz
  · have h := counterexample_deep_carriers_ge hk F hacyc hf
    omega

/-- If local geometry rules out `q=k`, the four-pure branch has a unique
remaining numerical profile: `q=k-1`, `r=k+4`, `c=1`, `W=3`, and `h<=1`.
This is a necessary condition, not a claim that such a configuration exists. -/
theorem four_pure_unsaturated_profile {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 4)
    (hq : (F.filter (OnOpenSide s)).card < k) :
    (F.filter (OnOpenSide s)).card = k - 1 ∧
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent = k + 4 ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent = 1 ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 4 ∧
      (nextRingCarriers F).card ≤ 1 := by
  have hnonpure := missing_side_nonpure_ge hk F hacyc s hmissing hf
  have hdeep := counterexample_deep_carriers_ge hk F hacyc hf
  have hslack := four_pure_missing_side_slack hk F hacyc s hmissing hf hp
  dsimp only at hslack
  omega

/-- Before the local endpoint analysis, the possible root counts have already
narrowed to `k-1` and `k`. -/
theorem four_pure_root_cases {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 4) :
    (F.filter (OnOpenSide s)).card = k - 1 ∨ (F.filter (OnOpenSide s)).card = k := by
  have hq := missing_side_preserved_card_le (by omega) F hacyc s hmissing
  have hr := missing_side_nonpure_ge hk F hacyc s hmissing hf
  have hslack := four_pure_missing_side_slack hk F hacyc s hmissing hf hp
  dsimp only at hslack
  omega

end GridGraphs.CarrierLayers.FourCarrier
