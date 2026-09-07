import GridGraphs.Accounting.CarrierLayers.Annulus.Deficit
import GridGraphs.Accounting.CarrierLayers.CoveredGlobalMissingSides

/-! # Global deep-carrier gain in stable counterexamples

At `n = 3k+2`, a counterexample with at most `k-1` actual deep carriers would
have `K+D <= 5`. The physical annulus inequality then gives `r <= 5`, contrary
to the existing global `r >= k+3`. Four pure carriers consequently force
`r >= k+4`, including for one-excess counterexamples with all sides covered.
-/

namespace GridGraphs.CarrierLayers.Annulus

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- Every stable counterexample has at least `k` actual deep carriers.
There is no boundary-deficiency, pure-carrier, or side-coverage assumption. -/
theorem counterexample_deep_carriers_ge {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    k ≤ Fintype.card (Carrier F) -
      (pureBoundaryCarriers F).card - (nextRingCarriers F).card := by
  let r := Fintype.card (Carrier F)
  let d := r - (pureBoundaryCarriers F).card - (nextRingCarriers F).card
  let K := 12 * k + 4 - ((F.filter IsGridBoundary).card + (F.filter IsNextRing).card)
  let D := (3 * k - 2) * d -
    (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card
  have hn : 3 * k + 2 - 4 = 3 * k - 2 := by omega
  have hper : 4 * (3 * k + 2) - 4 = 12 * k + 4 := by omega
  have hphysical : F.card + K + D = 12 * k + 4 + (3 * k - 2) * d := by
    simpa only [K, D, d, r, hn, hper] using
      (physical_deficit_identity (by omega) F hacyc).2.2
  have hbridge : r + 5 ≤ 2 * K + D := by
    simpa only [K, D, d, r, hn, hper, Nat.sub_sub] using
      components_add_five_le_twice_loss_add_deficit (by omega) F hacyc
  have hr : k + 3 ≤ r := stable_counterexample_induced_components_ge hk F hacyc hf
  by_contra h
  have hd : d ≤ k - 1 := by change ¬ k ≤ d at h; omega
  have hm := Nat.mul_le_mul_left (3 * k - 2) hd
  have he : 12 * k + 4 + (3 * k - 2) * (k - 1) = 3 * k ^ 2 + 7 * k + 6 := by
    have hk1 : k - 1 + 1 = k := by omega
    have hk2 : 3 * k - 2 + 2 = 3 * k := by omega
    nlinarith
  have hbudget : K + D ≤ 5 := by omega
  omega

/-- Four or more pure carriers force the improved induced count in every
stable counterexample, already at one excess. -/
theorem counterexample_components_ge_of_four_pure {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : 4 ≤ (pureBoundaryCarriers F).card) :
    k + 4 ≤ Fintype.card (Carrier F) := by
  have hd := counterexample_deep_carriers_ge hk F hacyc hf
  omega

/-- All four covered open sides give `r >= k+4`, with no small-boundary
assumption and no need to strengthen one excess to two excess. -/
theorem covered_counterexample_components_ge {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hcovered : ∀ s : Fin 4, ∃ C ∈ pureBoundaryCarriers F, ∃ v ∈ C.supp,
      OnOpenSide s v.val) :
    k + 4 ≤ Fintype.card (Carrier F) := by
  have hp := covered_sides_card_le_pure_carriers (by omega) F hacyc
    (univ : Finset (Fin 4)) (fun s _ => hcovered s)
  simp only [card_univ, Fintype.card_fin] at hp
  exact counterexample_components_ge_of_four_pure hk F hacyc hf hp

end GridGraphs.CarrierLayers.Annulus
