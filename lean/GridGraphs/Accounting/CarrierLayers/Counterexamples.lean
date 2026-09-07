import GridGraphs.Accounting.CarrierLayers.NextRingInjection
import GridGraphs.Accounting.CarrierLayers.RadialSide
import GridGraphs.Accounting.ResidueTwoCounterexampleProfile

/-! # Global pure-boundary-carrier reduction for stable counterexamples -/

namespace GridGraphs

open Finset SimpleGraph

/-- Every stable counterexample at `k ≥ 7` has at least three pure boundary
carriers, with no assumption on its boundary deficiency. -/
theorem residueTwo_stable_counterexample_three_le_pureBoundaryCarriers {k : Nat}
    (hk : 7 ≤ k) (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hcard : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    3 ≤ (pureBoundaryCarriers F).card := by
  classical
  have hbudget := residueTwo_stable_counterexample_budget (by omega) F hacyc hcard
  let : Nonempty (GridVertex (3 * k + 2) (3 * k + 2)) :=
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hc := one_le_card_connectedComponent
    (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _))
  have hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) ≤
      2 * k + 6 := by omega
  have hp := perimeter_le_pureBoundaryCarriers_add_twice_boundaryDeficiency
    (by omega) F hacyc
  by_contra h
  have hsmall : (pureBoundaryCarriers F).card ≤ 2 := by omega
  have hscaled := Nat.mul_le_mul_left (3 * k + 2) hsmall
  omega

/-- Every stable counterexample is in the near-sharp three-carrier branch or
has at least four pure boundary carriers. No boundary deficiency is prescribed. -/
theorem residueTwo_stable_counterexample_pure_boundary_cases {k : Nat}
    (hk : 7 ≤ k) (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hcard : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    ((pureBoundaryCarriers F).card = 3 ∧ F.card ≤ 3 * k ^ 2 + 7 * k + 2 ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent ≤ 5 ∧
      k + 2 ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent ∧
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent ≤ k + 6) ∨
    4 ≤ (pureBoundaryCarriers F).card := by
  by_cases hp : 4 ≤ (pureBoundaryCarriers F).card
  · exact Or.inr hp
  · have hthree := residueTwo_stable_counterexample_three_le_pureBoundaryCarriers
      hk F hacyc hcard
    have hle : (pureBoundaryCarriers F).card ≤ 3 := by omega
    have hprofile := residueTwo_counterexample_profile_of_pure_carriers_le_three
      (by omega) F hacyc hle hcard
    exact Or.inl ⟨by omega,
      residueTwo_card_le_target_add_two_of_pure_carriers_le_three (by omega) F hacyc hle,
      hprofile⟩

/-- Two excess vertices in the at-most-three-pure-carriers branch leave only
one spare budget unit, hence exactly three possible numerical profiles. -/
theorem residueTwo_two_excess_three_carrier_profiles {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hcard : 3 * k ^ 2 + 7 * k + 2 ≤ F.card) :
    let r := Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent
    let c := Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent
    let b := boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F)
    F.card = 3 * k ^ 2 + 7 * k + 2 ∧
      ((r = k + 2 ∧ c = 1 ∧ b = 2 * k + 3) ∨
       (r = k + 3 ∧ c = 1 ∧ b = 2 * k + 2) ∨
       (r = k + 2 ∧ c = 2 ∧ b = 2 * k + 2)) := by
  classical
  dsimp only
  have hcardEq := Nat.le_antisymm
    (residueTwo_card_le_target_add_two_of_pure_carriers_le_three hk F hacyc hp) hcard
  have hr := (residueTwo_counterexample_profile (by omega) (by omega : 1 ≤ 2)
    F hacyc hcard).1
  have hb := two_mul_add_two_le_boundaryDeficiencySum_of_pure_carriers_le_three
    hk F hacyc hp
  have hc : 1 ≤ Fintype.card (forcedEdgeGraph
      (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).connectedComponentMk (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  have hbudget :
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent +
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 3 * k + 6 := by
    nlinarith
  exact ⟨hcardEq, by omega⟩

end GridGraphs
