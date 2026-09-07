import GridGraphs.Accounting.CarrierLayers.Annulus.Counterexamples
import GridGraphs.Accounting.CarrierLayers.MissingSideSharp
import GridGraphs.Accounting.BoundaryFive.Upper

/-! # Annulus counterexample budgets and conditional upper bounds

Two excess vertices force four pure carriers globally. The annulus deep-carrier
gain then gives `r >= k+4` and `b+c+3e <= 2k+8`. This improves the entire
`b >= 7` branch, not the unconditional numerical upper bound. At the current
upper endpoint with `k = 1 mod 3`, three necessary profiles remain; none is
excluded here.
-/

namespace GridGraphs.CarrierLayers.Annulus

open Finset SimpleGraph

/-- The annulus carrier gain is global at two excess, without a prescribed
pure-carrier count, boundary budget, or coverage hypothesis. -/
theorem two_excess_components_ge {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + 2 ≤ F.card) :
    k + 4 ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent := by
  exact covered_counterexample_components_ge hk F hacyc (by omega)
    (residueTwo_all_open_sides_covered_of_two_excess hk F hacyc hf)

/-- With four pure carriers the stronger budget already holds at one excess. -/
theorem counterexample_budget_of_four_pure {k excess : Nat}
    (hk : 5 ≤ k) (hexcess : 1 ≤ excess)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + excess ≤ F.card)
    (hp : 4 ≤ (pureBoundaryCarriers F).card) :
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) +
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent + 3 * excess ≤ 2 * k + 8 := by
  have hr := counterexample_components_ge_of_four_pure hk F hacyc (by omega) hp
  change k + 4 ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
    (↑F : Set _)).ConnectedComponent at hr
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  nlinarith

/-- Global two-excess budget `b+c+3e <= 2k+8`. -/
theorem two_excess_counterexample_budget {k excess : Nat}
    (hk : 5 ≤ k) (hexcess : 2 ≤ excess)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + excess ≤ F.card) :
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) +
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent + 3 * excess ≤ 2 * k + 8 := by
  obtain ⟨_, _, _, hp⟩ := residueTwo_four_distinct_pure_carriers_of_two_excess
    hk F hacyc (by omega)
  exact counterexample_budget_of_four_pure hk (by omega) F hacyc hf hp

/-- A sharper bound on the entire `b >= 7` branch, without a score assumption.
This does not change the unconditional upper bound. -/
theorem card_le_of_boundaryDeficiency_ge_seven {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : 7 ≤ boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F)) :
    F.card ≤ 3 * k ^ 2 + 7 * k + (2 * k) / 3 := by
  by_contra h
  have hf : 3 * k ^ 2 + 7 * k + ((2 * k) / 3 + 1) ≤ F.card := by omega
  have he : 2 ≤ (2 * k) / 3 + 1 := by omega
  have hbudget := two_excess_counterexample_budget hk he F hacyc hf
  let : Nonempty (GridVertex (3 * k + 2) (3 * k + 2)) :=
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hc := one_le_card_connectedComponent
    (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _))
  omega

/-- At width 23, boundary deficiency at least seven gives the bound 200. -/
theorem square23_card_le_two_hundred_of_boundaryDeficiency_ge_seven
    (F : Finset (GridVertex 23 23))
    (hacyc : (forcedEdgeGraph (gridGraph 23 23) (↑F : Set _)).IsAcyclic)
    (hb : 7 ≤ boundaryDeficiencySum 23 23 (univ \ F)) :
    F.card ≤ 200 := by
  simpa using card_le_of_boundaryDeficiency_ge_seven (k := 7) (by omega) F hacyc hb

/-- At or above the current unconditional upper endpoint for `k = 1 mod 3`,
size is exact and the only possible `(r,c,b)` profiles are
`(k+5,1,5)`, `(k+4,2,5)`, and `(k+4,1,6)`. These are necessary conditions,
not existence statements or exclusions of any of the three branches. -/
theorem current_upper_endpoint_profiles {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card) :
    let r := Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent
    let c := Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent
    let b := boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F)
    F.card = 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ∧
      r + c + b = k + 11 ∧
      ((r = k + 5 ∧ c = 1 ∧ b = 5) ∨
       (r = k + 4 ∧ c = 2 ∧ b = 5) ∨
       (r = k + 4 ∧ c = 1 ∧ b = 6)) := by
  dsimp only
  have hupper := BoundaryFive.forced_card_le_residueTwo_bound hk F hacyc
  have hfeq := Nat.le_antisymm hupper hf
  have he : 5 ≤ (2 * k + 1) / 3 := by omega
  have hquot : 3 * ((2 * k + 1) / 3) = 2 * k + 1 := by omega
  have hr := two_excess_components_ge hk F hacyc (by omega)
  have hb := five_le_boundaryDeficiencySum_compl (by omega) F hacyc
  let : Nonempty (GridVertex (3 * k + 2) (3 * k + 2)) :=
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hc := one_le_card_connectedComponent
    (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _))
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  have hbudget :
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent +
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = k + 11 := by
    rw [hfeq] at hledger
    nlinarith
  exact ⟨hfeq, hbudget, by omega⟩

end GridGraphs.CarrierLayers.Annulus
