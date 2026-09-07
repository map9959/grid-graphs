import GridGraphs.Accounting.CarrierLayers.CoveredGlobalMissingSides
import GridGraphs.Accounting.BoundarySix.Upper

/-!
# Global excess budgets and the remaining upper-endpoint profile

The global induced-carrier gain tightens the excess budget by one. This
improves the numerical upper bound when boundary deficiency is at least six,
not unconditionally. At k = 2 modulo 3, attaining the old global upper bound
forces deficiency five and a connected forced graph.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

/-- The global `r >= k+3` bound saves one budget unit for arbitrary positive
excess, without a boundary-deficiency or side-coverage hypothesis. -/
theorem residueTwo_global_counterexample_budget {k excess : Nat}
    (hk : 5 ≤ k) (hexcess : 1 ≤ excess)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + excess ≤ F.card) :
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) +
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent + 3 * excess ≤ 2 * k + 9 := by
  have hr := stable_counterexample_induced_components_ge hk F hacyc (by omega)
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  nlinarith

/-- A sharper numerical bound on the entire `b >= 6` branch. The exceptional
`b = 6` case uses the existing two-excess small-boundary carrier gain. -/
theorem residueTwo_card_le_of_boundaryDeficiency_ge_six {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : 6 ≤ boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F)) :
    F.card ≤ 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 := by
  by_contra h
  have hf : 3 * k ^ 2 + 7 * k + ((2 * k + 1) / 3 + 1) ≤ F.card := by omega
  have he : 2 ≤ (2 * k + 1) / 3 + 1 := by omega
  let : Nonempty (GridVertex (3 * k + 2) (3 * k + 2)) :=
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hc := one_le_card_connectedComponent
    (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _))
  by_cases hb6 : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) ≤ 6
  · have hprofile := (residueTwo_small_boundary_counterexample_profile hk
      (by omega) F hacyc hb6 hf).2
    rw [Nat.min_eq_right he] at hprofile
    omega
  · have hprofile := residueTwo_global_counterexample_budget hk (by omega) F hacyc hf
    omega

/-- When `k = 2 mod 3`, a feasible set at or above the old unconditional
upper endpoint has exactly that size and profile `(r,c,b) = (k+4,1,5)`.
This classifies the remaining obstruction; it does not exclude it. -/
theorem residueTwo_old_upper_endpoint_profile {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 2)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 2) / 3 ≤ F.card) :
    F.card = 3 * k ^ 2 + 7 * k + (2 * k + 2) / 3 ∧
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent = k + 4 ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent = 1 ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5 := by
  have hupper := forced_card_le_boundary_six_residueTwo_bound hk F hacyc
  have hfeq := Nat.le_antisymm hupper hf
  have hquot : 3 * ((2 * k + 2) / 3) = 2 * k + 2 := by omega
  have hbmin := five_le_boundaryDeficiencySum_compl (by omega) F hacyc
  have hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5 := by
    by_contra h
    have hbranch := residueTwo_card_le_of_boundaryDeficiency_ge_six hk F hacyc (by omega)
    omega
  have he : 2 ≤ (2 * k + 2) / 3 := by omega
  have hr := (residueTwo_small_boundary_counterexample_profile hk
    (by omega) F hacyc (by omega) hf).1
  rw [Nat.min_eq_right he] at hr
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
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = k + 10 := by
    rw [hfeq] at hledger
    nlinarith
  exact ⟨hfeq, by omega, by omega, hb⟩

end GridGraphs.CarrierLayers
