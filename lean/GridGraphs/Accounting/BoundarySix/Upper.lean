import GridGraphs.Accounting.BoundarySix.CarrierBound
import GridGraphs.Accounting.ResidueTwoCounterexampleProfile

/-!
# A residue-two upper bound from the boundary-six refinement

The proof covers every feasible set: low boundary cost forces extra carriers,
while high boundary cost pays directly through the exact component ledger.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The first two excess vertices each force an additional carrier when b<=6. -/
theorem residueTwo_small_boundary_counterexample_profile {k excess : Nat}
    (hk : 5 ≤ k) (hexcess : 1 ≤ excess)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) ≤ 6)
    (hcard : 3 * k ^ 2 + 7 * k + excess ≤ F.card) :
    k + 2 + min excess 2 ≤ Fintype.card
      ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).ConnectedComponent ∧
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) +
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent + 3 * excess + min excess 2 ≤ 2 * k + 10 := by
  classical
  have hlength := forced_card_le_small_boundary_components (by omega) F hacyc hb
  have hcarriers : k + 2 + min excess 2 ≤ Fintype.card
      ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).ConnectedComponent := by
    by_contra h
    have hsmall : Fintype.card
        ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).ConnectedComponent ≤
          k + 1 + min excess 2 := by omega
    have hscaled := Nat.mul_le_mul_left (3 * k + 2 - 4) hsmall
    have hsub : 3 * k + 2 - 4 + 2 = 3 * k := by omega
    by_cases he : 2 ≤ excess
    · rw [Nat.min_eq_right he] at hscaled
      nlinarith
    · have hmin : min excess 2 = 1 := by omega
      rw [hmin] at hscaled
      nlinarith
  refine ⟨hcarriers, ?_⟩
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  nlinarith

/-- All feasible residue-two sets obey the improved polynomial bound. -/
theorem forced_card_le_boundary_six_residueTwo_bound {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) :
    F.card ≤ 3 * k ^ 2 + 7 * k + (2 * k + 2) / 3 := by
  classical
  by_contra h
  have hcard : 3 * k ^ 2 + 7 * k + ((2 * k + 2) / 3 + 1) ≤ F.card := by omega
  have hboundary := five_le_boundaryDeficiencySum_compl (by omega) F hacyc
  have hcomponent : 1 ≤ Fintype.card
      (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).connectedComponentMk (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  by_cases hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) ≤ 6
  · have hprofile := (residueTwo_small_boundary_counterexample_profile hk
      (by omega) F hacyc hb hcard).2
    omega
  · have hprofile := (residueTwo_counterexample_profile (by omega)
      (by omega) F hacyc hcard).2
    omega

/-- Unconditional stable-range upper bound, not restricted to boundary-six sets. -/
theorem maxPreserved_residueTwo_le_boundary_six_refinement {k : Nat} (hk : 5 ≤ k) :
    maxPreserved (3 * k + 2) (3 * k + 2) ≤
      3 * k ^ 2 + 7 * k + (2 * k + 2) / 3 := by
  classical
  rw [maxPreserved_eq_maxForcedAcyclic (by omega) (by omega)]
  unfold maxForcedAcyclic
  apply Finset.sup_le
  intro F hF
  exact forced_card_le_boundary_six_residueTwo_bound hk F (mem_acyclicForcedSets.mp hF)

end GridGraphs
