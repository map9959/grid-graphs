import GridGraphs.Accounting.BoundarySix.Balance
import GridGraphs.Accounting.CarrierLayerBound
import GridGraphs.Accounting.BoundaryStratifiedCarrierBound

/-! # Carrier capacity with at most six boundary-deficiency units -/

namespace GridGraphs

open Finset SimpleGraph

/-- Four pure boundary carriers are still necessary at deficiency six. The
single possible next-ring vertex is charged only once in the global layer bound. -/
theorem forced_card_le_boundary_six_components {n : Nat} (hn : 12 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6) :
    F.card ≤ (n - 4) *
      Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent + 7 := by
  classical
  have hboundary := forced_boundary_card_le_pureBoundaryCarriers_add_nextRing
    (by omega) F hacyc
  have hlayers := forced_card_le_boundary_add_nextRing_add_nonpure_carriers
    (by omega) F hacyc
  have hring := boundaryDeficiencySum_compl_eq_six_next_ring_card_le_one
    (by omega) F hacyc hb
  obtain ⟨hlower, hupper⟩ := boundaryDeficiencySum_compl_eq_six_boundary_count_bounds
    (by omega) F hacyc hb
  have hfour : 4 ≤ (pureBoundaryCarriers F).card := by
    by_contra h
    have hp : (pureBoundaryCarriers F).card ≤ 3 := by omega
    have hscaled := Nat.mul_le_mul_left n hp
    omega
  have hp_le := pureBoundaryCarriers_card_le F
  have hsub := Nat.sub_add_cancel hp_le
  have hscaled := congrArg (fun a : Nat => (n - 4) * a) hsub
  have hfourmul := Nat.mul_le_mul_left (n - 4) hfour
  have hnsub : n - 4 + 4 = n := by omega
  have hboundarysub : 4 * n - 9 + 9 = 4 * n := by omega
  nlinarith

/-- A common refined estimate for both low-boundary-cost branches. -/
theorem forced_card_le_small_boundary_components {n : Nat} (hn : 12 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) ≤ 6) :
    F.card ≤ (n - 4) *
      Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent + 7 := by
  have hmin := five_le_boundaryDeficiencySum_compl (by omega) F hacyc
  have hcases : boundaryDeficiencySum n n (univ \ F) = 5 ∨
      boundaryDeficiencySum n n (univ \ F) = 6 := by omega
  rcases hcases with hfive | hsix
  · exact forced_card_le_boundary_stratified_components (by omega) F hacyc hfive
  · exact forced_card_le_boundary_six_components hn F hacyc hsix

end GridGraphs
