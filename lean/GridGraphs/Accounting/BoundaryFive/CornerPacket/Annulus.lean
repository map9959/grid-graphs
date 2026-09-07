import GridGraphs.Accounting.CarrierLayers.Annulus.Deficit
import GridGraphs.Accounting.BoundaryStratifiedCarrierBound

/-! # The full-rod budget at boundary deficiency five

This uses the physical annulus forest, including its isolates. Neither ambient
connectivity nor a prescribed endpoint profile is required.
-/

namespace GridGraphs.BoundaryFive.CornerPacket

open Finset SimpleGraph CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

/-- Boundary deficiency five fixes the annulus occupancy exactly. -/
theorem boundary_five_annulus_occupancy {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5) :
    (F.filter IsGridBoundary).card = 4 * n - 9 ∧
      (F.filter IsNextRing).card = 0 ∧ (selected F).card = 4 * n - 9 := by
  classical
  have hholes := (boundaryDeficiencySum_compl_eq_five_corners_and_card
    (by omega) F hacyc hb).2
  have hall := BoundaryFiveConstruction.boundary_card (by omega : 7 ≤ n)
  have hpartition : F.filter IsGridBoundary ∪ (univ \ F).filter IsGridBoundary =
      ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset := by
    ext v
    by_cases hv : v ∈ F <;> simp [hv]
  have hdisj : Disjoint (F.filter IsGridBoundary) ((univ \ F).filter IsGridBoundary) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp (mem_filter.mp hw).1).2 (mem_filter.mp hv).1
  have h := card_union_of_disjoint hdisj
  rw [hpartition, hall, hholes] at h
  have hB : (F.filter IsGridBoundary).card = 4 * n - 9 := by omega
  have hE : (F.filter IsNextRing).card = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hvF, hvr⟩ := mem_filter.mp hv
    have hr := hvr
    dsimp [IsNextRing] at hr
    exact boundaryDeficiencySum_compl_eq_five_next_ring_notMem (by omega) F hacyc hb v
      (by omega) (by omega) (by omega) (by omega) (by omega) hvF
  refine ⟨hB, hE, ?_⟩
  rw [selected_card_layers (by omega), hB, hE, Nat.add_zero]

/-- At most one full deep rod is possible at boundary deficiency five, for
every side at least ten. No all-covered, `c=1`, or endpoint assumption is used. -/
theorem boundary_five_fullCarriers_le_one {n : Nat} (hn : 10 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5) :
    (fullCarriers F).card ≤ 1 := by
  obtain ⟨hB, hE, hA⟩ := boundary_five_annulus_occupancy (by omega) F hacyc hb
  have hlength := selected_length_bound F hacyc
  rw [hA] at hlength
  have hr : 4 ≤ Fintype.card
      ((graph n).induce (↑(selected F) : Set _)).ConnectedComponent := by
    by_contra h
    have hmul := Nat.mul_le_mul_left n (show Fintype.card
      ((graph n).induce (↑(selected F) : Set _)).ConnectedComponent ≤ 3 by omega)
    omega
  have hbudget := component_budget (by omega) F hacyc
  rw [hB, hE] at hbudget
  have hbridge := fullCarriers_card_add_one_le_components (by omega) F hacyc
  omega

end GridGraphs.BoundaryFive.CornerPacket
