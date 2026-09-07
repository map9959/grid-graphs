import GridGraphs.Accounting.BoundaryFive.Rootless.PeelingGraphs
import GridGraphs.Accounting.BoundaryFive.CornerPacket.Annulus

/-! # Connectivity off the exceptional vertex, without an outer-tree model -/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph

theorem next_ring_notMem {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (v : GridVertex n n) (hv : IsNextRing v) : v ∉ F :=
  boundaryDeficiencySum_compl_eq_five_next_ring_notMem (by omega) F hacyc hb v
    hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2

/-- The only possible forced edge at w=(1,2) is the edge to z=(2,2). -/
theorem exception_edge {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (v : GridVertex n n)
    (he : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj
      (⟨1, by omega⟩, ⟨2, by omega⟩) v) :
    v = (⟨2, by omega⟩, ⟨2, by omega⟩) ∧ v ∈ F := by
  classical
  have hw : (⟨1, by omega⟩, ⟨2, by omega⟩) ∉ F := next_ring_notMem hn F hacyc hb _
    (by simp [IsNextRing]; omega)
  have hv : v ∈ F := he.2.resolve_left hw
  have hvr : ¬ IsNextRing v := fun h => next_ring_notMem hn F hacyc hb v h hv
  have hnot : ¬ (v.1.val = 0 ∧ v.2.val = 2) := by
    intro h
    have heq : v = (⟨0, by omega⟩, ⟨2, by omega⟩) := Prod.ext (Fin.ext h.1) (Fin.ext h.2)
    exact hh (heq ▸ hv)
  have ha := he.1
  simp only [gridGraph, adjacent, Fin.ext_iff] at ha
  dsimp at ha
  refine ⟨?_, hv⟩
  simp only [Prod.ext_iff, Fin.ext_iff]
  dsimp [IsNextRing] at hvr
  omega

theorem exception_isolate {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (hz : (⟨2, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    ∀ v, ¬ (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj
      (⟨1, by omega⟩, ⟨2, by omega⟩) v := by
  intro v he
  obtain ⟨heq, hv⟩ := exception_edge hn F hacyc hb hh v he
  exact hz (heq ▸ hv)

theorem annulus_forced_eq {n : Nat} (F : Finset (GridVertex n n)) :
    forcedEdgeGraph (CarrierLayers.Annulus.graph n) (↑(CarrierLayers.Annulus.selected F) : Set _) =
      (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).induce CarrierLayers.Annulus.Mem := by
  ext v w
  change ((gridGraph n n).Adj v.1 w.1 ∧
    (v ∈ CarrierLayers.Annulus.selected F ∨ w ∈ CarrierLayers.Annulus.selected F)) ↔ _
  simp only [CarrierLayers.Annulus.selected, mem_filter, mem_univ, true_and]
  rfl

/-- The cubic annulus budget gives at most two forced components at b=5.
No ambient component count, corner-hole orientation, or connectivity is used. -/
theorem annulus_components_le_two {n : Nat} (hn : 10 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5) :
    Nat.card ((forcedEdgeGraph (gridGraph n n) (↑F : Set _)).induce
      CarrierLayers.Annulus.Mem).ConnectedComponent ≤ 2 := by
  classical
  obtain ⟨hB, hE, hA⟩ := CornerPacket.boundary_five_annulus_occupancy (by omega) F hacyc hb
  have hlength := CarrierLayers.Annulus.selected_length_bound F hacyc
  rw [hA] at hlength
  have hr : 4 ≤ Fintype.card ((CarrierLayers.Annulus.graph n).induce
      (↑(CarrierLayers.Annulus.selected F) : Set _)).ConnectedComponent := by
    by_contra h
    have := Nat.mul_le_mul_left n (show Fintype.card ((CarrierLayers.Annulus.graph n).induce
      (↑(CarrierLayers.Annulus.selected F) : Set _)).ConnectedComponent ≤ 3 by omega)
    omega
  have hbudget := CarrierLayers.Annulus.component_budget (by omega) F hacyc
  rw [hB, hE] at hbudget
  have hcard : Nat.card (forcedEdgeGraph (CarrierLayers.Annulus.graph n)
      (↑(CarrierLayers.Annulus.selected F) : Set _)).ConnectedComponent ≤ 2 := by
    rw [Nat.card_eq_fintype_card]
    omega
  simpa only [annulus_forced_eq] using hcard

/-- Every two annulus vertices other than w are connected inside the actual
annulus forced graph. Its isolated w is retained in the component budget. -/
theorem annulus_reachable_off_exception {n : Nat} (hn : 10 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (x y : CarrierLayers.Annulus.Vertex n)
    (hx : x.1 ≠ (⟨1, by omega⟩, ⟨2, by omega⟩))
    (hy : y.1 ≠ (⟨1, by omega⟩, ⟨2, by omega⟩)) :
    ((forcedEdgeGraph (gridGraph n n) (↑F : Set _)).induce CarrierLayers.Annulus.Mem).Reachable x y := by
  classical
  let w : CarrierLayers.Annulus.Vertex n :=
    ⟨(⟨1, by omega⟩, ⟨2, by omega⟩), by simp [CarrierLayers.Annulus.Mem]⟩
  apply reachable_off_isolate _ (annulus_components_le_two hn F hacyc hb) w
    ?_ x y (fun he => hx (congrArg Subtype.val he)) (fun he => hy (congrArg Subtype.val he))
  intro v he
  have h := (exception_edge (by omega) F hacyc hb hh v.1 he).1
  have hv := v.2
  change CarrierLayers.Annulus.Mem v.1 at hv
  rw [h] at hv
  change 2 < 2 ∨ n ≤ 2 + 2 ∨ 2 < 2 ∨ n ≤ 2 + 2 at hv
  omega

end GridGraphs.BoundaryFive.Rootless
