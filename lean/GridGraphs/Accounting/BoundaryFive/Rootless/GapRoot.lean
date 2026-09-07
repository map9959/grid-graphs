import GridGraphs.Accounting.BoundaryFive.Rootless.Endpoint
import GridGraphs.Accounting.BoundaryFive.CornerPacket.Geometry

/-! # The exceptional deep corner is U at the c=2 endpoint

The local singleton argument assumes z is preserved, not c=1. Only the
perimeter gap is positioned; the other corner-hole choices stay free.
-/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph

theorem top_gap_mem_corner_no_neighbor {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (hz : (⟨2, by omega⟩, ⟨2, by omega⟩) ∈ F) :
    ∀ v, (gridGraph n n).Adj (⟨2, by omega⟩, ⟨2, by omega⟩) v → v ∉ F := by
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  let z : GridVertex n n := (⟨2, by omega⟩, ⟨2, by omega⟩)
  let a : GridVertex n n := (⟨2, by omega⟩, ⟨0, by omega⟩)
  let t : GridVertex n n := (⟨2, by omega⟩, ⟨1, by omega⟩)
  have hconn := perimeter_preconnected_of_top_gap (by omega) F hacyc hb ha hh
  have haF : a ∈ F := CornerPacket.boundary_mem_of_top_gap hn F hacyc hb hh a
    (by simp [a, IsGridBoundary]) (by simp [a, BoundarySix.Near]; omega)
    (by simp [a, Prod.ext_iff, Fin.ext_iff])
  have hat : H.Adj a t := ⟨by simp [a, t, gridGraph, adjacent], Or.inl haF⟩
  have htz : H.Adj t z := ⟨by simp [t, z, gridGraph, adjacent], Or.inr hz⟩
  have hright : (⟨2, by omega⟩, ⟨3, by omega⟩) ∉ F := by
    intro hy
    let y : GridVertex n n := (⟨2, by omega⟩, ⟨3, by omega⟩)
    let s : GridVertex n n := (⟨1, by omega⟩, ⟨3, by omega⟩)
    let b : GridVertex n n := (⟨0, by omega⟩, ⟨3, by omega⟩)
    have hbF : b ∈ F := CornerPacket.boundary_mem_of_top_gap hn F hacyc hb hh b
      (by simp [b, IsGridBoundary]) (by simp [b, BoundarySix.Near]; omega)
      (by simp [b, Prod.ext_iff, Fin.ext_iff])
    have hzy : H.Adj z y := ⟨by simp [z, y, gridGraph, adjacent], Or.inl hz⟩
    have hys : H.Adj y s := ⟨by simp [y, s, gridGraph, adjacent], Or.inl hy⟩
    have hsb : H.Adj s b := ⟨by simp [s, b, gridGraph, adjacent], Or.inr hbF⟩
    let p : H.Walk a b := .cons hat (.cons htz (.cons hzy (.cons hys (.cons hsb .nil))))
    have hp : p.IsPath := by
      simp [p, Walk.cons_isPath_iff, a, t, z, y, s, b, Prod.ext_iff, Fin.ext_iff]
    have hzb := CornerPacket.path_stays_in_connected_set H hacyc {v | IsGridBoundary v} hconn
      (by simp [a, IsGridBoundary]) (by simp [b, IsGridBoundary]) p hp (v := z) (by simp [p])
    simp [z, IsGridBoundary] at hzb
    omega
  have hdown : (⟨3, by omega⟩, ⟨2, by omega⟩) ∉ F := by
    intro hy
    let y : GridVertex n n := (⟨3, by omega⟩, ⟨2, by omega⟩)
    let s : GridVertex n n := (⟨3, by omega⟩, ⟨1, by omega⟩)
    let b : GridVertex n n := (⟨3, by omega⟩, ⟨0, by omega⟩)
    have hbF : b ∈ F := CornerPacket.boundary_mem_of_top_gap hn F hacyc hb hh b
      (by simp [b, IsGridBoundary]) (by simp [b, BoundarySix.Near]; omega)
      (by simp [b, Prod.ext_iff, Fin.ext_iff])
    have hzy : H.Adj z y := ⟨by simp [z, y, gridGraph, adjacent], Or.inl hz⟩
    have hys : H.Adj y s := ⟨by simp [y, s, gridGraph, adjacent], Or.inl hy⟩
    have hsb : H.Adj s b := ⟨by simp [s, b, gridGraph, adjacent], Or.inr hbF⟩
    let p : H.Walk a b := .cons hat (.cons htz (.cons hzy (.cons hys (.cons hsb .nil))))
    have hp : p.IsPath := by
      simp [p, Walk.cons_isPath_iff, a, t, z, y, s, b, Prod.ext_iff, Fin.ext_iff]
    have hzb := CornerPacket.path_stays_in_connected_set H hacyc {v | IsGridBoundary v} hconn
      (by simp [a, IsGridBoundary]) (by simp [b, IsGridBoundary]) p hp (v := z) (by simp [p])
    simp [z, IsGridBoundary] at hzb
    omega
  intro v hadj hv
  have hcoords := hadj
  simp only [gridGraph, adjacent, Fin.ext_iff] at hcoords
  dsimp at hcoords
  have hcases : v = (⟨1, by omega⟩, ⟨2, by omega⟩) ∨
      v = (⟨2, by omega⟩, ⟨1, by omega⟩) ∨
      v = (⟨2, by omega⟩, ⟨3, by omega⟩) ∨
      v = (⟨3, by omega⟩, ⟨2, by omega⟩) := by
    simp only [Prod.ext_iff, Fin.ext_iff]
    omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact boundaryDeficiencySum_compl_eq_five_next_ring_notMem (by omega) F hacyc hb _
      (by simp) (by simp; omega) (by simp) (by simp; omega) (by simp) hv
  · exact boundaryDeficiencySum_compl_eq_five_next_ring_notMem (by omega) F hacyc hb _
      (by simp) (by simp; omega) (by simp) (by simp; omega) (by simp) hv
  · exact hright hv
  · exact hdown hv

theorem top_gap_mem_corner_singleton {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (hz : (⟨2, by omega⟩, ⟨2, by omega⟩) ∈ F) :
    ∃ Z : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent,
      Z ∉ pureBoundaryCarriers F ∧ Z.supp.toFinset.card = 1 := by
  classical
  have hno := top_gap_mem_corner_no_neighbor hn F hacyc hb ha hh hz
  let z : (↑F : Set (GridVertex n n)) := ⟨(⟨2, by omega⟩, ⟨2, by omega⟩), hz⟩
  let G := (gridGraph n n).induce (↑F : Set _)
  let Z := G.connectedComponentMk z
  have hzZ : z ∈ Z.supp := rfl
  have heq (v : (↑F : Set (GridVertex n n))) (hv : v ∈ Z.supp) : v = z := by
    obtain ⟨p⟩ := Z.reachable_of_mem_supp hzZ hv
    cases p with
    | nil => rfl
    | @cons _ t _ h _ => exact (hno _ h t.2).elim
  refine ⟨Z, ?_, ?_⟩
  · intro hpure
    have hzb := (mem_filter.mp hpure).2 z hzZ
    simp [z, IsGridBoundary] at hzb
    omega
  · have hs : Z.supp.toFinset = {z} := by
      ext v
      simp only [Set.mem_toFinset, mem_singleton]
      exact ⟨heq v, fun h => h ▸ hzZ⟩
    rw [hs, card_singleton]

theorem top_gap_endpoint_corner_notMem {k : Nat} (hk : 7 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5)
    (hr : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).ConnectedComponent = k + 4)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    (⟨2, by omega⟩, ⟨2, by omega⟩) ∉ F := by
  intro hz
  obtain ⟨Z, hZ, hsize⟩ := top_gap_mem_corner_singleton (by omega) F hacyc hb ha hh hz
  exact current_endpoint_no_nonpure_singleton (by omega) hmod F hacyc hb hr hf Z hZ hsize

end GridGraphs.BoundaryFive.Rootless
