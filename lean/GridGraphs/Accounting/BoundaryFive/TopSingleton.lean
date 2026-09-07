import GridGraphs.Accounting.BoundaryFive.GapPosition
import GridGraphs.Accounting.BoundaryFive.Inward
import GridGraphs.Accounting.BoundaryFive.Perimeter
import GridGraphs.Accounting.BoundaryFive.Endpoint

/-! # The singleton below an oriented top gap

Only the gap is positioned. The other corner-hole orientations remain free.
An explicit off-boundary path contradicts the unique boundary-only path in
the ambient forest; no full outer-frame construction is needed.
-/

namespace GridGraphs.BoundaryFive

open Finset SimpleGraph

private theorem path_stays_in_boundary {n : Nat}
    (H : SimpleGraph (GridVertex n n)) (hacyc : H.IsAcyclic)
    (hconn : (H.induce {v | IsGridBoundary v}).Preconnected)
    {a b : GridVertex n n} (ha : IsGridBoundary a) (hb : IsGridBoundary b)
    (p : H.Walk a b) (hp : p.IsPath) {v : GridVertex n n} (hv : v ∈ p.support) :
    IsGridBoundary v := by
  obtain ⟨q, hq⟩ := (hconn ⟨a, ha⟩ ⟨b, hb⟩).exists_isPath
  let f := (Embedding.induce (G := H) {v | IsGridBoundary v}).toHom
  have hmap : (q.map f).IsPath := hq.map (by
    intro x y h
    exact Subtype.ext h)
  have he := (hacyc.subsingleton_path a b).elim ⟨p, hp⟩ ⟨q.map f, hmap⟩
  have hs : p.support = (q.map f).support := congrArg (fun r : H.Path a b => r.val.support) he
  rw [hs, Walk.support_map, List.mem_map] at hv
  obtain ⟨w, _, hw⟩ := hv
  exact hw ▸ w.2

/-- The vertex `(2,2)` is preserved and has no preserved grid neighbor when
the unique gap is at `(0,1)-(0,2)`. No other hole orientation is assumed. -/
theorem top_gap_preserved_isolated {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hb' : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    (⟨2, by omega⟩, ⟨2, by omega⟩) ∈ F ∧
      ∀ v, (gridGraph n n).Adj (⟨2, by omega⟩, ⟨2, by omega⟩) v → v ∉ F := by
  classical
  let z : GridVertex n n := (⟨2, by omega⟩, ⟨2, by omega⟩)
  let a : GridVertex n n := (⟨2, by omega⟩, ⟨0, by omega⟩)
  let t : GridVertex n n := (⟨2, by omega⟩, ⟨1, by omega⟩)
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  have hz : z ∈ F := top_hole_forces_deep (by omega) F hacyc hb hc 2
    (by omega) (by omega) hb'
  have hconn := perimeter_preconnected_of_top_gap (by omega) F hacyc hb ha hb'
  obtain ⟨Q, u, _, _, hholes, hnear, _, _⟩ := holes_eq_insert_second hn F hacyc hb
  have hextra : (⟨0, by omega⟩, ⟨2, by omega⟩) = u := by
    have hm : (⟨0, by omega⟩, ⟨2, by omega⟩) ∈ insert u Q := by
      rw [← hholes]
      simp [hb', IsGridBoundary]
    rcases mem_insert.mp hm with h | h
    · exact h
    · have hn' := hnear _ h
      simp only [BoundarySix.Near] at hn'
      omega
  have forced (v : GridVertex n n) (hvb : IsGridBoundary v)
      (hvn : ¬ BoundarySix.Near v)
      (hne : v ≠ (⟨0, by omega⟩, ⟨2, by omega⟩)) : v ∈ F := by
    by_contra hv
    have hm : v ∈ insert u Q := by rw [← hholes]; simp [hv, hvb]
    rcases mem_insert.mp hm with h | h
    · exact hne (h.trans hextra.symm)
    · exact hvn (hnear v h)
  have haF : a ∈ F := forced a (by simp [a, IsGridBoundary])
    (by simp [a, BoundarySix.Near]; omega) (by simp [a, Prod.ext_iff, Fin.ext_iff])
  have hat : H.Adj a t := ⟨by simp [a, t, gridGraph, adjacent], Or.inl haF⟩
  have htz : H.Adj t z := ⟨by simp [t, z, gridGraph, adjacent], Or.inr hz⟩
  have hright : (⟨2, by omega⟩, ⟨3, by omega⟩) ∉ F := by
    intro hy
    let y : GridVertex n n := (⟨2, by omega⟩, ⟨3, by omega⟩)
    let s : GridVertex n n := (⟨1, by omega⟩, ⟨3, by omega⟩)
    let b : GridVertex n n := (⟨0, by omega⟩, ⟨3, by omega⟩)
    have hbF : b ∈ F := forced b (by simp [b, IsGridBoundary])
      (by simp [b, BoundarySix.Near]; omega) (by simp [b, Prod.ext_iff, Fin.ext_iff])
    have hzy : H.Adj z y := ⟨by simp [z, y, gridGraph, adjacent], Or.inl hz⟩
    have hys : H.Adj y s := ⟨by simp [y, s, gridGraph, adjacent], Or.inl hy⟩
    have hsb : H.Adj s b := ⟨by simp [s, b, gridGraph, adjacent], Or.inr hbF⟩
    let p : H.Walk a b := .cons hat (.cons htz (.cons hzy (.cons hys (.cons hsb .nil))))
    have hp : p.IsPath := by
      simp [p, Walk.cons_isPath_iff, a, t, z, y, s, b, Prod.ext_iff, Fin.ext_iff]
    have hzb := path_stays_in_boundary H hacyc hconn
      (by simp [a, IsGridBoundary]) (by simp [b, IsGridBoundary]) p hp
      (v := z) (by simp [p])
    simp [z, IsGridBoundary] at hzb
    omega
  have hdown : (⟨3, by omega⟩, ⟨2, by omega⟩) ∉ F := by
    intro hy
    let y : GridVertex n n := (⟨3, by omega⟩, ⟨2, by omega⟩)
    let s : GridVertex n n := (⟨3, by omega⟩, ⟨1, by omega⟩)
    let b : GridVertex n n := (⟨3, by omega⟩, ⟨0, by omega⟩)
    have hbF : b ∈ F := forced b (by simp [b, IsGridBoundary])
      (by simp [b, BoundarySix.Near]; omega) (by simp [b, Prod.ext_iff, Fin.ext_iff])
    have hzy : H.Adj z y := ⟨by simp [z, y, gridGraph, adjacent], Or.inl hz⟩
    have hys : H.Adj y s := ⟨by simp [y, s, gridGraph, adjacent], Or.inl hy⟩
    have hsb : H.Adj s b := ⟨by simp [s, b, gridGraph, adjacent], Or.inr hbF⟩
    let p : H.Walk a b := .cons hat (.cons htz (.cons hzy (.cons hys (.cons hsb .nil))))
    have hp : p.IsPath := by
      simp [p, Walk.cons_isPath_iff, a, t, z, y, s, b, Prod.ext_iff, Fin.ext_iff]
    have hzb := path_stays_in_boundary H hacyc hconn
      (by simp [a, IsGridBoundary]) (by simp [b, IsGridBoundary]) p hp
      (v := z) (by simp [p])
    simp [z, IsGridBoundary] at hzb
    omega
  refine ⟨hz, ?_⟩
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

/-- The oriented gap supplies an actual nonpure singleton induced carrier,
supported exactly at `(2,2)`. -/
theorem top_gap_singleton {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hb' : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    ∃ Z : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent,
      Z ∉ pureBoundaryCarriers F ∧ Z.supp.toFinset.card = 1 ∧
      ∀ v ∈ Z.supp, v.1 = (⟨2, by omega⟩, ⟨2, by omega⟩) := by
  classical
  obtain ⟨hz, hiso⟩ := top_gap_preserved_isolated hn F hacyc hb hc ha hb'
  let z : (↑F : Set (GridVertex n n)) := ⟨(⟨2, by omega⟩, ⟨2, by omega⟩), hz⟩
  let G := (gridGraph n n).induce (↑F : Set _)
  let Z := G.connectedComponentMk z
  have hno (v : (↑F : Set (GridVertex n n))) (h : G.Adj z v) : False :=
    hiso v.1 h v.2
  have hzZ : z ∈ Z.supp := by simp [Z, ConnectedComponent.mem_supp_iff]
  have heq (v : (↑F : Set (GridVertex n n))) (hv : v ∈ Z.supp) : v = z := by
    obtain ⟨p⟩ := Z.reachable_of_mem_supp hzZ hv
    cases p with
    | nil => rfl
    | cons h p => exact (hno _ h).elim
  refine ⟨Z, ?_, ?_, fun v hv => congrArg Subtype.val (heq v hv)⟩
  · intro hpure
    have hzb := (mem_filter.mp hpure).2 z hzZ
    simp [z, IsGridBoundary] at hzb
    omega
  · have hs : Z.supp.toFinset = {z} := by
      ext v
      simp only [Set.mem_toFinset, mem_singleton]
      exact ⟨heq v, fun h => h ▸ hzZ⟩
    rw [hs, card_singleton]

/-- The old upper endpoint is impossible with the gap in the top position.
Boundary deficiency five and ambient connectivity follow from the endpoint
profile rather than being additional hypotheses. -/
theorem top_gap_old_upper_endpoint_false {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 2)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 2) / 3 ≤ F.card)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hb' : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) : False := by
  obtain ⟨_, _, hc, hb⟩ :=
    CarrierLayers.residueTwo_old_upper_endpoint_profile hk hmod F hacyc hf
  obtain ⟨Z, hZ, hsize, _⟩ := top_gap_singleton (by omega) F hacyc hb hc ha hb'
  exact old_upper_endpoint_no_nonpure_singleton hk hmod F hacyc hf Z hZ hsize

end GridGraphs.BoundaryFive
