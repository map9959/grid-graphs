import GridGraphs.Accounting.BoundarySix.Connected.Annulus
import GridGraphs.Accounting.BoundarySix.Connected.RingPosition

/-! # The second-position inward extension makes a physical cycle

The connected forced annulus includes all annulus vertices, including vertices
not in the selected set. An outside vertex cannot have two forced neighbors in
that annulus. This excludes side position two, but not side position three.
-/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

/-- Two physical forced edges through one outside vertex would give a second
path between vertices already connected inside the annulus. -/
theorem outside_two_annulus_neighbors_false {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hc : Fintype.card (forcedEdgeGraph (graph n)
      (↑(selected F) : Set _)).ConnectedComponent = 1)
    {a b z : GridVertex n n} (ha : Mem a) (hb : Mem b) (hz : ¬ Mem z)
    (hab : a ≠ b)
    (haz : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj a z)
    (hzb : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj z b) : False := by
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  let A := forcedEdgeGraph (graph n) (↑(selected F) : Set _)
  have : Subsingleton A.ConnectedComponent := Fintype.card_le_one_iff_subsingleton.mp hc.le
  have hconn : A.Preconnected := fun x y => ConnectedComponent.exact (Subsingleton.elim _ _)
  obtain ⟨q, hq⟩ := (hconn ⟨a, ha⟩ ⟨b, hb⟩).exists_isPath
  let inc : A →g H :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y h
        refine ⟨h.1, ?_⟩
        simpa only [selected, mem_filter, mem_univ, true_and, mem_coe] using h.2 }
  let p : H.Walk a b := .cons haz (.cons hzb .nil)
  have hp : p.IsPath := by
    simp [p, Walk.cons_isPath_iff, hab, haz.ne, hzb.ne]
  have hmap : (q.map inc).IsPath := hq.map Subtype.val_injective
  have he := (hacyc.subsingleton_path a b).elim ⟨p, hp⟩ ⟨q.map inc, hmap⟩
  have hs : p.support = (q.map inc).support := congrArg (fun r : H.Path a b => r.val.support) he
  have hmem : z ∈ p.support := by simp [p]
  rw [hs, Walk.support_map, List.mem_map] at hmem
  obtain ⟨w, _, hw⟩ := hmem
  exact hz (hw ▸ w.2)

/-- At either second position, the depth-two extension has two distinct
annulus neighbors, contradicting the physical annulus tree. -/
theorem second_position_false {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (hp : 4 ≤ (pureBoundaryCarriers F).card)
    (hzero : (nextRingCarriers F).card = 0)
    (s : Fin 4) (t : Fin n) (ht : 0 < t.val ∧ t.val + 1 < n)
    (hw : sideChart s (t, ⟨1, by omega⟩) ∈ F)
    (hpos : t.val = 2 ∨ t.val + 3 = n) : False := by
  have hbounds := inward_position_bounds hn F hacyc hb hzero s t ht hw
  have hzF := inward_depth_two_of_no_shallow (by omega) F hacyc hzero s t ht hw
  have hwR : IsNextRing (sideChart s (t, ⟨1, by omega⟩)) := by
    fin_cases s <;> simp [sideChart, IsNextRing] <;> omega
  have hc := (nonempty_ring_no_full_rods hn F hacyc hb hp
    ⟨_, mem_filter.mpr ⟨hw, hwR⟩⟩).2.1
  let u : Fin n := if t.val = 2 then ⟨1, by omega⟩ else ⟨n - 2, by omega⟩
  have hu : u.val = 1 ∨ u.val + 2 = n := by
    dsimp [u]
    split_ifs <;> simp
    omega
  have hadj : (gridGraph n n).Adj (t, ⟨2, by omega⟩) (u, ⟨2, by omega⟩) := by
    simp only [gridGraph, adjacent, Fin.ext_iff]
    dsimp [u]
    split_ifs <;> simp <;> omega
  apply outside_two_annulus_neighbors_false F hacyc hc
    (a := sideChart s (t, ⟨1, by omega⟩))
    (b := sideChart s (u, ⟨2, by omega⟩))
    (z := sideChart s (t, ⟨2, by omega⟩))
  · exact (mem_iff_layers (by omega) _).mpr (Or.inr hwR)
  · fin_cases s <;> simp [sideChart, Mem] <;> omega
  · fin_cases s <;> simp [sideChart, Mem] <;> omega
  · intro he
    have he' := congrArg (fun v : GridVertex n n => v.2.val) (sideChart_injective s he)
    change 1 = 2 at he'
    omega
  · refine ⟨(sideChart_adj s _ _).mpr ?_, Or.inr hzF⟩
    simp [gridGraph, adjacent]
  · exact ⟨(sideChart_adj s _ _).mpr hadj, Or.inl hzF⟩

/-- The nonempty-ring branch can only occur at the third position from a
corner. The second-position cycle does not eliminate this remaining case. -/
theorem inward_position_three {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (hp : 4 ≤ (pureBoundaryCarriers F).card)
    (hzero : (nextRingCarriers F).card = 0)
    (s : Fin 4) (t : Fin n) (ht : 0 < t.val ∧ t.val + 1 < n)
    (hw : sideChart s (t, ⟨1, by omega⟩) ∈ F) :
    t.val = 3 ∨ t.val + 4 = n := by
  have h := inward_position_two_or_three hn F hacyc hb hzero s t ht hw
  have hnot := second_position_false hn F hacyc hb hp hzero s t ht hw
  tauto

end GridGraphs.BoundarySix.Connected
