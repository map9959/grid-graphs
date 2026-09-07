import GridGraphs.Accounting.BoundaryFive.TopSingleton
import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoEdgeGeometry

/-! # The first forced vertices of the oriented corner packet

Coordinates here are full-grid coordinates: the deep corner is `(2,2)`.
The other boundary-hole orientations remain unrestricted.
-/

namespace GridGraphs.BoundaryFive.CornerPacket

open Finset SimpleGraph

/-- A connected induced part of a forest contains every path between its vertices. -/
theorem path_stays_in_connected_set {V : Type*} (H : SimpleGraph V)
    (hacyc : H.IsAcyclic) (S : Set V) (hconn : (H.induce S).Preconnected)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (p : H.Walk a b) (hp : p.IsPath) {v : V} (hv : v ∈ p.support) : v ∈ S := by
  obtain ⟨q, hq⟩ := (hconn ⟨a, ha⟩ ⟨b, hb⟩).exists_isPath
  let f := (Embedding.induce (G := H) S).toHom
  have hmap : (q.map f).IsPath := hq.map (by
    intro x y h
    exact Subtype.ext h)
  have he := (hacyc.subsingleton_path a b).elim ⟨p, hp⟩ ⟨q.map f, hmap⟩
  have hs : p.support = (q.map f).support :=
    congrArg (fun r : H.Path a b => r.val.support) he
  rw [hs, Walk.support_map, List.mem_map] at hv
  obtain ⟨w, _, hw⟩ := hv
  exact hw ▸ w.2

/-- All boundary vertices other than Near positions and the positioned Second
hole are preserved. This does not normalize the remaining Near holes. -/
theorem boundary_mem_of_top_gap {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (v : GridVertex n n) (hv : IsGridBoundary v) (hnear : ¬ BoundarySix.Near v)
    (hne : v ≠ (⟨0, by omega⟩, ⟨2, by omega⟩)) : v ∈ F := by
  classical
  obtain ⟨Q, u, _, _, hholes, hQ, _, _⟩ := holes_eq_insert_second hn F hacyc hb
  have hu : (⟨0, by omega⟩, ⟨2, by omega⟩) = u := by
    have hm : (⟨0, by omega⟩, ⟨2, by omega⟩) ∈ insert u Q := by
      rw [← hholes]
      simp [hh, IsGridBoundary]
    rcases mem_insert.mp hm with h | h
    · exact h
    · have hq := hQ _ h
      simp only [BoundarySix.Near] at hq
      omega
  by_contra hf
  have hm : v ∈ insert u Q := by rw [← hholes]; simp [hf, hv]
  rcases mem_insert.mp hm with h | h
  · exact hne (h.trans hu.symm)
  · exact hnear (hQ v h)

/-- Besides the singleton's neighbors, the two axial distance-two vertices and
the inward diagonal are holes. The axial exclusions use the actual perimeter. -/
theorem top_gap_packet_holes {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    (⟨3, by omega⟩, ⟨3, by omega⟩) ∉ F ∧
    (⟨2, by omega⟩, ⟨4, by omega⟩) ∉ F ∧
    (⟨4, by omega⟩, ⟨2, by omega⟩) ∉ F := by
  obtain ⟨hz, _⟩ := top_gap_preserved_isolated hn F hacyc hb hc ha hh
  have hconn := perimeter_preconnected_of_top_gap (by omega) F hacyc hb ha hh
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  let a : GridVertex n n := (⟨2, by omega⟩, ⟨0, by omega⟩)
  let t : GridVertex n n := (⟨2, by omega⟩, ⟨1, by omega⟩)
  let z : GridVertex n n := (⟨2, by omega⟩, ⟨2, by omega⟩)
  have haF : a ∈ F := boundary_mem_of_top_gap hn F hacyc hb hh a
    (by simp [a, IsGridBoundary]) (by simp [a, BoundarySix.Near]; omega)
    (by simp [a, Prod.ext_iff, Fin.ext_iff])
  have hat : H.Adj a t := ⟨by simp [a, t, gridGraph, adjacent], Or.inl haF⟩
  have htz : H.Adj t z := ⟨by simp [t, z, gridGraph, adjacent], Or.inr hz⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hv
    exact CarrierLayers.ThreeCarrier.diagonal_preserved_false (n := n) (↑F : Set _) hacyc
      (⟨2, by omega⟩, ⟨2, by omega⟩) (⟨3, by omega⟩, ⟨3, by omega⟩)
      hz hv (Or.inl rfl) (Or.inl rfl)
  · intro hy
    let u : GridVertex n n := (⟨2, by omega⟩, ⟨3, by omega⟩)
    let y : GridVertex n n := (⟨2, by omega⟩, ⟨4, by omega⟩)
    let s : GridVertex n n := (⟨1, by omega⟩, ⟨4, by omega⟩)
    let b : GridVertex n n := (⟨0, by omega⟩, ⟨4, by omega⟩)
    have hbF : b ∈ F := boundary_mem_of_top_gap hn F hacyc hb hh b
      (by simp [b, IsGridBoundary]) (by simp [b, BoundarySix.Near]; omega)
      (by simp [b, Prod.ext_iff, Fin.ext_iff])
    have hzu : H.Adj z u := ⟨by simp [z, u, gridGraph, adjacent], Or.inl hz⟩
    have huy : H.Adj u y := ⟨by simp [u, y, gridGraph, adjacent], Or.inr hy⟩
    have hys : H.Adj y s := ⟨by simp [y, s, gridGraph, adjacent], Or.inl hy⟩
    have hsb : H.Adj s b := ⟨by simp [s, b, gridGraph, adjacent], Or.inr hbF⟩
    let p : H.Walk a b := .cons hat (.cons htz
      (.cons hzu (.cons huy (.cons hys (.cons hsb .nil)))))
    have hp : p.IsPath := by
      simp [p, Walk.cons_isPath_iff, a, t, z, u, y, s, b, Prod.ext_iff, Fin.ext_iff]
    have hzb := path_stays_in_connected_set H hacyc {v | IsGridBoundary v} hconn
      (by simp [a, IsGridBoundary]) (by simp [b, IsGridBoundary]) p hp
      (v := z) (by simp [p])
    simp [z, IsGridBoundary] at hzb
    omega
  · intro hy
    let u : GridVertex n n := (⟨3, by omega⟩, ⟨2, by omega⟩)
    let y : GridVertex n n := (⟨4, by omega⟩, ⟨2, by omega⟩)
    let s : GridVertex n n := (⟨4, by omega⟩, ⟨1, by omega⟩)
    let b : GridVertex n n := (⟨4, by omega⟩, ⟨0, by omega⟩)
    have hbF : b ∈ F := boundary_mem_of_top_gap hn F hacyc hb hh b
      (by simp [b, IsGridBoundary]) (by simp [b, BoundarySix.Near]; omega)
      (by simp [b, Prod.ext_iff, Fin.ext_iff])
    have hzu : H.Adj z u := ⟨by simp [z, u, gridGraph, adjacent], Or.inl hz⟩
    have huy : H.Adj u y := ⟨by simp [u, y, gridGraph, adjacent], Or.inr hy⟩
    have hys : H.Adj y s := ⟨by simp [y, s, gridGraph, adjacent], Or.inl hy⟩
    have hsb : H.Adj s b := ⟨by simp [s, b, gridGraph, adjacent], Or.inr hbF⟩
    let p : H.Walk a b := .cons hat (.cons htz
      (.cons hzu (.cons huy (.cons hys (.cons hsb .nil)))))
    have hp : p.IsPath := by
      simp [p, Walk.cons_isPath_iff, a, t, z, u, y, s, b, Prod.ext_iff, Fin.ext_iff]
    have hzb := path_stays_in_connected_set H hacyc {v | IsGridBoundary v} hconn
      (by simp [a, IsGridBoundary]) (by simp [b, IsGridBoundary]) p hp
      (v := z) (by simp [p])
    simp [z, IsGridBoundary] at hzb
    omega

/-- Domination at the inward diagonal chooses exactly one of the two next roots. -/
theorem top_gap_packet_fork {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    ((⟨3, by omega⟩, ⟨4, by omega⟩) ∈ F ∧
      (⟨4, by omega⟩, ⟨3, by omega⟩) ∉ F) ∨
    ((⟨4, by omega⟩, ⟨3, by omega⟩) ∈ F ∧
      (⟨3, by omega⟩, ⟨4, by omega⟩) ∉ F) := by
  obtain ⟨_, hiso⟩ := top_gap_preserved_isolated hn F hacyc hb hc ha hh
  have hh33 := (top_gap_packet_holes hn F hacyc hb hc ha hh).1
  obtain ⟨v, hv, hadj⟩ := CarrierLayers.preserved_neighbor_of_one_forced_component
    (by omega) F hc _ hh33
  have h23 : (⟨2, by omega⟩, ⟨3, by omega⟩) ∉ F :=
    hiso _ (by simp [gridGraph, adjacent])
  have h32 : (⟨3, by omega⟩, ⟨2, by omega⟩) ∉ F :=
    hiso _ (by simp [gridGraph, adjacent])
  have hcases : v = (⟨2, by omega⟩, ⟨3, by omega⟩) ∨
      v = (⟨3, by omega⟩, ⟨2, by omega⟩) ∨
      v = (⟨3, by omega⟩, ⟨4, by omega⟩) ∨
      v = (⟨4, by omega⟩, ⟨3, by omega⟩) := by
    simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
    simp only [Prod.ext_iff, Fin.ext_iff]
    dsimp at hadj
    omega
  have hnotboth (h34 : (⟨3, by omega⟩, ⟨4, by omega⟩) ∈ F)
      (h43 : (⟨4, by omega⟩, ⟨3, by omega⟩) ∈ F) : False :=
    CarrierLayers.ThreeCarrier.diagonal_preserved_false (n := n) (↑F : Set _) hacyc
      (⟨3, by omega⟩, ⟨4, by omega⟩) (⟨4, by omega⟩, ⟨3, by omega⟩)
      h34 h43 (Or.inl rfl) (Or.inr rfl)
  rcases hcases with rfl | rfl | rfl | rfl
  · exact (h23 hv).elim
  · exact (h32 hv).elim
  · exact Or.inl ⟨hv, hnotboth hv⟩
  · exact Or.inr ⟨hv, fun h => hnotboth h hv⟩

/-- In the `(3,4)` fork, domination forces the next left deep-boundary root. -/
theorem top_gap_packet_left_root {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (h34 : (⟨3, by omega⟩, ⟨4, by omega⟩) ∈ F) :
    (⟨5, by omega⟩, ⟨2, by omega⟩) ∈ F := by
  have h42 := (top_gap_packet_holes hn F hacyc hb hc ha hh).2.2
  obtain ⟨_, hiso⟩ := top_gap_preserved_isolated hn F hacyc hb hc ha hh
  have h32 : (⟨3, by omega⟩, ⟨2, by omega⟩) ∉ F :=
    hiso _ (by simp [gridGraph, adjacent])
  have h43 : (⟨4, by omega⟩, ⟨3, by omega⟩) ∉ F := by
    intro h
    exact CarrierLayers.ThreeCarrier.diagonal_preserved_false (n := n) (↑F : Set _) hacyc
      (⟨3, by omega⟩, ⟨4, by omega⟩) (⟨4, by omega⟩, ⟨3, by omega⟩)
      h34 h (Or.inl rfl) (Or.inr rfl)
  have h41 : (⟨4, by omega⟩, ⟨1, by omega⟩) ∉ F :=
    boundaryDeficiencySum_compl_eq_five_next_ring_notMem (by omega) F hacyc hb _
      (by simp) (by simp; omega) (by simp) (by simp; omega) (by simp)
  obtain ⟨v, hv, hadj⟩ := CarrierLayers.preserved_neighbor_of_one_forced_component
    (by omega) F hc _ h42
  have hcases : v = (⟨3, by omega⟩, ⟨2, by omega⟩) ∨
      v = (⟨4, by omega⟩, ⟨1, by omega⟩) ∨
      v = (⟨4, by omega⟩, ⟨3, by omega⟩) ∨
      v = (⟨5, by omega⟩, ⟨2, by omega⟩) := by
    simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
    simp only [Prod.ext_iff, Fin.ext_iff]
    dsimp at hadj
    omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact (h32 hv).elim
  · exact (h41 hv).elim
  · exact (h43 hv).elim
  · exact hv

/-- Adjacent left deep-boundary roots cannot both be preserved when their
outer spokes land on the connected perimeter. -/
theorem left_adjacent_roots_forbidden {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (i : Nat) (hi : 2 ≤ i) (hi' : i + 4 ≤ n)
    (hx : (⟨i, by omega⟩, ⟨2, by omega⟩) ∈ F)
    (hy : (⟨i + 1, by omega⟩, ⟨2, by omega⟩) ∈ F) : False := by
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  let a : GridVertex n n := (⟨i, by omega⟩, ⟨0, by omega⟩)
  let s : GridVertex n n := (⟨i, by omega⟩, ⟨1, by omega⟩)
  let x : GridVertex n n := (⟨i, by omega⟩, ⟨2, by omega⟩)
  let y : GridVertex n n := (⟨i + 1, by omega⟩, ⟨2, by omega⟩)
  let t : GridVertex n n := (⟨i + 1, by omega⟩, ⟨1, by omega⟩)
  let b : GridVertex n n := (⟨i + 1, by omega⟩, ⟨0, by omega⟩)
  have haF : a ∈ F := boundary_mem_of_top_gap hn F hacyc hb hh a
    (by simp [a, IsGridBoundary]) (by simp [a, BoundarySix.Near]; omega)
    (by simp [a, Prod.ext_iff, Fin.ext_iff])
  have hbF : b ∈ F := boundary_mem_of_top_gap hn F hacyc hb hh b
    (by simp [b, IsGridBoundary]) (by simp [b, BoundarySix.Near]; omega)
    (by simp [b, Prod.ext_iff, Fin.ext_iff])
  have has : H.Adj a s := ⟨by simp [a, s, gridGraph, adjacent], Or.inl haF⟩
  have hsx : H.Adj s x := ⟨by simp [s, x, gridGraph, adjacent], Or.inr hx⟩
  have hxy : H.Adj x y := ⟨by simp [x, y, gridGraph, adjacent], Or.inl hx⟩
  have hyt : H.Adj y t := ⟨by simp [y, t, gridGraph, adjacent], Or.inl hy⟩
  have htb : H.Adj t b := ⟨by simp [t, b, gridGraph, adjacent], Or.inr hbF⟩
  let p : H.Walk a b := .cons has (.cons hsx (.cons hxy (.cons hyt (.cons htb .nil))))
  have hp : p.IsPath := by
    simp [p, Walk.cons_isPath_iff, a, s, x, y, t, b, Prod.ext_iff, Fin.ext_iff]
  have hxb := path_stays_in_connected_set H hacyc {v | IsGridBoundary v}
    (perimeter_preconnected_of_top_gap (by omega) F hacyc hb ha hh)
    (by simp [a, IsGridBoundary]) (by simp [b, IsGridBoundary]) p hp
    (v := x) (by simp [p])
  simp [x, IsGridBoundary] at hxb
  omega

/-- A carrier at `(5,2)` blocked vertically and on the left has at most three
vertices if a hole occurs at column four or five. -/
theorem left_root_carrier_short {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (h52 : (⟨5, by omega⟩, ⟨2, by omega⟩) ∈ F)
    (hC : (⟨(⟨5, by omega⟩, ⟨2, by omega⟩), h52⟩ : (↑F : Set _)) ∈ C.supp)
    (h42 : (⟨4, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (h62 : (⟨6, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (h51 : (⟨5, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (j : Nat) (hj : 3 ≤ j) (hj' : j ≤ 5)
    (h5j : (⟨5, by omega⟩, ⟨j, by omega⟩) ∉ F) :
    C.supp.toFinset.card ≤ 3 := by
  classical
  let b : (↑F : Set (GridVertex n n)) := ⟨(⟨5, by omega⟩, ⟨2, by omega⟩), h52⟩
  have hb : b ∈ C.supp := hC
  have hbox (v : (↑F : Set (GridVertex n n))) (hv : v ∈ C.supp) :
      v.1.1.val = 5 ∧ 2 ≤ v.1.2.val ∧ v.1.2.val ≤ 4 := by
    rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
    · have he : v.1.1 = b.1.1 := (hr v hv).trans (hr b hb).symm
      have hlo : 2 ≤ v.1.2.val := by
        by_contra h
        obtain ⟨hf, _⟩ := induced_forced_connectedComponent_horizontal_interval_of_le
          hacyc C hv hb he (⟨1, by omega⟩ : Fin n) (by dsimp; omega) (by simp [b])
        exact h51 (by simpa only [he, b, mem_coe] using hf)
      have hhi : v.1.2.val < j := by
        by_contra h
        obtain ⟨hf, _⟩ := induced_forced_connectedComponent_horizontal_interval_of_le
          hacyc C hb hv he.symm (⟨j, by omega⟩ : Fin n) (by dsimp [b]; omega)
            (by dsimp; omega)
        exact h5j hf
      exact ⟨congrArg Fin.val he, hlo, by omega⟩
    · have he : v.1.2 = b.1.2 := (hc v hv).trans (hc b hb).symm
      have hlo : 5 ≤ v.1.1.val := by
        by_contra h
        obtain ⟨hf, _⟩ := induced_forced_connectedComponent_vertical_interval_of_le
          hacyc C hv hb he (⟨4, by omega⟩ : Fin n) (by dsimp; omega) (by simp [b])
        exact h42 (by simpa only [he, b, mem_coe] using hf)
      have hhi : v.1.1.val ≤ 5 := by
        by_contra h
        obtain ⟨hf, _⟩ := induced_forced_connectedComponent_vertical_interval_of_le
          hacyc C hb hv he.symm (⟨6, by omega⟩ : Fin n) (by simp [b]) (by dsimp; omega)
        exact h62 hf
      have he' := congrArg Fin.val he
      dsimp [b] at he'
      exact ⟨by omega, by omega, by omega⟩
  let f : C.supp → Fin 3 := fun v => ⟨v.1.1.2.val - 2, by have := hbox v.1 v.2; omega⟩
  have hinj : Function.Injective f := by
    intro v w he
    have hv := hbox v.1 v.2
    have hw := hbox w.1 w.2
    have he' := congrArg Fin.val he
    dsimp [f] at he'
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> omega
  simpa only [Set.toFinset_card, Fintype.card_fin] using Fintype.card_le_of_injective f hinj

/-- With no preserved neighbor, an actual induced component is a singleton. -/
theorem carrier_card_one_of_no_neighbor {n : Nat}
    (F : Finset (GridVertex n n))
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (v : (↑F : Set (GridVertex n n))) (hv : v ∈ C.supp)
    (hno : ∀ w, (gridGraph n n).Adj v.1 w → w ∉ F) : C.supp.toFinset.card = 1 := by
  classical
  have he (w : (↑F : Set (GridVertex n n))) (hw : w ∈ C.supp) : w = v := by
    obtain ⟨p⟩ := C.reachable_of_mem_supp hv hw
    cases p with
    | nil => rfl
    | @cons _ t _ h p => exact (hno _ h t.2).elim
  have hs : C.supp.toFinset = {v} := by
    ext w
    simp only [Set.mem_toFinset, mem_singleton]
    exact ⟨he w, fun h => h ▸ hv⟩
  rw [hs, card_singleton]

/-- The first fork contains an actual second short nonpure carrier, not just
short occupied pieces of potentially longer carriers. It cannot contain `z`. -/
theorem top_gap_first_fork_short_carrier {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (h34 : (⟨3, by omega⟩, ⟨4, by omega⟩) ∈ F) :
    ∃ S : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent,
      S ∉ pureBoundaryCarriers F ∧ S.supp.toFinset.card ≤ 3 ∧
      ∀ v ∈ S.supp, v.1 ≠ (⟨2, by omega⟩, ⟨2, by omega⟩) := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let c : (↑F : Set (GridVertex n n)) := ⟨(⟨3, by omega⟩, ⟨4, by omega⟩), h34⟩
  let C := G.connectedComponentMk c
  have hcC : c ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have h52 := top_gap_packet_left_root hn F hacyc hb hc ha hh h34
  let b : (↑F : Set (GridVertex n n)) := ⟨(⟨5, by omega⟩, ⟨2, by omega⟩), h52⟩
  let B := G.connectedComponentMk b
  have hbB : b ∈ B.supp := by simp [B, ConnectedComponent.mem_supp_iff]
  obtain ⟨h33, h24, h42⟩ := top_gap_packet_holes hn F hacyc hb hc ha hh
  have h62 : (⟨6, by omega⟩, ⟨2, by omega⟩) ∉ F :=
    left_adjacent_roots_forbidden hn F hacyc hb ha hh 5 (by omega) (by omega) h52
  have h51 : (⟨5, by omega⟩, ⟨1, by omega⟩) ∉ F :=
    boundaryDeficiencySum_compl_eq_five_next_ring_notMem (by omega) F hacyc hb _
      (by simp) (by simp; omega) (by simp) (by simp; omega) (by simp)
  have hshort : C.supp.toFinset.card ≤ 3 ∨ B.supp.toFinset.card ≤ 3 := by
    by_cases h44 : (⟨4, by omega⟩, ⟨4, by omega⟩) ∈ F
    · have h53 : (⟨5, by omega⟩, ⟨3, by omega⟩) ∉ F := by
        intro h
        exact CarrierLayers.ThreeCarrier.diagonal_preserved_false (n := n) (↑F : Set _) hacyc
          (⟨4, by omega⟩, ⟨4, by omega⟩) (⟨5, by omega⟩, ⟨3, by omega⟩)
          h44 h (Or.inl rfl) (Or.inr rfl)
      exact Or.inr (left_root_carrier_short hn F hacyc B h52 hbB h42 h62 h51
        3 (by omega) (by omega) h53)
    · by_cases h35 : (⟨3, by omega⟩, ⟨5, by omega⟩) ∈ F
      · have hnotboth (h54 : (⟨5, by omega⟩, ⟨4, by omega⟩) ∈ F)
            (h55 : (⟨5, by omega⟩, ⟨5, by omega⟩) ∈ F) : False :=
          forced_rectangle_two_rows_false (⟨3, by omega⟩ : Fin (n - 2))
            (⟨4, by omega⟩ : Fin (n - 1)) hacyc h34 h35 h54 h55
        by_cases h54 : (⟨5, by omega⟩, ⟨4, by omega⟩) ∈ F
        · exact Or.inr (left_root_carrier_short hn F hacyc B h52 hbB h42 h62 h51
            5 (by omega) (by omega) (hnotboth h54))
        · exact Or.inr (left_root_carrier_short hn F hacyc B h52 hbB h42 h62 h51
            4 (by omega) (by omega) h54)
      · have hsize : C.supp.toFinset.card = 1 := by
          apply carrier_card_one_of_no_neighbor F C c hcC
          intro v hadj hv
          have hcases : v = (⟨2, by omega⟩, ⟨4, by omega⟩) ∨
              v = (⟨3, by omega⟩, ⟨3, by omega⟩) ∨
              v = (⟨3, by omega⟩, ⟨5, by omega⟩) ∨
              v = (⟨4, by omega⟩, ⟨4, by omega⟩) := by
            simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
            dsimp [c] at hadj
            simp only [Prod.ext_iff, Fin.ext_iff]
            omega
          rcases hcases with rfl | rfl | rfl | rfl
          · exact h24 hv
          · exact h33 hv
          · exact h35 hv
          · exact h44 hv
        exact Or.inl (by omega)
  rcases hshort with hC | hB
  · refine ⟨C, ?_, hC, ?_⟩
    · intro hp
      have hboundary := (mem_filter.mp hp).2 c hcC
      simp [c, IsGridBoundary] at hboundary
      omega
    · intro v hv he
      have hs := induced_forced_reachable_same_row_or_column hacyc
        (C.reachable_of_mem_supp hcC hv)
      simp [c, he] at hs
  · refine ⟨B, ?_, hB, ?_⟩
    · intro hp
      have hboundary := (mem_filter.mp hp).2 b hbB
      simp [b, IsGridBoundary] at hboundary
      omega
    · intro v hv he
      obtain ⟨_, hiso⟩ := top_gap_preserved_isolated hn F hacyc hb hc ha hh
      have hsize := carrier_card_one_of_no_neighbor F B v hv (by simpa only [he] using hiso)
      obtain ⟨w, hw⟩ := card_eq_one.mp hsize
      have hb' : b = w := mem_singleton.mp (hw ▸ Set.mem_toFinset.mpr hbB)
      have hv' : v = w := mem_singleton.mp (hw ▸ Set.mem_toFinset.mpr hv)
      have he' : b = v := hb'.trans hv'.symm
      have hval := congrArg Subtype.val he'
      simp [b, he] at hval

/-- The deep forced component at `z` is exactly its three-vertex corner star.
This concerns the forced graph restricted to the deep square, not `grid[F]`. -/
theorem top_gap_deep_component_exact_star {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    let z : BoundaryFiveConstruction.Deep n :=
      ⟨(⟨2, by omega⟩, ⟨2, by omega⟩), by
        simp [BoundaryFiveConstruction.Deep]; omega⟩
    ∀ w : BoundaryFiveConstruction.Deep n,
      ((forcedEdgeGraph (gridGraph n n) (↑F : Set _)).induce
        (BoundaryFiveConstruction.Deep n)).Reachable z w ↔
      w.1 = (⟨2, by omega⟩, ⟨2, by omega⟩) ∨
      w.1 = (⟨2, by omega⟩, ⟨3, by omega⟩) ∨
      w.1 = (⟨3, by omega⟩, ⟨2, by omega⟩) := by
  dsimp only
  let D := BoundaryFiveConstruction.Deep n
  let H := (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).induce D
  let z : D := ⟨(⟨2, by omega⟩, ⟨2, by omega⟩), by
    simp [D, BoundaryFiveConstruction.Deep]; omega⟩
  let P (w : D) : Prop := w.1 = (⟨2, by omega⟩, ⟨2, by omega⟩) ∨
    w.1 = (⟨2, by omega⟩, ⟨3, by omega⟩) ∨
    w.1 = (⟨3, by omega⟩, ⟨2, by omega⟩)
  obtain ⟨hz, hiso⟩ := top_gap_preserved_isolated hn F hacyc hb hc ha hh
  obtain ⟨h33, h24, h42⟩ := top_gap_packet_holes hn F hacyc hb hc ha hh
  have h23 : (⟨2, by omega⟩, ⟨3, by omega⟩) ∉ F :=
    hiso _ (by simp [gridGraph, adjacent])
  have h32 : (⟨3, by omega⟩, ⟨2, by omega⟩) ∉ F :=
    hiso _ (by simp [gridGraph, adjacent])
  have hclosed {u v : D} (hu : P u) (he : H.Adj u v) : P v := by
    have hvD := v.2
    dsimp [D, BoundaryFiveConstruction.Deep] at hvD
    have hadj : (gridGraph n n).Adj u.1 v.1 := he.1
    have hF : u.1 ∈ F ∨ v.1 ∈ F := he.2
    rcases hu with hu | hu | hu
    · simp only [gridGraph, adjacent, hu, Fin.ext_iff] at hadj
      simp only [P, Prod.ext_iff, Fin.ext_iff]
      dsimp at hadj
      omega
    · have hvF : v.1 ∈ F := hF.resolve_left (by simpa only [hu] using h23)
      have hcases : v.1 = (⟨2, by omega⟩, ⟨2, by omega⟩) ∨
          v.1 = (⟨2, by omega⟩, ⟨4, by omega⟩) ∨
          v.1 = (⟨3, by omega⟩, ⟨3, by omega⟩) := by
        simp only [gridGraph, adjacent, hu, Fin.ext_iff] at hadj
        simp only [Prod.ext_iff, Fin.ext_iff]
        dsimp at hadj
        omega
      rcases hcases with h | h | h
      · exact Or.inl h
      · exact (h24 (h ▸ hvF)).elim
      · exact (h33 (h ▸ hvF)).elim
    · have hvF : v.1 ∈ F := hF.resolve_left (by simpa only [hu] using h32)
      have hcases : v.1 = (⟨2, by omega⟩, ⟨2, by omega⟩) ∨
          v.1 = (⟨4, by omega⟩, ⟨2, by omega⟩) ∨
          v.1 = (⟨3, by omega⟩, ⟨3, by omega⟩) := by
        simp only [gridGraph, adjacent, hu, Fin.ext_iff] at hadj
        simp only [Prod.ext_iff, Fin.ext_iff]
        dsimp at hadj
        omega
      rcases hcases with h | h | h
      · exact Or.inl h
      · exact (h42 (h ▸ hvF)).elim
      · exact (h33 (h ▸ hvF)).elim
  have hwalk {u v : D} (p : H.Walk u v) : P u → P v := by
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hu => ih (hclosed hu h)
  intro w
  change H.Reachable z w ↔ P w
  constructor
  · rintro ⟨p⟩
    exact hwalk p (Or.inl rfl)
  · intro hw
    rcases hw with hw | hw | hw
    · have he : w = z := Subtype.ext hw
      rw [he]
    · have he : H.Adj z w := ⟨by simp [z, hw, gridGraph, adjacent], Or.inl hz⟩
      exact he.reachable
    · have he : H.Adj z w := ⟨by simp [z, hw, gridGraph, adjacent], Or.inl hz⟩
      exact he.reachable

/-- The first fork supplies two distinct actual nonpure carriers with lengths
one and at most three. The second carrier is derived, not supplied as a premise. -/
theorem top_gap_first_fork_two_short_carriers {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (h34 : (⟨3, by omega⟩, ⟨4, by omega⟩) ∈ F) :
    ∃ Z S : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent,
      Z ≠ S ∧ Z ∉ pureBoundaryCarriers F ∧ S ∉ pureBoundaryCarriers F ∧
      Z.supp.toFinset.card = 1 ∧ S.supp.toFinset.card ≤ 3 := by
  obtain ⟨Z, hZ, hZsize, hZsupp⟩ := top_gap_singleton hn F hacyc hb hc ha hh
  obtain ⟨S, hS, hSsize, hSsupp⟩ :=
    top_gap_first_fork_short_carrier hn F hacyc hb hc ha hh h34
  refine ⟨Z, S, ?_, hZ, hS, hZsize, hSsize⟩
  intro he
  obtain ⟨v, hv⟩ := Z.nonempty_supp
  exact hSsupp v (he ▸ hv) (hZsupp v hv)

end GridGraphs.BoundaryFive.CornerPacket
