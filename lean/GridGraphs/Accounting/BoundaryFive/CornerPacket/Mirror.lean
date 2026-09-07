import GridGraphs.Accounting.BoundaryFive.CornerPacket.Geometry

/-! # The other local fork, with the original top gap unchanged -/

namespace GridGraphs.BoundaryFive.CornerPacket

open Finset SimpleGraph

/-- The second fork forces the next top deep-boundary root. -/
theorem top_gap_packet_top_root {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent = 1)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (h43 : (⟨4, by omega⟩, ⟨3, by omega⟩) ∈ F) :
    (⟨2, by omega⟩, ⟨5, by omega⟩) ∈ F := by
  have h24 := (top_gap_packet_holes hn F hacyc hb hc ha hh).2.1
  obtain ⟨_, hiso⟩ := top_gap_preserved_isolated hn F hacyc hb hc ha hh
  have h23 : (⟨2, by omega⟩, ⟨3, by omega⟩) ∉ F :=
    hiso _ (by simp [gridGraph, adjacent])
  have h34 : (⟨3, by omega⟩, ⟨4, by omega⟩) ∉ F := by
    intro h
    exact CarrierLayers.ThreeCarrier.diagonal_preserved_false (n := n) (↑F : Set _) hacyc
      (⟨3, by omega⟩, ⟨4, by omega⟩) (⟨4, by omega⟩, ⟨3, by omega⟩)
      h h43 (Or.inl rfl) (Or.inr rfl)
  have h14 : (⟨1, by omega⟩, ⟨4, by omega⟩) ∉ F :=
    boundaryDeficiencySum_compl_eq_five_next_ring_notMem (by omega) F hacyc hb _
      (by simp) (by simp; omega) (by simp) (by simp; omega) (by simp)
  obtain ⟨v, hv, hadj⟩ := CarrierLayers.preserved_neighbor_of_one_forced_component
    (by omega) F hc _ h24
  have hcases : v = (⟨2, by omega⟩, ⟨3, by omega⟩) ∨
      v = (⟨1, by omega⟩, ⟨4, by omega⟩) ∨
      v = (⟨3, by omega⟩, ⟨4, by omega⟩) ∨
      v = (⟨2, by omega⟩, ⟨5, by omega⟩) := by
    simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
    simp only [Prod.ext_iff, Fin.ext_iff]
    dsimp at hadj
    omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact (h23 hv).elim
  · exact (h14 hv).elim
  · exact (h34 hv).elim
  · exact hv

/-- The top spokes used here avoid the gap at columns one and two. -/
theorem top_adjacent_roots_forbidden {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (i : Nat) (hi : 3 ≤ i) (hi' : i + 4 ≤ n)
    (hx : (⟨2, by omega⟩, ⟨i, by omega⟩) ∈ F)
    (hy : (⟨2, by omega⟩, ⟨i + 1, by omega⟩) ∈ F) : False := by
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  let a : GridVertex n n := (⟨0, by omega⟩, ⟨i, by omega⟩)
  let s : GridVertex n n := (⟨1, by omega⟩, ⟨i, by omega⟩)
  let x : GridVertex n n := (⟨2, by omega⟩, ⟨i, by omega⟩)
  let y : GridVertex n n := (⟨2, by omega⟩, ⟨i + 1, by omega⟩)
  let t : GridVertex n n := (⟨1, by omega⟩, ⟨i + 1, by omega⟩)
  let b : GridVertex n n := (⟨0, by omega⟩, ⟨i + 1, by omega⟩)
  have haF : a ∈ F := boundary_mem_of_top_gap hn F hacyc hb hh a
    (by simp [a, IsGridBoundary]) (by simp [a, BoundarySix.Near]; omega)
    (by simp [a, Prod.ext_iff, Fin.ext_iff]; omega)
  have hbF : b ∈ F := boundary_mem_of_top_gap hn F hacyc hb hh b
    (by simp [b, IsGridBoundary]) (by simp [b, BoundarySix.Near]; omega)
    (by simp [b, Prod.ext_iff, Fin.ext_iff]; omega)
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

/-- The vertical version of the bounded actual carrier at the next root. -/
theorem top_root_carrier_short {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (h25 : (⟨2, by omega⟩, ⟨5, by omega⟩) ∈ F)
    (hC : (⟨(⟨2, by omega⟩, ⟨5, by omega⟩), h25⟩ : (↑F : Set _)) ∈ C.supp)
    (h24 : (⟨2, by omega⟩, ⟨4, by omega⟩) ∉ F)
    (h26 : (⟨2, by omega⟩, ⟨6, by omega⟩) ∉ F)
    (h15 : (⟨1, by omega⟩, ⟨5, by omega⟩) ∉ F)
    (j : Nat) (hj : 3 ≤ j) (hj' : j ≤ 5)
    (hj5 : (⟨j, by omega⟩, ⟨5, by omega⟩) ∉ F) :
    C.supp.toFinset.card ≤ 3 := by
  classical
  let b : (↑F : Set (GridVertex n n)) := ⟨(⟨2, by omega⟩, ⟨5, by omega⟩), h25⟩
  have hb : b ∈ C.supp := hC
  have hbox (v : (↑F : Set (GridVertex n n))) (hv : v ∈ C.supp) :
      v.1.2.val = 5 ∧ 2 ≤ v.1.1.val ∧ v.1.1.val ≤ 4 := by
    rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
    · have he : v.1.1 = b.1.1 := (hr v hv).trans (hr b hb).symm
      have hlo : 5 ≤ v.1.2.val := by
        by_contra h
        obtain ⟨hf, _⟩ := induced_forced_connectedComponent_horizontal_interval_of_le
          hacyc C hv hb he (⟨4, by omega⟩ : Fin n) (by dsimp; omega) (by simp [b])
        exact h24 (by simpa only [he, b, mem_coe] using hf)
      have hhi : v.1.2.val ≤ 5 := by
        by_contra h
        obtain ⟨hf, _⟩ := induced_forced_connectedComponent_horizontal_interval_of_le
          hacyc C hb hv he.symm (⟨6, by omega⟩ : Fin n) (by simp [b]) (by dsimp; omega)
        exact h26 hf
      have he' := congrArg Fin.val he
      dsimp [b] at he'
      exact ⟨by omega, by omega, by omega⟩
    · have he : v.1.2 = b.1.2 := (hc v hv).trans (hc b hb).symm
      have hlo : 2 ≤ v.1.1.val := by
        by_contra h
        obtain ⟨hf, _⟩ := induced_forced_connectedComponent_vertical_interval_of_le
          hacyc C hv hb he (⟨1, by omega⟩ : Fin n) (by dsimp; omega) (by simp [b])
        exact h15 (by simpa only [he, b, mem_coe] using hf)
      have hhi : v.1.1.val < j := by
        by_contra h
        obtain ⟨hf, _⟩ := induced_forced_connectedComponent_vertical_interval_of_le
          hacyc C hb hv he.symm (⟨j, by omega⟩ : Fin n) (by dsimp [b]; omega)
            (by dsimp; omega)
        exact hj5 hf
      exact ⟨congrArg Fin.val he, hlo, by omega⟩
  let f : C.supp → Fin 3 := fun v => ⟨v.1.1.1.val - 2, by have := hbox v.1 v.2; omega⟩
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

/-- The second fork gives a short actual carrier distinct from the singleton. -/
theorem top_gap_second_fork_short_carrier {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent = 1)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (h43 : (⟨4, by omega⟩, ⟨3, by omega⟩) ∈ F) :
    ∃ S : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent,
      S ∉ pureBoundaryCarriers F ∧ S.supp.toFinset.card ≤ 3 ∧
      ∀ v ∈ S.supp, v.1 ≠ (⟨2, by omega⟩, ⟨2, by omega⟩) := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let c : (↑F : Set (GridVertex n n)) := ⟨(⟨4, by omega⟩, ⟨3, by omega⟩), h43⟩
  let C := G.connectedComponentMk c
  have hcC : c ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have h25 := top_gap_packet_top_root hn F hacyc hb hc ha hh h43
  let b : (↑F : Set (GridVertex n n)) := ⟨(⟨2, by omega⟩, ⟨5, by omega⟩), h25⟩
  let B := G.connectedComponentMk b
  have hbB : b ∈ B.supp := by simp [B, ConnectedComponent.mem_supp_iff]
  obtain ⟨h33, h24, h42⟩ := top_gap_packet_holes hn F hacyc hb hc ha hh
  have h26 : (⟨2, by omega⟩, ⟨6, by omega⟩) ∉ F :=
    top_adjacent_roots_forbidden hn F hacyc hb ha hh 5 (by omega) (by omega) h25
  have h15 : (⟨1, by omega⟩, ⟨5, by omega⟩) ∉ F :=
    boundaryDeficiencySum_compl_eq_five_next_ring_notMem (by omega) F hacyc hb _
      (by simp) (by simp; omega) (by simp) (by simp; omega) (by simp)
  have hshort : C.supp.toFinset.card ≤ 3 ∨ B.supp.toFinset.card ≤ 3 := by
    by_cases h44 : (⟨4, by omega⟩, ⟨4, by omega⟩) ∈ F
    · have h35 : (⟨3, by omega⟩, ⟨5, by omega⟩) ∉ F := by
        intro h
        exact CarrierLayers.ThreeCarrier.diagonal_preserved_false (n := n) (↑F : Set _) hacyc
          (⟨4, by omega⟩, ⟨4, by omega⟩) (⟨3, by omega⟩, ⟨5, by omega⟩)
          h44 h (Or.inr rfl) (Or.inl rfl)
      exact Or.inr (top_root_carrier_short hn F hacyc B h25 hbB h24 h26 h15
        3 (by omega) (by omega) h35)
    · by_cases h53 : (⟨5, by omega⟩, ⟨3, by omega⟩) ∈ F
      · have hnotboth (h45 : (⟨4, by omega⟩, ⟨5, by omega⟩) ∈ F)
            (h55 : (⟨5, by omega⟩, ⟨5, by omega⟩) ∈ F) : False := by
          let P : Set (GridVertex n n) := {v | v.swap ∈ F}
          let f : forcedEdgeGraph (gridGraph n n) P →g
              forcedEdgeGraph (gridGraph n n) (↑F : Set _) :=
            { toFun := Prod.swap
              map_rel' := by
                intro v w h
                refine ⟨?_, h.2⟩
                simpa only [gridGraph, adjacent, Prod.fst_swap, Prod.snd_swap, or_comm]
                  using h.1 }
          have hac := hacyc.comap f (by
            intro v w h
            exact Prod.swap_injective h)
          exact forced_rectangle_two_rows_false (⟨3, by omega⟩ : Fin (n - 2))
            (⟨4, by omega⟩ : Fin (n - 1)) hac h43 h53 h45 h55
        by_cases h45 : (⟨4, by omega⟩, ⟨5, by omega⟩) ∈ F
        · exact Or.inr (top_root_carrier_short hn F hacyc B h25 hbB h24 h26 h15
            5 (by omega) (by omega) (hnotboth h45))
        · exact Or.inr (top_root_carrier_short hn F hacyc B h25 hbB h24 h26 h15
            4 (by omega) (by omega) h45)
      · have hsize : C.supp.toFinset.card = 1 := by
          apply carrier_card_one_of_no_neighbor F C c hcC
          intro v hadj hv
          have hcases : v = (⟨4, by omega⟩, ⟨2, by omega⟩) ∨
              v = (⟨3, by omega⟩, ⟨3, by omega⟩) ∨
              v = (⟨5, by omega⟩, ⟨3, by omega⟩) ∨
              v = (⟨4, by omega⟩, ⟨4, by omega⟩) := by
            simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
            dsimp [c] at hadj
            simp only [Prod.ext_iff, Fin.ext_iff]
            omega
          rcases hcases with rfl | rfl | rfl | rfl
          · exact h42 hv
          · exact h33 hv
          · exact h53 hv
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
      have hval := congrArg Subtype.val (hb'.trans hv'.symm)
      simp [b, he] at hval

/-- The oriented top gap always supplies two distinct short nonpure carriers. -/
theorem top_gap_two_short_carriers {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent = 1)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    ∃ Z S : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent,
      Z ≠ S ∧ Z ∉ pureBoundaryCarriers F ∧ S ∉ pureBoundaryCarriers F ∧
      Z.supp.toFinset.card = 1 ∧ S.supp.toFinset.card ≤ 3 := by
  rcases top_gap_packet_fork hn F hacyc hb hc ha hh with ⟨h34, _⟩ | ⟨h43, _⟩
  · exact top_gap_first_fork_two_short_carriers hn F hacyc hb hc ha hh h34
  · obtain ⟨Z, hZ, hZsize, hZsupp⟩ := top_gap_singleton hn F hacyc hb hc ha hh
    obtain ⟨S, hS, hSsize, hSsupp⟩ :=
      top_gap_second_fork_short_carrier hn F hacyc hb hc ha hh h43
    refine ⟨Z, S, ?_, hZ, hS, hZsize, hSsize⟩
    intro he
    obtain ⟨v, hv⟩ := Z.nonempty_supp
    exact hSsupp v (he ▸ hv) (hZsupp v hv)

end GridGraphs.BoundaryFive.CornerPacket
