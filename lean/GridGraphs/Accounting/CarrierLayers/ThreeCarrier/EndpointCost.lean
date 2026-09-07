import GridGraphs.Accounting.CarrierLayers.FourCarrier.RootDeficit

/-! # The sixth unit at an endpoint root

The inward neighbor forces a non-near off-side hole in addition to the
corner and three near-corner witnesses. All five charged vertices are distinct.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- An endpoint root forces a second off-side boundary hole, away from all
corners and near-corner positions. -/
theorem endpoint_root_nonNear_hole {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (v : GridVertex n n) (hv : v ∈ F) (hs : OnOpenSide s v)
    (hend : sidePosition s v = 1 ∨ sidePosition s v = n - 2) :
    ∃ b, b ∉ F ∧ IsGridBoundary b ∧ ¬ OnOpenSide s b ∧
      ¬ BoundarySix.Corner b ∧ ¬ BoundarySix.Near b := by
  obtain ⟨u, rfl⟩ := sideChart_surjective s v
  have hus := (sideChart_openSide s u).mp hs
  have hu0 : u.2 = ⟨0, by omega⟩ := Fin.ext hus.1
  have hi := sideChart_root_inward (by omega) F hacyc s hmissing u.1 hus.2
    (by convert hv using 1; exact congrArg (sideChart s) (Prod.ext rfl hu0.symm))
  rw [sideChart_position] at hend
  let b : GridVertex n n :=
    (⟨if u.1.val = 1 then 0 else n - 1, by split <;> omega⟩, ⟨2, by omega⟩)
  have hP := sideChart_acyclic s F hacyc
  have hb : sideChart s b ∉ F := by
    intro hbF
    rcases hend with he | he
    · have hu1 : u.1 = ⟨1, by omega⟩ := Fin.ext he
      have H := grid_cell_has_unforced_edge
        (⟨0, by omega⟩ : Fin (n - 1)) (⟨1, by omega⟩ : Fin (n - 1)) hP
      simp only [cell00, cell01, cell11, cell10, Set.mem_ofPred_eq] at H
      have hb' : sideChart s (⟨0, by omega⟩, ⟨2, by omega⟩) ∈ F := by
        simpa [b, he] using hbF
      rw [hu1] at hi
      rcases H with H | H | H | H
      · exact H.2 hb'
      · exact H.1 hb'
      · exact H.2 hi
      · exact H.1 hi
    · have hu1 : u.1 = ⟨n - 2, by omega⟩ := Fin.ext he
      have H := grid_cell_has_unforced_edge
        (⟨n - 2, by omega⟩ : Fin (n - 1)) (⟨1, by omega⟩ : Fin (n - 1)) hP
      have he' : n - 2 + 1 = n - 1 := by omega
      simp only [cell00, cell01, cell11, cell10, he', Set.mem_ofPred_eq] at H
      have hb' : sideChart s (⟨n - 1, by omega⟩, ⟨2, by omega⟩) ∈ F := by
        simpa [b, he, show n - 2 ≠ 1 by omega] using hbF
      rw [hu1] at hi
      rcases H with H | H | H | H
      · exact H.1 hi
      · exact H.2 hb'
      · exact H.1 hb'
      · exact H.2 hi
  refine ⟨sideChart s b, hb, ?_, ?_, ?_, ?_⟩
  · rw [sideChart_boundary]
    dsimp [b, IsGridBoundary]
    split <;> omega
  · rw [sideChart_openSide]
    dsimp [b]
    omega
  · rw [sideChart_corner]
    dsimp [b, BoundarySix.Corner]
    omega
  · rw [sideChart_near]
    dsimp [b, BoundarySix.Near]
    split <;> omega

/-- The sharp endpoint exclusion needed at `W=5`: the charge is six,
not just the previously available five. No score or saturation is assumed. -/
theorem endpoint_root_offside_deficiency_ge_six {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (v : GridVertex n n) (hv : v ∈ F) (hs : OnOpenSide s v)
    (hend : sidePosition s v = 1 ∨ sidePosition s v = n - 2) :
    6 ≤ boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) := by
  classical
  obtain ⟨a, hac, _, haU⟩ := endpoint_root_corner_hole (by omega) F hacyc s hmissing v hv hs hend
  obtain ⟨b, hbU, hbb, hbs, hbc, hbn⟩ :=
    endpoint_root_nonNear_hole hn F hacyc s hmissing v hv hs hend
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := BoundarySix.corner_witnesses hn F hacyc
  have hpos (u : GridVertex n n) (hus : OnOpenSide s u) (hun : BoundarySix.Near u) :
      sidePosition s u = 1 ∨ sidePosition s u = n - 2 := by
    unfold OnOpenSide OnSide at hus
    unfold BoundarySix.Near at hun
    unfold sidePosition
    split <;> omega
  have hsmall : (Q.filter (OnOpenSide s)).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    have hxs := (mem_filter.mp hx).2
    have hys := (mem_filter.mp hy).2
    have hxp := hpos x hxs (hQnear x (mem_filter.mp hx).1)
    have hyp := hpos y hys (hQnear y (mem_filter.mp hy).1)
    have hxne : sidePosition s x ≠ sidePosition s v := by
      intro he
      exact (mem_sdiff.mp (hQU (mem_filter.mp hx).1)).2
        ((sidePosition_injective hxs hs he).symm ▸ hv)
    have hyne : sidePosition s y ≠ sidePosition s v := by
      intro he
      exact (mem_sdiff.mp (hQU (mem_filter.mp hy).1)).2
        ((sidePosition_injective hys hs he).symm ▸ hv)
    exact sidePosition_injective hxs hys (by omega)
  let R := Q.filter (fun u => ¬ OnOpenSide s u)
  let O := (univ \ F).filter (fun u => IsGridBoundary u ∧ ¬ OnOpenSide s u)
  have hpart := card_filter_add_card_filter_not (s := Q) (p := OnOpenSide s)
  have hR : 3 ≤ R.card := by dsimp [R]; omega
  have haR : a ∉ R := by
    intro h
    have hnear := hQnear a (mem_filter.mp h).1
    unfold BoundarySix.Corner at hac
    unfold BoundarySix.Near at hnear
    omega
  have hbR : b ∉ insert a R := by
    simp only [mem_insert]
    rintro (rfl | h)
    · exact hbc hac
    · exact hbn (hQnear b (mem_filter.mp h).1)
  have hsub : insert b (insert a R) ⊆ O := by
    apply insert_subset
    · exact mem_filter.mpr ⟨by simp [hbU], hbb, hbs⟩
    apply insert_subset
    · apply mem_filter.mpr
      refine ⟨by simp [haU], ?_, ?_⟩
      · unfold BoundarySix.Corner at hac
        unfold IsGridBoundary
        omega
      · unfold BoundarySix.Corner at hac
        unfold OnOpenSide OnSide
        omega
    · intro u hu
      have hnear := hQnear u (mem_filter.mp hu).1
      refine mem_filter.mpr ⟨hQU (mem_filter.mp hu).1, ?_, (mem_filter.mp hu).2⟩
      unfold BoundarySix.Near at hnear
      unfold IsGridBoundary
      omega
  have hO := card_le_card hsub
  rw [card_insert_of_notMem hbR, card_insert_of_notMem haR] at hO
  have hj : 1 ≤ ((univ \ F).filter BoundarySix.Corner).card := by
    apply card_pos.mpr
    exact ⟨a, by simp [haU, hac]⟩
  have hW := offside_deficiency_eq_holes_add_corners (by omega) F s
  change _ = O.card + _ at hW
  omega

/-- At weighted cost at most five, roots lie strictly between the two
near-corner positions. -/
theorem root_positions_of_offside_deficiency_le_five {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 5)
    (v : GridVertex n n) (hv : v ∈ F) (hs : OnOpenSide s v) :
    2 ≤ sidePosition s v ∧ sidePosition s v < n - 2 := by
  have hb := sidePosition_bounds hs
  have hne : ¬ (sidePosition s v = 1 ∨ sidePosition s v = n - 2) := by
    intro h
    have hcost := endpoint_root_offside_deficiency_ge_six hn F hacyc s hmissing v hv hs h
    omega
  omega

end GridGraphs.CarrierLayers.ThreeCarrier
