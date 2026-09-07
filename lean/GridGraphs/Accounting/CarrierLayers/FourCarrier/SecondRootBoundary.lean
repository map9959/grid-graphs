import GridGraphs.Accounting.CarrierLayers.FourCarrier.ExceptionalWitness

/-! # The second root exhausts the three-unit off-side budget

One forced near-end hole and the two far-corner holes leave every non-near
off-side boundary position preserved. A radial axis reaching depths two and
three then closes a six-cycle against that preserved boundary.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

theorem second_root_offside_nonNear_preserved {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 3)
    (t : Fin n) (ht : t.val = 2 ∨ t.val = n - 3)
    (hroot : sideChart s (t, ⟨0, by omega⟩) ∈ F) :
    ∀ v, IsGridBoundary v → ¬ OnOpenSide s v → ¬ BoundarySix.Near v → v ∈ F := by
  classical
  have hcorners := corners_preserved_of_offside_le_three hn F hacyc s hW
  let P : Set (GridVertex n n) := {v | sideChart s v ∈ F}
  have hP := sideChart_acyclic s F hacyc
  have hin := sideChart_root_inward (by omega) F hacyc s hmissing t (by omega) hroot
  let a : GridVertex n n :=
    (⟨if t.val = 2 then 0 else n - 1, by split <;> omega⟩, ⟨1, by omega⟩)
  let b : GridVertex n n := (⟨0, by omega⟩, ⟨n - 2, by omega⟩)
  let c : GridVertex n n := (⟨1, by omega⟩, ⟨n - 1, by omega⟩)
  let d : GridVertex n n := (⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩)
  let e : GridVertex n n := (⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩)
  have ha : a ∉ P := by
    intro ha
    change sideChart s a ∈ F at ha
    by_cases hfirst : t.val = 2
    · have he : t = (⟨2, by omega⟩ : Fin n) := Fin.ext hfirst
      rw [he] at hroot hin
      have hcorner : sideChart s (⟨0, by omega⟩, ⟨0, by omega⟩) ∈ F :=
        hcorners _ ((sideChart_corner s _).mpr (by simp [BoundarySix.Corner]))
      have ha' : sideChart s (⟨0, by omega⟩, ⟨1, by omega⟩) ∈ F := by
        simpa only [a, if_pos hfirst] using ha
      exact forced_rectangle_two_rows_false (⟨0, by omega⟩ : Fin (n - 2))
        (⟨0, by omega⟩ : Fin (n - 1)) hP hcorner ha' hroot hin
    · have he : t = (⟨n - 3, by omega⟩ : Fin n) := Fin.ext (show t.val = n - 3 by omega)
      rw [he] at hroot hin
      have hcorner : sideChart s (⟨n - 1, by omega⟩, ⟨0, by omega⟩) ∈ F :=
        hcorners _ ((sideChart_corner s _).mpr (by dsimp [BoundarySix.Corner]; omega))
      have ha' : sideChart s (⟨n - 1, by omega⟩, ⟨1, by omega⟩) ∈ F := by
        simpa only [a, if_neg hfirst] using ha
      have hlast : n - 3 + 2 = n - 1 := by omega
      apply forced_rectangle_two_rows_false (⟨n - 3, by omega⟩ : Fin (n - 2))
        (⟨0, by omega⟩ : Fin (n - 1)) hP hroot hin
      · change sideChart s (⟨n - 3 + 2, by omega⟩, ⟨0, by omega⟩) ∈ F
        simpa only [hlast] using hcorner
      · change sideChart s (⟨n - 3 + 2, by omega⟩, ⟨1, by omega⟩) ∈ F
        simpa only [hlast] using ha'
  have hbc : b ∉ P ∨ c ∉ P := by
    have H := grid_cell_has_unforced_edge
      (⟨0, by omega⟩ : Fin (n - 1)) (⟨n - 2, by omega⟩ : Fin (n - 1)) hP
    have hlast : n - 2 + 1 = n - 1 := by omega
    simp only [cell00, cell01, cell11, cell10, hlast] at H
    rcases H with H | H | H | H
    · exact Or.inl H.1
    · exact Or.inr H.2
    · exact Or.inr H.1
    · exact Or.inl H.2
  have hde : d ∉ P ∨ e ∉ P := by
    have H := grid_cell_has_unforced_edge
      (⟨n - 2, by omega⟩ : Fin (n - 1)) (⟨n - 2, by omega⟩ : Fin (n - 1)) hP
    have hlast : n - 2 + 1 = n - 1 := by omega
    simp only [cell00, cell01, cell11, cell10, hlast] at H
    rcases H with H | H | H | H
    · exact Or.inl H.2
    · exact Or.inl H.1
    · exact Or.inr H.2
    · exact Or.inr H.1
  have choose (u v : GridVertex n n) (h : u ∉ P ∨ v ∉ P) :
      ∃ q, (q = u ∨ q = v) ∧ q ∉ P := by
    rcases h with h | h
    · exact ⟨u, Or.inl rfl, h⟩
    · exact ⟨v, Or.inr rfl, h⟩
  obtain ⟨q, hq, hqU⟩ := choose b c hbc
  obtain ⟨r, hr, hrU⟩ := choose d e hde
  let Q : Finset (GridVertex n n) := {a, q, r}
  have hQcard : Q.card = 3 := by
    rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;>
      simp only [Q, card_insert_eq_ite, card_singleton, mem_insert, mem_singleton,
        a, b, c, d, e, Prod.ext_iff, Fin.ext_iff] <;> split_ifs <;> omega
  have hQgeom : ∀ v ∈ Q, IsGridBoundary v ∧
      ¬ (v.2.val = 0 ∧ 0 < v.1.val ∧ v.1.val + 1 < n) ∧ BoundarySix.Near v := by
    intro v hv
    simp only [Q, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · dsimp [a, IsGridBoundary, BoundarySix.Near]
      split <;> omega
    · rcases hq with rfl | rfl <;> dsimp [b, c, IsGridBoundary, BoundarySix.Near] <;> omega
    · rcases hr with rfl | rfl <;> dsimp [d, e, IsGridBoundary, BoundarySix.Near] <;> omega
  let O := (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)
  have hsub : Q.image (sideChart s) ⊆ O := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hv
    have hgu := hQgeom u hu
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, ?_⟩,
      (sideChart_boundary s _).mpr hgu.1, fun h => hgu.2.1 ((sideChart_openSide s _).mp h)⟩
    simp only [Q, mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl <;> assumption
  have hweight := offside_deficiency_eq_holes_add_corners (by omega) F s
  have hOeq : Q.image (sideChart s) = O := by
    apply eq_of_subset_of_card_le hsub
    rw [card_image_of_injective _ (sideChart_injective s), hQcard]
    change _ = O.card + _ at hweight
    omega
  intro v hv hs hn
  by_contra hu
  have hvO : v ∈ O := mem_filter.mpr ⟨by simp [hu], hv, hs⟩
  rw [← hOeq] at hvO
  obtain ⟨u, huQ, rfl⟩ := mem_image.mp hvO
  exact hn ((sideChart_near s _).mpr (hQgeom u huQ).2.2)

/-- A second-position radial root cannot simultaneously fill depths two and
three at a weighted off-side budget of three. -/
theorem second_root_full_axis_false {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 3)
    (t : Fin n) (ht : t.val = 2 ∨ t.val = n - 3)
    (hroot : sideChart s (t, ⟨0, by omega⟩) ∈ F)
    (h2 : sideChart s (t, ⟨2, by omega⟩) ∈ F)
    (h3 : sideChart s (t, ⟨3, by omega⟩) ∈ F) : False := by
  have hfill := second_root_offside_nonNear_preserved hn F hacyc s hmissing hW t ht hroot
  have hP := sideChart_acyclic s F hacyc
  have hboundary (a d : Fin n) (ha : a.val = 0 ∨ a.val = n - 1)
      (hd : d.val = 2 ∨ d.val = 3) : sideChart s (a, d) ∈ F := by
    apply hfill
    · rw [sideChart_boundary]; dsimp [IsGridBoundary]; omega
    · rw [sideChart_openSide]; dsimp; omega
    · rw [sideChart_near]; dsimp [BoundarySix.Near]; omega
  rcases ht with ht | ht
  · have he : t = (⟨2, by omega⟩ : Fin n) := Fin.ext ht
    rw [he] at h2 h3
    exact forced_rectangle_two_rows_false (⟨0, by omega⟩ : Fin (n - 2))
      (⟨2, by omega⟩ : Fin (n - 1)) hP
      (hboundary ⟨0, by omega⟩ ⟨2, by omega⟩ (Or.inl rfl) (Or.inl rfl))
      (hboundary ⟨0, by omega⟩ ⟨3, by omega⟩ (Or.inl rfl) (Or.inr rfl)) h2 h3
  · have he : t = (⟨n - 3, by omega⟩ : Fin n) := Fin.ext ht
    rw [he] at h2 h3
    have hlast : n - 3 + 2 = n - 1 := by omega
    apply forced_rectangle_two_rows_false (⟨n - 3, by omega⟩ : Fin (n - 2))
      (⟨2, by omega⟩ : Fin (n - 1)) hP h2 h3
    · exact hboundary ⟨n - 3 + 2, by omega⟩ ⟨2, by omega⟩ (Or.inr hlast) (Or.inl rfl)
    · exact hboundary ⟨n - 3 + 2, by omega⟩ ⟨3, by omega⟩ (Or.inr hlast) (Or.inr rfl)

end GridGraphs.CarrierLayers.FourCarrier
