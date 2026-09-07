import GridGraphs.Accounting.CarrierLayers.FourCarrier.ShallowRequired

/-! # Geometry at three weighted off-side units

Two far-corner witnesses and corner weight two force all corners preserved.
The two second-position roots cannot coexist: their end rectangles would
supply two further holes, exhausting four rather than three off-side units.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- At most three weighted off-side units imply that every corner is preserved.
This does not require the chosen side to be missing or any score hypothesis. -/
theorem corners_preserved_of_offside_le_three {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 3) :
    ∀ v, BoundarySix.Corner v → v ∈ F := by
  classical
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := BoundarySix.corner_witnesses hn F hacyc
  let R := Q.filter (fun v => ¬ OnOpenSide s v)
  let O := (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)
  have hnear := near_openSide_card_le_two (by omega) Q hQnear s
  have hpart := card_filter_add_card_filter_not (s := Q) (p := OnOpenSide s)
  have hR : 2 ≤ R.card := by dsimp [R]; omega
  have hsub : R ⊆ O := by
    intro v hv
    refine mem_filter.mpr ⟨hQU (mem_filter.mp hv).1, ?_, (mem_filter.mp hv).2⟩
    have hn := hQnear v (mem_filter.mp hv).1
    unfold BoundarySix.Near at hn
    unfold IsGridBoundary
    omega
  intro v hc
  by_contra hu
  have hvO : v ∈ O := by
    refine mem_filter.mpr ⟨by simp [hu], ?_, ?_⟩
    all_goals unfold BoundarySix.Corner at hc
    · unfold IsGridBoundary; omega
    · unfold OnOpenSide OnSide; omega
  have hvR : v ∉ R := by
    intro hv
    have hn := hQnear v (mem_filter.mp hv).1
    unfold BoundarySix.Corner at hc
    unfold BoundarySix.Near at hn
    omega
  have hO := card_le_card (insert_subset hvO hsub)
  rw [card_insert_of_notMem hvR] at hO
  have hcpos : 1 ≤ ((univ \ F).filter BoundarySix.Corner).card := by
    apply one_le_card.mpr
    exact ⟨v, by simp [hu, hc]⟩
  have hw := offside_deficiency_eq_holes_add_corners (by omega) F s
  change _ = O.card + _ at hw
  omega

/-- The second root at each end cannot coexist at off-side cost at most three. -/
theorem not_both_second_roots_of_offside_le_three {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 3)
    (hr0 : sideChart s (⟨2, by omega⟩, ⟨0, by omega⟩) ∈ F)
    (hr1 : sideChart s (⟨n - 3, by omega⟩, ⟨0, by omega⟩) ∈ F) : False := by
  classical
  have hcorners := corners_preserved_of_offside_le_three hn F hacyc s hW
  let P : Set (GridVertex n n) := {v | sideChart s v ∈ F}
  have hP := sideChart_acyclic s F hacyc
  have hi0 := sideChart_root_inward (by omega) F hacyc s hmissing
    (⟨2, by omega⟩ : Fin n) (by dsimp; omega) hr0
  have hi1 := sideChart_root_inward (by omega) F hacyc s hmissing
    (⟨n - 3, by omega⟩ : Fin n) (by dsimp; omega) hr1
  let a : GridVertex n n := (⟨0, by omega⟩, ⟨1, by omega⟩)
  let b : GridVertex n n := (⟨n - 1, by omega⟩, ⟨1, by omega⟩)
  let c : GridVertex n n := (⟨0, by omega⟩, ⟨n - 2, by omega⟩)
  let d : GridVertex n n := (⟨1, by omega⟩, ⟨n - 1, by omega⟩)
  let e : GridVertex n n := (⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩)
  let f : GridVertex n n := (⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩)
  have hc0 : sideChart s (⟨0, by omega⟩, ⟨0, by omega⟩) ∈ F :=
    hcorners _ ((sideChart_corner s _).mpr (by simp [BoundarySix.Corner]))
  have hc1 : sideChart s (⟨n - 1, by omega⟩, ⟨0, by omega⟩) ∈ F :=
    hcorners _ ((sideChart_corner s _).mpr (by dsimp [BoundarySix.Corner]; omega))
  have ha : a ∉ P := by
    intro ha
    exact forced_rectangle_two_rows_false (⟨0, by omega⟩ : Fin (n - 2))
      (⟨0, by omega⟩ : Fin (n - 1)) hP hc0 ha hr0 hi0
  have hb : b ∉ P := by
    intro hb
    have he : n - 3 + 2 = n - 1 := by omega
    apply forced_rectangle_two_rows_false (⟨n - 3, by omega⟩ : Fin (n - 2))
      (⟨0, by omega⟩ : Fin (n - 1)) hP hr1 hi1
    · change sideChart s (⟨n - 3 + 2, by omega⟩, ⟨0, by omega⟩) ∈ F
      simpa only [he] using hc1
    · simpa only [he] using hb
  have hcd : c ∉ P ∨ d ∉ P := by
    have H := grid_cell_has_unforced_edge
      (⟨0, by omega⟩ : Fin (n - 1)) (⟨n - 2, by omega⟩ : Fin (n - 1)) hP
    have hlast : n - 2 + 1 = n - 1 := by omega
    simp only [cell00, cell01, cell11, cell10, hlast] at H
    rcases H with H | H | H | H
    · exact Or.inl H.1
    · exact Or.inr H.2
    · exact Or.inr H.1
    · exact Or.inl H.2
  have hef : e ∉ P ∨ f ∉ P := by
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
  obtain ⟨q, hq, hqU⟩ := choose c d hcd
  obtain ⟨t, ht, htU⟩ := choose e f hef
  let Q : Finset (GridVertex n n) := {a, b, q, t}
  have hQcard : Q.card = 4 := by
    rcases hq with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp only [Q, card_insert_eq_ite, card_singleton, mem_insert, mem_singleton,
        a, b, c, d, e, f, Prod.ext_iff, Fin.ext_iff] <;> split_ifs <;> omega
  let O := (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)
  have hsub : Q.image (sideChart s) ⊆ O := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hv
    have huP : u ∉ P := by
      simp only [Q, mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl <;> assumption
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, huP⟩, ?_⟩
    simp only [Q, mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · simp only [sideChart_boundary, sideChart_openSide]
      dsimp [a, IsGridBoundary]; omega
    · simp only [sideChart_boundary, sideChart_openSide]
      dsimp [b, IsGridBoundary]; omega
    · rcases hq with rfl | rfl <;> simp only [sideChart_boundary, sideChart_openSide] <;>
        dsimp [c, d, IsGridBoundary] <;> omega
    · rcases ht with rfl | rfl <;> simp only [sideChart_boundary, sideChart_openSide] <;>
        dsimp [e, f, IsGridBoundary] <;> omega
  have hO := card_le_card hsub
  rw [card_image_of_injective _ (sideChart_injective s), hQcard] at hO
  have hw := offside_deficiency_eq_holes_add_corners (by omega) F s
  change _ = O.card + _ at hw
  omega

/-- The surviving four-pure missing-side counterexample has weighted off-side
cost exactly three. -/
theorem four_pure_offside_deficiency_eq_three {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 4) :
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3 := by
  obtain ⟨_, hq, _, _, hb, _⟩ := four_pure_missing_side_profile hk F hacyc s hmissing hf hp
  have hpart := offside_deficiency_add_side_holes (by omega) F s
  have hholes := side_holes_add_roots (by omega) F s
  omega

end GridGraphs.CarrierLayers.FourCarrier
