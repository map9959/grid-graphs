import GridGraphs.Accounting.CarrierLayers.FourCarrier.SideChart

/-! # Four saturated off-side holes

The two end rectangles and two far corner cells supply four distinct holes.
At weighted cost at most four, no corner can be a hole and these four holes
exhaust the off-side boundary. In particular all off-side holes are near corners.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Ordinary off-side holes plus all corner holes give the exact weighted
off-side deficiency. Every corner is off the open side. -/
theorem offside_deficiency_eq_holes_add_corners {n : Nat} (hn : 2 ≤ n)
    (F : Finset (GridVertex n n)) (s : Fin 4) :
    boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) =
      ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card +
      ((univ \ F).filter BoundarySix.Corner).card := by
  have hweight (v : GridVertex n n) : gridBoundaryDeficiency n n v =
      (if IsGridBoundary v then 1 else 0) + (if BoundarySix.Corner v then 1 else 0) := by
    rw [gridBoundaryDeficiency_eq_four_side_indicators hn hn]
    unfold IsGridBoundary BoundarySix.Corner
    split_ifs <;> omega
  unfold boundaryDeficiencySum
  simp_rw [hweight]
  rw [sum_add_distrib]
  simp only [← sum_filter, sum_const, smul_eq_mul, mul_one, filter_filter]
  congr 1
  · congr 1
    ext v
    simp [and_left_comm, and_comm]
  · congr 1
    ext v
    simp only [mem_filter]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · intro h
      refine ⟨h.1, ?_, h.2⟩
      have hc := h.2
      unfold BoundarySix.Corner at hc
      unfold OnOpenSide OnSide
      omega

/-- Saturated roots and four weighted off-side units force preserved corners,
both off-side near-end holes, and no off-side holes away from near positions. -/
theorem saturated_missing_side_boundary {k : Nat} (hk : 3 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hq : (F.filter (OnOpenSide s)).card = k)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 4) :
    (∀ v, BoundarySix.Corner v → v ∈ F) ∧
      sideChart s (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F ∧
      sideChart s (⟨3 * k + 1, by omega⟩, ⟨1, by omega⟩) ∉ F ∧
      ∀ v, IsGridBoundary v → ¬ OnOpenSide s v → v ∉ F → BoundarySix.Near v := by
  classical
  let n := 3 * k + 2
  let P : Set (GridVertex n n) := {v | sideChart s v ∈ F}
  have hP := sideChart_acyclic s F hacyc
  have hphase := saturated_missing_side_exact_phase hk F hacyc s hmissing hq hW
  have hr0 : sideChart s (⟨2, by omega⟩, ⟨0, by omega⟩) ∈ F := by
    apply (hphase _ ((sideChart_openSide s _).mpr (by dsimp; omega))).mpr
    exact ⟨0, by omega, by rw [sideChart_position]⟩
  have hr1 : sideChart s (⟨3 * k - 1, by omega⟩, ⟨0, by omega⟩) ∈ F := by
    apply (hphase _ ((sideChart_openSide s _).mpr (by dsimp; omega))).mpr
    exact ⟨k - 1, by omega, by rw [sideChart_position]; dsimp; omega⟩
  have hi0 := sideChart_root_inward (by omega) F hacyc s hmissing
    (⟨2, by omega⟩ : Fin n) (by dsimp; omega) hr0
  have hi1 := sideChart_root_inward (by omega) F hacyc s hmissing
    (⟨3 * k - 1, by omega⟩ : Fin n) (by dsimp [n]; omega) hr1
  let a : GridVertex n n := (⟨0, by omega⟩, ⟨0, by omega⟩)
  let b : GridVertex n n := (⟨0, by omega⟩, ⟨1, by omega⟩)
  let c : GridVertex n n := (⟨n - 1, by omega⟩, ⟨0, by omega⟩)
  let d : GridVertex n n := (⟨n - 1, by omega⟩, ⟨1, by omega⟩)
  let e : GridVertex n n := (⟨0, by omega⟩, ⟨n - 2, by omega⟩)
  let f : GridVertex n n := (⟨1, by omega⟩, ⟨n - 1, by omega⟩)
  let g : GridVertex n n := (⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩)
  let h : GridVertex n n := (⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩)
  have hab : a ∉ P ∨ b ∉ P := by
    by_contra hn
    push Not at hn
    exact forced_rectangle_two_rows_false (⟨0, by omega⟩ : Fin (n - 2))
      (⟨0, by omega⟩ : Fin (n - 1)) hP hn.1 hn.2 hr0 hi0
  have hcd : c ∉ P ∨ d ∉ P := by
    by_contra hn
    push Not at hn
    have he : n - 3 + 2 = n - 1 := by omega
    have heRoot : n - 3 = 3 * k - 1 := by dsimp [n]; omega
    apply forced_rectangle_two_rows_false (⟨n - 3, by omega⟩ : Fin (n - 2))
      (⟨0, by omega⟩ : Fin (n - 1)) hP
    · change sideChart s (⟨n - 3, by omega⟩, ⟨0, by omega⟩) ∈ F
      simpa only [heRoot] using hr1
    · change sideChart s (⟨n - 3, by omega⟩, ⟨1, by omega⟩) ∈ F
      simpa only [heRoot] using hi1
    · simpa only [he] using hn.1
    · simpa only [he] using hn.2
  have hef : e ∉ P ∨ f ∉ P := by
    have H := grid_cell_has_unforced_edge
      (⟨0, by omega⟩ : Fin (n - 1)) (⟨n - 2, by omega⟩ : Fin (n - 1)) hP
    have hlast : n - 2 + 1 = n - 1 := by omega
    simp only [cell00, cell01, cell11, cell10, hlast] at H
    rcases H with H | H | H | H
    · exact Or.inl H.1
    · exact Or.inr H.2
    · exact Or.inr H.1
    · exact Or.inl H.2
  have hgh : g ∉ P ∨ h ∉ P := by
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
  obtain ⟨q0, hq0, hu0⟩ := choose a b hab
  obtain ⟨q1, hq1, hu1⟩ := choose c d hcd
  obtain ⟨q2, hq2, hu2⟩ := choose e f hef
  obtain ⟨q3, hq3, hu3⟩ := choose g h hgh
  let Q : Finset (GridVertex n n) := {q0, q1, q2, q3}
  have hQcard : Q.card = 4 := by
    have h01 : q0 ≠ q1 := by
      rcases hq0 with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
        simp [a, b, c, d, Prod.ext_iff, Fin.ext_iff] <;> omega
    have h02 : q0 ≠ q2 := by
      rcases hq0 with rfl | rfl <;> rcases hq2 with rfl | rfl <;>
        simp [a, b, e, f, Prod.ext_iff, Fin.ext_iff] <;> omega
    have h03 : q0 ≠ q3 := by
      rcases hq0 with rfl | rfl <;> rcases hq3 with rfl | rfl <;>
        simp [a, b, g, h, Prod.ext_iff, Fin.ext_iff] <;> omega
    have h12 : q1 ≠ q2 := by
      rcases hq1 with rfl | rfl <;> rcases hq2 with rfl | rfl <;>
        simp [c, d, e, f, Prod.ext_iff, Fin.ext_iff] <;> omega
    have h13 : q1 ≠ q3 := by
      rcases hq1 with rfl | rfl <;> rcases hq3 with rfl | rfl <;>
        simp [c, d, g, h, Prod.ext_iff, Fin.ext_iff] <;> omega
    have h23 : q2 ≠ q3 := by
      rcases hq2 with rfl | rfl <;> rcases hq3 with rfl | rfl <;>
        simp [e, f, g, h, Prod.ext_iff, Fin.ext_iff] <;> omega
    simp [Q, h01, h02, h03, h12, h13, h23]
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
    · rcases hq0 with rfl | rfl <;> simp only [sideChart_boundary, sideChart_openSide] <;>
        dsimp [a, b, IsGridBoundary] <;> omega
    · rcases hq1 with rfl | rfl <;> simp only [sideChart_boundary, sideChart_openSide] <;>
        dsimp [c, d, IsGridBoundary] <;> omega
    · rcases hq2 with rfl | rfl <;> simp only [sideChart_boundary, sideChart_openSide] <;>
        dsimp [e, f, IsGridBoundary] <;> omega
    · rcases hq3 with rfl | rfl <;> simp only [sideChart_boundary, sideChart_openSide] <;>
        dsimp [g, h, IsGridBoundary] <;> omega
  have hweight := offside_deficiency_eq_holes_add_corners (by omega) F s
  have hOlower := card_le_card hsub
  rw [card_image_of_injective _ (sideChart_injective s), hQcard] at hOlower
  have hcorners : ∀ v, BoundarySix.Corner v → v ∈ F := by
    have hzero : ((univ \ F).filter BoundarySix.Corner).card = 0 := by
      change _ = O.card + _ at hweight
      omega
    intro v hv
    by_contra hu
    have hm : v ∈ (univ \ F).filter BoundarySix.Corner := by simp [hu, hv]
    rw [card_eq_zero.mp hzero] at hm
    simp at hm
  have haF : a ∈ P := hcorners _ ((sideChart_corner s _).mpr (by simp [a, BoundarySix.Corner]))
  have hcF : c ∈ P := hcorners _ ((sideChart_corner s _).mpr (by
    dsimp [c, BoundarySix.Corner]; omega))
  have hq0b : q0 = b := hq0.resolve_left (fun he => hu0 (he ▸ haF))
  have hq1d : q1 = d := hq1.resolve_left (fun he => hu1 (he ▸ hcF))
  have hOeq : Q.image (sideChart s) = O := by
    apply eq_of_subset_of_card_le hsub
    rw [card_image_of_injective _ (sideChart_injective s), hQcard]
    change _ = O.card + _ at hweight
    omega
  refine ⟨hcorners, ?_, ?_, ?_⟩
  · rw [hq0b] at hu0
    exact hu0
  · rw [hq1d] at hu1
    have hend : n - 1 = 3 * k + 1 := by omega
    change sideChart s d ∉ F at hu1
    simpa only [d, hend] using hu1
  · intro v hv hs hu
    have hvO : v ∈ O := mem_filter.mpr ⟨by simp [hu], hv, hs⟩
    rw [← hOeq] at hvO
    obtain ⟨u, huQ, rfl⟩ := mem_image.mp hvO
    simp only [Q, mem_insert, mem_singleton, hq0b, hq1d] at huQ
    rcases huQ with rfl | rfl | rfl | rfl
    · apply (sideChart_near s _).mpr
      simp [b, BoundarySix.Near]
    · apply (sideChart_near s _).mpr
      simp [d, BoundarySix.Near]
      omega
    · apply (sideChart_near s _).mpr
      rcases hq2 with rfl | rfl <;> simp [e, f, BoundarySix.Near] <;> omega
    · apply (sideChart_near s _).mpr
      rcases hq3 with rfl | rfl <;> simp [g, h, BoundarySix.Near] <;> omega

end GridGraphs.CarrierLayers.FourCarrier
