import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostThreeReduction

/-! # The physical three-hole boundary before classifying its extra hole

Two distinct far-corner cells supply two near holes. At W3 all corners are
preserved and exactly one further off-side hole remains. Its position is not
assumed to be adjacent to either witness.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- W3 preserves every corner and consists of three ordinary off-side holes.
At most one is non-near. This does not require a missing-carrier hypothesis. -/
theorem cost_three_boundary {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3) :
    (∀ v, BoundarySix.Corner v → v ∈ F) ∧
      ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card = 3 ∧
      ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v ∧
        ¬ BoundarySix.Near v)).card ≤ 1 := by
  classical
  have hcorners := corners_preserved_of_offside_le_three hn F hacyc s (by omega)
  have hj : ((univ \ F).filter BoundarySix.Corner).card = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact (mem_sdiff.mp (mem_filter.mp hv).1).2 (hcorners v (mem_filter.mp hv).2)
  let O := (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)
  let N := (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v ∧
    ¬ BoundarySix.Near v)
  have hweight := offside_deficiency_eq_holes_add_corners (by omega) F s
  have hO : O.card = 3 := by dsimp [O]; omega
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := BoundarySix.corner_witnesses hn F hacyc
  let R := Q.filter (fun v => ¬ OnOpenSide s v)
  have hnear := near_openSide_card_le_two (by omega) Q hQnear s
  have hpart := card_filter_add_card_filter_not (s := Q) (p := OnOpenSide s)
  have hR : 2 ≤ R.card := by dsimp [R]; omega
  have hdisj : Disjoint N R := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_filter.mp hv).2.2.2 (hQnear v (mem_filter.mp hw).1)
  have hsub : N ∪ R ⊆ O := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact mem_filter.mpr ⟨(mem_filter.mp hv).1, (mem_filter.mp hv).2.1,
        (mem_filter.mp hv).2.2.1⟩
    · have hvn := hQnear v (mem_filter.mp hv).1
      refine mem_filter.mpr ⟨hQU (mem_filter.mp hv).1, ?_, (mem_filter.mp hv).2⟩
      unfold BoundarySix.Near at hvn
      unfold IsGridBoundary
      omega
  have hcount := card_le_card hsub
  rw [card_union_of_disjoint hdisj] at hcount
  exact ⟨hcorners, hO, by change N.card ≤ 1; omega⟩

/-- Two physical far-corner holes exist without any cost or score premise.
Their incident-side choices remain explicit. -/
theorem offside_far_hole_pair {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) (s : Fin 4) :
    ∃ a b : GridVertex (3 * k + 2) (3 * k + 2),
      (a = (⟨0, by omega⟩, ⟨3 * k, by omega⟩) ∨
        a = (⟨1, by omega⟩, ⟨3 * k + 1, by omega⟩)) ∧
      (b = (⟨3 * k, by omega⟩, ⟨3 * k + 1, by omega⟩) ∨
        b = (⟨3 * k + 1, by omega⟩, ⟨3 * k, by omega⟩)) ∧
      sideChart s a ≠ sideChart s b ∧
      {sideChart s a, sideChart s b} ⊆
        (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) := by
  classical
  let n := 3 * k + 2
  let P : Set (GridVertex n n) := {v | sideChart s v ∈ F}
  have hP := sideChart_acyclic s F hacyc
  let a0 : GridVertex n n := (⟨0, by omega⟩, ⟨3 * k, by omega⟩)
  let a1 : GridVertex n n := (⟨1, by omega⟩, ⟨3 * k + 1, by omega⟩)
  let b0 : GridVertex n n := (⟨3 * k, by omega⟩, ⟨3 * k + 1, by omega⟩)
  let b1 : GridVertex n n := (⟨3 * k + 1, by omega⟩, ⟨3 * k, by omega⟩)
  have ha : a0 ∉ P ∨ a1 ∉ P := by
    have H := grid_cell_has_unforced_edge
      (⟨0, by omega⟩ : Fin (n - 1)) (⟨3 * k, by omega⟩ : Fin (n - 1)) hP
    simp only [cell00, cell01, cell11, cell10] at H
    rcases H with H | H | H | H
    · exact Or.inl H.1
    · exact Or.inr H.2
    · exact Or.inr H.1
    · exact Or.inl H.2
  have hb : b0 ∉ P ∨ b1 ∉ P := by
    have H := grid_cell_has_unforced_edge
      (⟨3 * k, by omega⟩ : Fin (n - 1)) (⟨3 * k, by omega⟩ : Fin (n - 1)) hP
    simp only [cell00, cell01, cell11, cell10] at H
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
  obtain ⟨a, ha, haU⟩ := choose a0 a1 ha
  obtain ⟨b, hb, hbU⟩ := choose b0 b1 hb
  let O := (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)
  have haO : sideChart s a ∈ O := by
    refine mem_filter.mpr ⟨by simp [show sideChart s a ∉ F from haU], ?_⟩
    rcases ha with rfl | rfl <;> simp only [sideChart_boundary, sideChart_openSide] <;>
      dsimp [a0, a1, IsGridBoundary] <;> omega
  have hbO : sideChart s b ∈ O := by
    refine mem_filter.mpr ⟨by simp [show sideChart s b ∉ F from hbU], ?_⟩
    rcases hb with rfl | rfl <;> simp only [sideChart_boundary, sideChart_openSide] <;>
      dsimp [b0, b1, IsGridBoundary] <;> omega
  have hab : sideChart s a ≠ sideChart s b := by
    intro he
    have he' := sideChart_injective s he
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [a0, a1, b0, b1, Prod.ext_iff, Fin.ext_iff] at he'
    omega
  exact ⟨a, b, ha, hb, hab, insert_subset haO (singleton_subset_iff.mpr hbO)⟩

/-- At W3 the two far witnesses leave exactly one distinct additional hole.
The extra hole's position is deliberately unrestricted; adjacency to a far
witness requires the later carrier/run argument. -/
theorem cost_three_far_holes_plus_one {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) (s : Fin 4)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3) :
    ∃ a b c : GridVertex (3 * k + 2) (3 * k + 2),
      (a = (⟨0, by omega⟩, ⟨3 * k, by omega⟩) ∨
        a = (⟨1, by omega⟩, ⟨3 * k + 1, by omega⟩)) ∧
      (b = (⟨3 * k, by omega⟩, ⟨3 * k + 1, by omega⟩) ∨
        b = (⟨3 * k + 1, by omega⟩, ⟨3 * k, by omega⟩)) ∧
      sideChart s a ≠ sideChart s b ∧ c ≠ sideChart s a ∧ c ≠ sideChart s b ∧
      ¬ BoundarySix.Corner c ∧
      (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) =
        {sideChart s a, sideChart s b, c} := by
  classical
  obtain ⟨a, b, ha, hb, hab, hsub⟩ := offside_far_hole_pair hk F hacyc s
  obtain ⟨hcorners, hOcard, _⟩ := cost_three_boundary (by omega) F hacyc s hW
  let O := (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)
  let Q : Finset (GridVertex (3 * k + 2) (3 * k + 2)) := {sideChart s a, sideChart s b}
  have hQcard : Q.card = 2 := by simp [Q, hab]
  have hsub' : Q ⊆ O := hsub
  have hdiff : (O \ Q).card = 1 := by
    rw [card_sdiff_of_subset hsub', hQcard]
    change O.card = 3 at hOcard
    omega
  obtain ⟨c, hc⟩ := card_eq_one.mp hdiff
  have hcD : c ∈ O \ Q := by rw [hc]; simp
  have hcO := (mem_sdiff.mp hcD).1
  have hcQ := (mem_sdiff.mp hcD).2
  have hcA : c ≠ sideChart s a := by intro he; apply hcQ; simp [Q, he]
  have hcB : c ≠ sideChart s b := by intro he; apply hcQ; simp [Q, he]
  have hcCorner : ¬ BoundarySix.Corner c := by
    intro h
    exact (mem_sdiff.mp (mem_filter.mp hcO).1).2 (hcorners c h)
  refine ⟨a, b, c, ha, hb, hab, hcA, hcB, hcCorner, ?_⟩
  have he := sdiff_union_of_subset hsub
  change O \ Q ∪ Q = O at he
  rw [hc] at he
  change O = {sideChart s a, sideChart s b, c}
  rw [← he]
  ext v
  simp [Q, or_comm, or_left_comm]

/-- The surviving counterexample profiles also have preserved corners and
roots strictly away from both second positions. No extra-hole position is inferred. -/
theorem three_pure_remaining_boundary {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3) :
    (∀ v, BoundarySix.Corner v → v ∈ F) ∧
      ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card = 3 ∧
      (∀ v ∈ F, OnOpenSide s v → 3 ≤ sidePosition s v ∧ sidePosition s v + 3 < 3 * k + 2) := by
  have hW := three_pure_missing_side_cost_eq_three hk F hacyc s hmissing hf hp
  obtain ⟨hcorners, hholes, _⟩ := cost_three_boundary (by omega) F hacyc s hW
  exact ⟨hcorners, hholes, fun v hv hs =>
    root_positions_of_corners_preserved hk F hacyc s hmissing hf hp hcorners v hv hs⟩

end GridGraphs.CarrierLayers.ThreeCarrier
