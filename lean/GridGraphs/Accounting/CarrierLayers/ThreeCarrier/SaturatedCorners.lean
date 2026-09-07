import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.EndpointCost

/-! # Saturation is impossible with three pure carriers

A preserved corner isolated in the induced graph uses a pure carrier without
covering any open side. The three covered sides in a stable counterexample
already require three other physical carriers.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- In a three-pure stable counterexample, a corner cannot be an induced
isolate. This counts an actual component in addition to the covered sides. -/
theorem corner_notMem_of_neighbors_notMem {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3)
    (a : GridVertex (3 * k + 2) (3 * k + 2)) (ha : BoundarySix.Corner a)
    (hiso : ∀ v, (gridGraph (3 * k + 2) (3 * k + 2)).Adj a v → v ∉ F) :
    a ∉ F := by
  classical
  intro haF
  let G := (gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)
  let u : (↑F : Set _) := ⟨a, haF⟩
  let D := G.connectedComponentMk u
  have hu : u ∈ D.supp := by simp [D, ConnectedComponent.mem_supp_iff]
  have hsingle (v : (↑F : Set _)) (hv : v ∈ D.supp) : v = u := by
    have hr : G.Reachable u v :=
      ConnectedComponent.exact ((ConnectedComponent.mem_supp_iff _ _).mp hv).symm
    by_contra hne
    have hm := mem_support_of_reachable (Ne.symm hne) hr
    obtain ⟨w, hw⟩ := (mem_support G).mp hm
    exact hiso w.val hw w.property
  have hD : D ∈ pureBoundaryCarriers F := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro v hv
    rw [hsingle v hv]
    change IsGridBoundary a
    unfold BoundarySix.Corner at ha
    unfold IsGridBoundary
    omega
  let S := univ.filter (fun s : Fin 4 =>
    ∃ C ∈ pureBoundaryCarriers F, ∃ v ∈ C.supp, OnOpenSide s v.val)
  have hS : 3 ≤ S.card := stable_counterexample_three_le_covered_sides hk F hacyc hf
  have hex (s : S) := (mem_filter.mp s.property).2
  choose C hC v hv hs using hex
  have hne (s : S) : C s ≠ D := by
    intro he
    have hvu := hsingle (v s) (he ▸ hv s)
    have hvs := hs s
    rw [hvu] at hvs
    change OnOpenSide s.val a at hvs
    unfold BoundarySix.Corner at ha
    unfold OnOpenSide OnSide at hvs
    omega
  let f : S → (pureBoundaryCarriers F).erase D := fun s =>
    ⟨C s, mem_erase.mpr ⟨hne s, hC s⟩⟩
  have hinj : Function.Injective f := by
    intro s t he
    have heC : C s = C t := congrArg Subtype.val he
    obtain ⟨b, hb⟩ := pure_carrier_on_side (by omega) F hacyc (C t) (hC t)
    exact Subtype.ext ((openSide_unique (hs s) (hb (v s) (heC ▸ hv s))).trans
      (openSide_unique (hs t) (hb (v t) (hv t))).symm)
  have hcount := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe, card_erase_of_mem hD, hp] at hcount
  omega

/-- Endpoint exclusion at cost five gives the saturated phase `2,5,...,3k-1`. -/
theorem saturated_missing_side_exact_phase_le_five {k : Nat} (hk : 3 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hq : (F.filter (OnOpenSide s)).card = k)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 5) :
    ∀ v, OnOpenSide s v → (v ∈ F ↔ ∃ i < k, sidePosition s v = 3 * i + 2) := by
  classical
  let A := F.filter (OnOpenSide s)
  let S := A.image (sidePosition s)
  have hcard : S.card = k := by
    rw [card_image_iff.mpr, hq]
    intro u hu v hv he
    exact sidePosition_injective (mem_filter.mp hu).2 (mem_filter.mp hv).2 he
  have hbound : ∀ x ∈ S, 2 ≤ x ∧ x < 3 * k := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    have h := root_positions_of_offside_deficiency_le_five (by omega) F hacyc s hmissing hW
      v (mem_filter.mp hv).1 (mem_filter.mp hv).2
    simpa only [Nat.add_sub_cancel] using h
  have hspace : ∀ x ∈ S, ∀ y ∈ S, x < y → x + 3 ≤ y := by
    intro x hx y hy hlt
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
    obtain ⟨w, hw, hwr, huw⟩ := missing_side_root_inward (by omega) F hacyc s hmissing
      u (mem_filter.mp hu).1 (mem_filter.mp hu).2
    obtain ⟨z, hz, hzr, hvz⟩ := missing_side_root_inward (by omega) F hacyc s hmissing
      v (mem_filter.mp hv).1 (mem_filter.mp hv).2
    exact radial_pair_spacing (by omega) F hacyc s
      (mem_filter.mp hu).1 (mem_filter.mp hv).1 hw hz
      (mem_filter.mp hu).2 (mem_filter.mp hv).2 hwr hzr huw hvz hlt
  have hphase := tight_three_spaced_positions (by omega) S hcard hbound hspace
  intro v hvs
  rw [← hphase]
  constructor
  · intro hv
    exact mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, hvs⟩, rfl⟩
  · intro hv
    obtain ⟨u, hu, he⟩ := mem_image.mp hv
    exact (sidePosition_injective (mem_filter.mp hu).2 hvs he) ▸ (mem_filter.mp hu).1

/-- Both missing-side corners are holes in a saturated three-pure
counterexample with `W<=5`. A preserved corner would be a fourth pure carrier. -/
theorem saturated_missing_side_corner_holes {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hq : (F.filter (OnOpenSide s)).card = k)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 5) :
    sideChart s (⟨0, by omega⟩, ⟨0, by omega⟩) ∉ F ∧
      sideChart s (⟨3 * k + 1, by omega⟩, ⟨0, by omega⟩) ∉ F := by
  let n := 3 * k + 2
  have hP := sideChart_acyclic s F hacyc
  have hphase := saturated_missing_side_exact_phase_le_five (by omega) F hacyc s hmissing hq hW
  have hr0 : sideChart s (⟨2, by omega⟩, ⟨0, by omega⟩) ∈ F := by
    apply (hphase _ ((sideChart_openSide s _).mpr (by dsimp; omega))).mpr
    exact ⟨0, by omega, by rw [sideChart_position]⟩
  have hr1 : sideChart s (⟨n - 3, by omega⟩, ⟨0, by omega⟩) ∈ F := by
    apply (hphase _ ((sideChart_openSide s _).mpr (by dsimp; omega))).mpr
    exact ⟨k - 1, by omega, by rw [sideChart_position]; dsimp [n]; omega⟩
  have hi0 := sideChart_root_inward (by omega) F hacyc s hmissing
    (⟨2, by omega⟩ : Fin n) (by dsimp; omega) hr0
  have hi1 := sideChart_root_inward (by omega) F hacyc s hmissing
    (⟨n - 3, by omega⟩ : Fin n) (by dsimp; omega) hr1
  have hsideHole (t : Fin n) (ht : t.val = 1 ∨ t.val = n - 2) :
      sideChart s (t, ⟨0, by omega⟩) ∉ F := by
    intro hv
    have hpos := root_positions_of_offside_deficiency_le_five (by omega) F hacyc s hmissing
      hW _ hv ((sideChart_openSide s _).mpr (by dsimp; omega))
    rw [sideChart_position] at hpos
    dsimp at hpos
    omega
  have hcorner (t : Fin n) (ht : t.val = 0 ∨ t.val = n - 1) :
      sideChart s (t, ⟨0, by omega⟩) ∉ F := by
    intro haF
    have hnear : sideChart s (t, ⟨1, by omega⟩) ∉ F := by
      intro hbF
      rcases ht with he | he
      · have ht0 : t = ⟨0, by omega⟩ := Fin.ext he
        rw [ht0] at haF hbF
        exact forced_rectangle_two_rows_false (⟨0, by omega⟩ : Fin (n - 2))
          (⟨0, by omega⟩ : Fin (n - 1)) hP haF hbF hr0 hi0
      · have ht1 : t = ⟨n - 1, by omega⟩ := Fin.ext he
        have he' : n - 3 + 2 = n - 1 := by omega
        apply forced_rectangle_two_rows_false (⟨n - 3, by omega⟩ : Fin (n - 2))
          (⟨0, by omega⟩ : Fin (n - 1)) hP hr1 hi1
        · change sideChart s (⟨n - 3 + 2, by omega⟩, ⟨0, by omega⟩) ∈ F
          simpa only [he', ht1] using haF
        · change sideChart s (⟨n - 3 + 2, by omega⟩, ⟨1, by omega⟩) ∈ F
          simpa only [he', ht1] using hbF
    apply corner_notMem_of_neighbors_notMem hk F hacyc hf hp _ ?_ ?_ haF
    · rw [sideChart_corner]
      dsimp [BoundarySix.Corner]
      omega
    · intro v hadj hv
      obtain ⟨z, rfl⟩ := sideChart_surjective s v
      have hadj' := (sideChart_adj s _ _).mp hadj
      have hz : z = (t, ⟨1, by omega⟩) ∨
          (z.2.val = 0 ∧ (z.1.val = 1 ∨ z.1.val = n - 2)) := by
        simp only [gridGraph, adjacent, Fin.ext_iff] at hadj'
        simp only [Prod.ext_iff, Fin.ext_iff]
        omega
      rcases hz with rfl | ⟨hz0, hz1⟩
      · exact hnear hv
      · have he : z = (z.1, ⟨0, by omega⟩) := Prod.ext rfl (Fin.ext hz0)
        rw [he] at hv
        exact hsideHole z.1 hz1 hv
  exact ⟨hcorner _ (Or.inl rfl), hcorner _ (Or.inr (by dsimp [n]))⟩

/-- Two distinct corner holes cost four, while the off-side near-corner
witnesses cost at least two more. The witnesses cannot reuse either corner. -/
theorem offside_deficiency_ge_six_of_two_corner_holes {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (a b : GridVertex n n)
    (ha : BoundarySix.Corner a) (hb : BoundarySix.Corner b)
    (hab : a ≠ b) (haU : a ∉ F) (hbU : b ∉ F) :
    6 ≤ boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) := by
  classical
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := BoundarySix.corner_witnesses hn F hacyc
  have hnear := near_openSide_card_le_two (by omega) Q hQnear s
  let R := Q.filter (fun v => ¬ OnOpenSide s v)
  have hpart := card_filter_add_card_filter_not (s := Q) (p := OnOpenSide s)
  have hR : 2 ≤ R.card := by dsimp [R]; omega
  let O := (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)
  let J := (univ \ F).filter BoundarySix.Corner
  have hcorner (v : GridVertex n n) (hc : BoundarySix.Corner v) (hU : v ∉ F) :
      v ∈ O ∧ v ∈ J ∧ v ∉ R := by
    have hB : IsGridBoundary v := by unfold BoundarySix.Corner at hc; unfold IsGridBoundary; omega
    have hs : ¬ OnOpenSide s v := by unfold BoundarySix.Corner at hc; unfold OnOpenSide OnSide; omega
    refine ⟨by simp [O, hU, hB, hs], by simp [J, hU, hc], ?_⟩
    intro h
    have hvn := hQnear v (mem_filter.mp h).1
    unfold BoundarySix.Corner at hc
    unfold BoundarySix.Near at hvn
    omega
  obtain ⟨haO, haJ, haR⟩ := hcorner a ha haU
  obtain ⟨hbO, hbJ, hbR⟩ := hcorner b hb hbU
  have hsub : insert a (insert b R) ⊆ O := by
    apply insert_subset haO
    apply insert_subset hbO
    intro v hv
    have hvn := hQnear v (mem_filter.mp hv).1
    refine mem_filter.mpr ⟨hQU (mem_filter.mp hv).1, ?_, (mem_filter.mp hv).2⟩
    unfold BoundarySix.Near at hvn
    unfold IsGridBoundary
    omega
  have hO := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hab, haR]), card_insert_of_notMem hbR] at hO
  have hJ : 2 ≤ J.card := by
    have hsubJ : {a, b} ⊆ J := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact haJ
      · exact hbJ
    have h := card_le_card hsubJ
    simpa [hab] using h
  have hW := offside_deficiency_eq_holes_add_corners (by omega) F s
  change _ = O.card + J.card at hW
  omega

/-- Saturated roots are excluded also at cost five in the three-pure
counterexample branch. The inexpensive `W<=4` branch uses the existing theorem. -/
theorem missing_side_roots_lt {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 5) :
    (F.filter (OnOpenSide s)).card < k := by
  by_cases hcheap : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 4
  · exact missing_side_roots_lt_of_pure_le_four (by omega) F hacyc s hmissing (by omega) hcheap
  have hq := missing_side_preserved_card_le (by omega) F hacyc s hmissing
  by_contra h
  have hsat : (F.filter (OnOpenSide s)).card = k := by omega
  obtain ⟨ha, hb⟩ := saturated_missing_side_corner_holes hk F hacyc s hmissing hf hp hsat hW
  have hcost := offside_deficiency_ge_six_of_two_corner_holes (by omega) F hacyc s
    (sideChart s (⟨0, by omega⟩, ⟨0, by omega⟩))
    (sideChart s (⟨3 * k + 1, by omega⟩, ⟨0, by omega⟩))
    ((sideChart_corner s _).mpr (by simp [BoundarySix.Corner]))
    ((sideChart_corner s _).mpr (by simp [BoundarySix.Corner]))
    (by intro he; have he' := sideChart_injective s he; simp [Prod.ext_iff, Fin.ext_iff] at he')
    ha hb
  omega

end GridGraphs.CarrierLayers.ThreeCarrier
