import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoGeometry

/-! # W2 layer loss and exclusion of the baseline deep count

Root-neighbor columns are disjoint by spacing. The two end columns are
additional losses because the second-position roots have been excluded.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- Two physical neighbor shadows per root are disjoint and avoid `B`.
Both shadows and `B` lie in the interval with the two end columns removed. -/
theorem spaced_root_shadow_count {n : Nat} (hn : 5 ≤ n) (A B : Finset Nat)
    (hA : ∀ a ∈ A, 3 ≤ a ∧ a + 3 < n)
    (hB : ∀ b ∈ B, 2 ≤ b ∧ b + 2 < n)
    (hspace : ∀ a ∈ A, ∀ b ∈ A, a < b → a + 3 ≤ b)
    (havoid : ∀ a ∈ A, ∀ b ∈ B, ¬ (a + 1 = b ∨ b + 1 = a)) :
    B.card + 2 * A.card + 4 ≤ n := by
  classical
  let L := A.image (fun a => a - 1)
  let R := A.image (fun a => a + 1)
  have hL : L.card = A.card := by
    apply card_image_iff.mpr
    intro a ha b hb he
    dsimp only at he
    have := hA a ha
    have := hA b hb
    omega
  have hR : R.card = A.card := card_image_of_injective _ (by intro a b he; dsimp only at he; omega)
  have hLR : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha, he⟩ := mem_image.mp hx
    obtain ⟨b, hb, he'⟩ := mem_image.mp hy
    have hab := hA a ha
    have hba := hA b hb
    have hlt : b < a := by omega
    have := hspace b hb a ha hlt
    omega
  have hSB : Disjoint (L ∪ R) B := by
    apply Finset.disjoint_left.mpr
    intro b hb hbB
    rcases mem_union.mp hb with hb | hb
    · obtain ⟨a, ha, he⟩ := mem_image.mp hb
      have := hA a ha
      exact havoid a ha b hbB (Or.inr (by omega))
    · obtain ⟨a, ha, he⟩ := mem_image.mp hb
      exact havoid a ha b hbB (Or.inl he)
  have hsub : (L ∪ R) ∪ B ⊆ Icc 2 (n - 3) := by
    intro x hx
    apply mem_Icc.mpr
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hx with hx | hx
      · obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
        have := hA a ha
        omega
      · obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
        have := hA a ha
        omega
    · have := hB x hx
      omega
  have hcount := card_le_card hsub
  rw [card_union_of_disjoint hSB, card_union_of_disjoint hLR, hL, hR, Nat.card_Icc] at hcount
  omega

/-- At W2 every next-ring vertex is on the root side, where the `2q` root
shadows and two end columns are unavailable. -/
theorem cost_two_nextRing_add_twice_roots {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) :
    (F.filter IsNextRing).card + 2 * (F.filter (OnOpenSide s)).card + 2 ≤ 3 * k := by
  classical
  let A := (F.filter (OnOpenSide s)).image (sidePosition s)
  let B := (F.filter IsNextRing).image (sidePosition s)
  have hcorners := (cost_two_boundary (by omega) F hacyc s hW).1
  have hAcard : A.card = (F.filter (OnOpenSide s)).card := by
    apply card_image_iff.mpr
    intro u hu v hv he
    exact sidePosition_injective (mem_filter.mp hu).2 (mem_filter.mp hv).2 he
  have hBcard : B.card = (F.filter IsNextRing).card := by
    apply card_image_iff.mpr
    intro u hu v hv he
    obtain ⟨a, _, _, heu⟩ := cost_two_nextRing_chart (by omega) F hacyc s hW
      u (mem_filter.mp hu).1 (mem_filter.mp hu).2
    obtain ⟨b, _, _, hev⟩ := cost_two_nextRing_chart (by omega) F hacyc s hW
      v (mem_filter.mp hv).1 (mem_filter.mp hv).2
    rw [heu, hev, sideChart_position, sideChart_position] at he
    change a.val = b.val at he
    rw [heu, hev, Fin.ext he]
  have hA : ∀ a ∈ A, 3 ≤ a ∧ a + 3 < 3 * k + 2 := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact root_positions_of_corners_preserved hk F hacyc s hmissing hf hp hcorners
      v (mem_filter.mp hv).1 (mem_filter.mp hv).2
  have hB : ∀ b ∈ B, 2 ≤ b ∧ b + 2 < 3 * k + 2 := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
    obtain ⟨a, ha0, han, rfl⟩ := cost_two_nextRing_chart (by omega) F hacyc s hW
      v (mem_filter.mp hv).1 (mem_filter.mp hv).2
    simpa only [sideChart_position] using And.intro ha0 han
  have hspace : ∀ a ∈ A, ∀ b ∈ A, a < b → a + 3 ≤ b := by
    intro a ha b hb hlt
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
    obtain ⟨w, hw, hwr, huw⟩ := missing_side_root_inward (by omega) F hacyc s hmissing
      u (mem_filter.mp hu).1 (mem_filter.mp hu).2
    obtain ⟨z, hz, hzr, hvz⟩ := missing_side_root_inward (by omega) F hacyc s hmissing
      v (mem_filter.mp hv).1 (mem_filter.mp hv).2
    exact radial_pair_spacing (by omega) F hacyc s
      (mem_filter.mp hu).1 (mem_filter.mp hv).1 hw hz
      (mem_filter.mp hu).2 (mem_filter.mp hv).2 hwr hzr huw hvz hlt
  have havoid : ∀ a ∈ A, ∀ b ∈ B, ¬ (a + 1 = b ∨ b + 1 = a) := by
    intro a ha b hb hdiag
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
    obtain ⟨a, _, _, he⟩ := cost_two_nextRing_chart (by omega) F hacyc s hW
      v (mem_filter.mp hv).1 (mem_filter.mp hv).2
    obtain ⟨z, rfl⟩ := sideChart_surjective s u
    have hzs := (sideChart_openSide s z).mp (mem_filter.mp hu).2
    have hz : z = (z.1, ⟨0, by omega⟩) := Prod.ext rfl (Fin.ext hzs.1)
    rw [he, sideChart_position, sideChart_position] at hdiag
    dsimp only at hdiag
    have hhole := chart_diagonal_boundary_hole (by omega) F hacyc s a z.1
      (by omega) (he ▸ (mem_filter.mp hv).1)
    exact hhole (by simpa only [← hz] using (mem_filter.mp hu).1)
  have hcount := spaced_root_shadow_count (by omega) A B hA hB hspace havoid
  rw [hAcard, hBcard] at hcount
  omega

/-- The physical boundary/next-ring gap `K=|U_boundary|-|F_nextRing|`
satisfies `K+m>=k+4`, hence `K>=k+1`. -/
theorem cost_two_boundary_layer_gap {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) :
    let K := ((univ \ F).filter IsGridBoundary).card - (F.filter IsNextRing).card
    k + 4 ≤ K + (k - (F.filter (OnOpenSide s)).card) ∧ k + 1 ≤ K := by
  dsimp only
  have hE := cost_two_nextRing_add_twice_roots hk F hacyc s hmissing hf hp hW
  have hprofile := three_pure_missing_side_exact_profile hk F hacyc s hmissing hf hp
  dsimp only at hprofile
  have hholes := side_holes_add_roots (by omega) F s
  have hO := (cost_two_boundary (by omega) F hacyc s hW).2.1
  let U := (univ \ F).filter IsGridBoundary
  have hpart := card_filter_add_card_filter_not (s := U) (p := OnOpenSide s)
  have hS : U.filter (OnOpenSide s) = (univ \ F).filter (OnOpenSide s) := by
    ext v
    simp only [U, mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩,
      fun h => ⟨⟨h.1, openSide_boundary h.2⟩, h.2⟩⟩
  have hO' : U.filter (fun v => ¬ OnOpenSide s v) =
      (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) := by
    ext v
    simp [U, and_assoc]
  rw [hS, hO', hO] at hpart
  dsimp [U] at hpart
  omega

/-- W2 excludes the former baseline `d=k-1`: at least `k` actual carriers
reach the deep layer. This is obtained from global capacity with the physical
layer gap, not by charging inward witnesses as distinct carriers. -/
theorem cost_two_deep_carriers_ge {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) :
    k ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent - 3 - (nextRingCarriers F).card := by
  have hgap := (cost_two_boundary_layer_gap hk F hacyc s hmissing hf hp hW).2
  have hcap := card_le_layers_without_nextRing_carriers (by omega) F hacyc
  have hE := forced_nextRing_card_le_compl_boundary_card (by omega) F hacyc
  have hper : (F.filter IsGridBoundary).card +
      ((univ \ F).filter IsGridBoundary).card = 12 * k + 4 := by
    have he : (F.filter IsGridBoundary) ∪ ((univ \ F).filter IsGridBoundary) =
        univ.filter IsGridBoundary := by
      ext v
      by_cases hv : v ∈ F <;> simp [hv]
    have hd : Disjoint (F.filter IsGridBoundary) ((univ \ F).filter IsGridBoundary) := by
      apply Finset.disjoint_left.mpr
      intro v hv hu
      exact (mem_sdiff.mp (mem_filter.mp hu).1).2 (mem_filter.mp hv).1
    rw [← card_union_of_disjoint hd, he]
    have h := BoundaryFiveConstruction.boundary_card (by omega : 7 ≤ 3 * k + 2)
    have h' : (univ.filter (fun v : GridVertex (3 * k + 2) (3 * k + 2) =>
        IsGridBoundary v)).card = 4 * (3 * k + 2) - 4 := by simpa using h
    exact h'.trans (by omega)
  rw [hp] at hcap
  by_contra h
  have hd : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent - 3 - (nextRingCarriers F).card ≤ k - 1 := by omega
  have hm := Nat.mul_le_mul_left (3 * k + 2 - 4) hd
  have hk1 : k - 1 + 1 = k := by omega
  have hn : 3 * k + 2 - 4 + 2 = 3 * k := by omega
  have hlayers : (F.filter IsGridBoundary).card + (F.filter IsNextRing).card ≤ 11 * k + 3 := by
    omega
  nlinarith

/-- The paper's shallow-carrier inequality holds in W2: `h+m<=z`.
In particular the entire equality branch `h+m=z+1` is excluded. -/
theorem cost_two_shallow_slack {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) :
    (nextRingCarriers F).card + (k - (F.filter (OnOpenSide s)).card) ≤
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent - (F.filter (OnOpenSide s)).card - 3 := by
  have hd := cost_two_deep_carriers_ge hk F hacyc s hmissing hf hp hW
  have hq := (three_pure_missing_side_root_cost hk F hacyc s hmissing hf hp).1
  omega

/-- A sharp-target upper bound for the entire W2 baseline-deep branch.
The hypothesis is on the actual number of deep carriers, not a carrier assignment. -/
theorem card_le_target_of_cost_two_deep_le_baseline {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2)
    (hd : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent - 3 - (nextRingCarriers F).card ≤ k - 1) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  by_contra h
  have hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card := by omega
  have hdeep := cost_two_deep_carriers_ge hk F hacyc s hmissing hf hp hW
  omega

end GridGraphs.CarrierLayers.ThreeCarrier
