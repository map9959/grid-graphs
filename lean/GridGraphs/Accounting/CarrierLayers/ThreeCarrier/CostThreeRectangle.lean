import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostThreePurity

/-! # The W3 rectangle with one physical frame deletion

The deletion is not localized to eight configurations. Keeping its position
arbitrary allows at most two defective edges, which still suffices at k=5.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- All actual nonpure preserved vertices, and only those, lie in the enlarged rectangle. -/
theorem cost_three_nonpure_rectangle_iff {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3)
    (u : GridVertex (3 * k + 2) (3 * k + 2)) (hu : sideChart s u ∈ F) :
    ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk
      ⟨sideChart s u, hu⟩ ∉ pureBoundaryCarriers F ↔
      2 ≤ u.1.val ∧ u.1.val + 2 < 3 * k + 2 ∧ u.2.val + 2 < 3 * k + 2 := by
  let v : (↑F : Set _) := ⟨sideChart s u, hu⟩
  let C := ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk v
  have hv : v ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  constructor
  · intro hC
    by_cases hb : IsGridBoundary (sideChart s u)
    · have hs : OnOpenSide s (sideChart s u) := by
        by_contra hs
        exact hC (cost_three_offside_carrier_pure hk F hacyc s hW C v hv hb hs)
      have hs' := (sideChart_openSide s u).mp hs
      have hpos := root_positions_of_offside_deficiency_le_five (by omega) F hacyc s hmissing
        (by omega) _ hu hs
      rw [sideChart_position] at hpos
      omega
    by_cases hr : IsNextRing (sideChart s u)
    · obtain ⟨a, ha, han, he⟩ := cost_three_nextRing_chart hk F hacyc s hW _ hu hr
      have he' := sideChart_injective s he
      have hx := congrArg (fun v : GridVertex (3 * k + 2) (3 * k + 2) => v.1.val) he'
      have hy := congrArg (fun v : GridVertex (3 * k + 2) (3 * k + 2) => v.2.val) he'
      dsimp only at hx hy
      omega
    · have hbu : ¬ IsGridBoundary u := fun h => hb ((sideChart_boundary s u).mpr h)
      have hru : ¬ IsNextRing u := by
        intro h
        apply hr
        unfold sideChart
        split_ifs <;> dsimp [IsNextRing] at h ⊢ <;> omega
      unfold IsGridBoundary at hbu
      unfold IsNextRing at hru
      omega
  · rintro ⟨hx, hxn, hyn⟩ hC
    have hb := (sideChart_boundary s u).mp ((mem_filter.mp hC).2 v hv)
    have hy : u.2.val = 0 := by unfold IsGridBoundary at hb; omega
    exact hmissing C hC v hv ((sideChart_openSide s u).mpr ⟨hy, by omega, by omega⟩)

/-- The actual pure mass at W3 is 9k+1. -/
theorem cost_three_pure_mass {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3) :
    (pureBoundaryVertices F).card = 9 * k + 1 := by
  classical
  have himage : (pureBoundaryVertices F).image Subtype.val =
      F.filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hv
      obtain ⟨C, hC, huC⟩ := mem_biUnion.mp hu
      have huC' := Set.mem_toFinset.mp huC
      exact mem_filter.mpr ⟨u.property, (mem_filter.mp hC).2 u huC', hmissing C hC u huC'⟩
    · intro hv
      obtain ⟨hvF, hvb, hvs⟩ := mem_filter.mp hv
      let u : (↑F : Set _) := ⟨v, hvF⟩
      let C := ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk u
      have hu : u ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
      have hC := cost_three_offside_carrier_pure hk F hacyc s hW C u hu hvb hvs
      exact mem_image.mpr ⟨u, mem_biUnion.mpr ⟨C, hC, Set.mem_toFinset.mpr hu⟩, rfl⟩
  have hmass := congrArg Finset.card himage
  rw [card_image_of_injective _ Subtype.val_injective] at hmass
  let O := univ.filter (fun v : GridVertex (3 * k + 2) (3 * k + 2) =>
    IsGridBoundary v ∧ ¬ OnOpenSide s v)
  let B := univ.filter (fun v : GridVertex (3 * k + 2) (3 * k + 2) => IsGridBoundary v)
  have hB : B.card = 4 * (3 * k + 2) - 4 := by
    simpa [B] using BoundaryFiveConstruction.boundary_card (by omega : 7 ≤ 3 * k + 2)
  have hpart := card_filter_add_card_filter_not (s := B) (p := OnOpenSide s)
  have hside : B.filter (OnOpenSide s) = univ.filter (OnOpenSide s) := by
    ext v
    simp only [B, mem_filter, mem_univ, true_and]
    exact ⟨And.right, fun h => ⟨openSide_boundary h, h⟩⟩
  have hoff : B.filter (fun v => ¬ OnOpenSide s v) = O := by ext v; simp [B, O]
  rw [hside, hoff] at hpart
  have hsidecard := openSide_card (by omega : 2 ≤ 3 * k + 2) s
  have hsplit := card_sdiff_add_card_inter O F
  have hOF : O ∩ F = F.filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) := by
    ext v
    simp [O, and_comm, and_left_comm]
  have hOU : O \ F = (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) := by
    ext v
    simp [O, and_comm, and_left_comm]
  rw [hOF, hOU, (cost_three_boundary (by omega) F hacyc s hW).2.1] at hsplit
  omega

/-- The frame protecting the rectangle is full except possibly at one
noncorner vertex. Far near-corner witnesses lie outside this protected frame. -/
theorem cost_three_frame_defect {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) (s : Fin 4)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3) :
    ∃ c : GridVertex (3 * k + 2) (3 * k + 2), ¬ BoundarySix.Corner c ∧
      ∀ u : GridVertex (3 * k + 2) (3 * k + 2),
        (((u.1.val = 0 ∨ u.1.val = 3 * k + 1) ∧ u.2.val < 3 * k) ∨
          (u.2.val = 3 * k + 1 ∧ 2 ≤ u.1.val ∧ u.1.val < 3 * k)) →
        u ≠ c → sideChart s u ∈ F := by
  obtain ⟨a, b, c', ha, hb, _, _, _, hcCorner, hO⟩ := cost_three_far_holes_plus_one hk F hacyc s hW
  obtain ⟨c, hc⟩ := sideChart_surjective s c'
  refine ⟨c, ?_, ?_⟩
  · intro h
    exact hcCorner (hc ▸ (sideChart_corner s c).mpr h)
  · intro u hu huc
    by_contra hU
    have hm : sideChart s u ∈ (univ \ F).filter
        (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) := by
      refine mem_filter.mpr ⟨by simp [hU], ?_, ?_⟩
      · rw [sideChart_boundary]
        unfold IsGridBoundary
        omega
      · rw [sideChart_openSide]
        omega
    rw [hO, ← hc] at hm
    simp only [mem_insert, mem_singleton, (sideChart_injective s).eq_iff] at hm
    rcases hm with hm | hm | hm
    · rcases ha with ha | ha <;> rw [ha] at hm <;>
        have hx := congrArg (fun v : GridVertex (3 * k + 2) (3 * k + 2) => v.1.val) hm <;>
        have hy := congrArg (fun v : GridVertex (3 * k + 2) (3 * k + 2) => v.2.val) hm <;>
        dsimp only at hx hy <;> omega
    · rcases hb with hb | hb <;> rw [hb] at hm <;>
        have hx := congrArg (fun v : GridVertex (3 * k + 2) (3 * k + 2) => v.1.val) hm <;>
        have hy := congrArg (fun v : GridVertex (3 * k + 2) (3 * k + 2) => v.2.val) hm <;>
        dsimp only at hx hy <;> omega
    · exact huc hm

end GridGraphs.CarrierLayers.ThreeCarrier
