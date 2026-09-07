import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoCapacity
import GridGraphs.Accounting.CarrierLayers.CoveredBoundary

/-! # The full nonpure W2 rectangle

In `sideChart s (x,y)`, x is the column along the missing side and y is
physical depth. The nonpure rectangle includes depths zero and one, rather
than discarding root spokes or shallow horizontal carriers.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- A preserved charted vertex is nonpure exactly when it belongs to the
rectangle `2<=x<=n-3, 0<=y<=n-3`. This is an equivalence for actual components. -/
theorem cost_two_nonpure_rectangle_iff {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2)
    (u : GridVertex n n) (hu : sideChart s u ∈ F) :
    ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk ⟨sideChart s u, hu⟩ ∉
      pureBoundaryCarriers F ↔ 2 ≤ u.1.val ∧ u.1.val + 2 < n ∧ u.2.val + 2 < n := by
  let v : (↑F : Set _) := ⟨sideChart s u, hu⟩
  let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk v
  have hv : v ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  constructor
  · intro hC
    by_cases hb : IsGridBoundary (sideChart s u)
    · have hs : OnOpenSide s (sideChart s u) := by
        by_contra hs
        exact hC (cost_two_offside_carrier_pure hn F hacyc s hW C v hv hb hs)
      have hs' := (sideChart_openSide s u).mp hs
      have hpos := root_positions_of_offside_deficiency_le_five hn F hacyc s hmissing
        (by omega) _ hu hs
      rw [sideChart_position] at hpos
      omega
    by_cases hr : IsNextRing (sideChart s u)
    · obtain ⟨a, ha, han, he⟩ := cost_two_nextRing_chart hn F hacyc s hW _ hu hr
      have he' := sideChart_injective s he
      have hx := congrArg (fun v : GridVertex n n => v.1.val) he'
      have hy := congrArg (fun v : GridVertex n n => v.2.val) he'
      dsimp only at hx hy
      omega
    · fin_cases s <;> simp [sideChart, IsGridBoundary, IsNextRing] at hb hr <;> omega
  · rintro ⟨hx, hxn, hyn⟩ hC
    have hb := (sideChart_boundary s u).mp ((mem_filter.mp hC).2 v hv)
    have hy : u.2.val = 0 := by unfold IsGridBoundary at hb; omega
    exact hmissing C hC v hv ((sideChart_openSide s u).mpr ⟨hy, by omega, by omega⟩)

/-- Pure preserved vertices are exactly the preserved off-side boundary.
This retains the actual carrier union used by the global accounting APIs. -/
theorem cost_two_pure_vertices_image {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) :
    (pureBoundaryVertices F).image Subtype.val =
      F.filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) := by
  classical
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
    let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk u
    have hu : u ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
    have hC := cost_two_offside_carrier_pure hn F hacyc s hW C u hu hvb hvs
    exact mem_image.mpr ⟨u, mem_biUnion.mpr ⟨C, hC, Set.mem_toFinset.mpr hu⟩, rfl⟩

/-- The actual pure mass is `9k+2`; neither `p=3` nor a score bound is
needed for this mass calculation once the side is missing and W2 holds. -/
theorem cost_two_pure_mass {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) :
    (pureBoundaryVertices F).card = 9 * k + 2 := by
  classical
  have hmass := congrArg Finset.card (cost_two_pure_vertices_image (by omega) F hacyc s hmissing hW)
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
  rw [hOF, hOU, (cost_two_boundary (by omega) F hacyc s hW).2.1] at hsplit
  omega

/-- Off-side boundary vertices away from the four far near-corner positions
are preserved. In particular both side boundary edges facing the rectangle
and the central bottom boundary are full. -/
theorem cost_two_frame_mem {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2)
    (u : GridVertex (3 * k + 2) (3 * k + 2))
    (hu : ((u.1.val = 0 ∨ u.1.val = 3 * k + 1) ∧ u.2.val < 3 * k) ∨
      (u.2.val = 3 * k + 1 ∧ 2 ≤ u.1.val ∧ u.1.val < 3 * k)) :
    sideChart s u ∈ F := by
  by_contra hU
  obtain ⟨a, b, ha, hb, heq⟩ := cost_two_exact_far_holes hk F hacyc s hW
  have hm : sideChart s u ∈ (univ \ F).filter
      (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) := by
    refine mem_filter.mpr ⟨by simp [hU], ?_, ?_⟩
    · rw [sideChart_boundary]
      unfold IsGridBoundary
      omega
    · rw [sideChart_openSide]
      omega
  rw [heq] at hm
  simp only [mem_insert, mem_singleton] at hm
  rcases hm with hm | hm
  · have he := sideChart_injective s hm
    rcases ha with ha | ha <;> rw [ha] at he <;>
      have hx := congrArg (fun v : GridVertex (3 * k + 2) (3 * k + 2) => v.1.val) he <;>
      have hy := congrArg (fun v : GridVertex (3 * k + 2) (3 * k + 2) => v.2.val) he <;>
      dsimp only at hx hy <;> omega
  · have he := sideChart_injective s hm
    rcases hb with hb | hb <;> rw [hb] at he <;>
      have hx := congrArg (fun v : GridVertex (3 * k + 2) (3 * k + 2) => v.1.val) he <;>
      have hy := congrArg (fun v : GridVertex (3 * k + 2) (3 * k + 2) => v.2.val) he <;>
      dsimp only at hx hy <;> omega

/-- A depth-directed FF edge in the nonpure rectangle cannot use either
outer column. Its side-facing boundary edge would complete a six-cycle. -/
theorem cost_two_vertical_edge_columns {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2)
    (x y : Nat) (hx : 2 ≤ x ∧ x + 2 < 3 * k + 2) (hy : y + 3 < 3 * k + 2)
    (h0 : sideChart s (⟨x, by omega⟩, ⟨y, by omega⟩) ∈ F)
    (h1 : sideChart s (⟨x, by omega⟩, ⟨y + 1, by omega⟩) ∈ F) :
    3 ≤ x ∧ x ≤ 3 * k - 2 := by
  let n := 3 * k + 2
  have hP := sideChart_acyclic s F hacyc
  have hleft : x ≠ 2 := by
    intro he
    subst x
    have hb0 := cost_two_frame_mem hk F hacyc s hW
      (⟨0, by omega⟩, ⟨y, by omega⟩) (Or.inl ⟨Or.inl rfl, by dsimp; omega⟩)
    have hb1 := cost_two_frame_mem hk F hacyc s hW
      (⟨0, by omega⟩, ⟨y + 1, by omega⟩) (Or.inl ⟨Or.inl rfl, by dsimp; omega⟩)
    exact forced_rectangle_two_rows_false (⟨0, by omega⟩ : Fin (n - 2))
      (⟨y, by omega⟩ : Fin (n - 1)) hP hb0 hb1 h0 h1
  have hright : x ≠ 3 * k - 1 := by
    intro he
    have hstep : x + 2 = 3 * k + 1 := by omega
    have hb0 := cost_two_frame_mem hk F hacyc s hW
      (⟨3 * k + 1, by omega⟩, ⟨y, by omega⟩) (Or.inl ⟨Or.inr rfl, by dsimp; omega⟩)
    have hb1 := cost_two_frame_mem hk F hacyc s hW
      (⟨3 * k + 1, by omega⟩, ⟨y + 1, by omega⟩) (Or.inl ⟨Or.inr rfl, by dsimp; omega⟩)
    apply forced_rectangle_two_rows_false (⟨x, by omega⟩ : Fin (n - 2))
      (⟨y, by omega⟩ : Fin (n - 1)) hP h0 h1
    · change sideChart s (⟨x + 2, by omega⟩, ⟨y, by omega⟩) ∈ F
      simpa only [hstep] using hb0
    · change sideChart s (⟨x + 2, by omega⟩, ⟨y + 1, by omega⟩) ∈ F
      simpa only [hstep] using hb1
  omega

/-- Transposing local coordinates transports only the forced graph. -/
theorem chart_transpose_acyclic {n : Nat} (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) (s : Fin 4) :
    (forcedEdgeGraph (gridGraph n n) {v | sideChart s (v.2, v.1) ∈ F}).IsAcyclic := by
  let f : forcedEdgeGraph (gridGraph n n) {v | sideChart s (v.2, v.1) ∈ F} →g
      forcedEdgeGraph (gridGraph n n) (↑F : Set _) :=
    { toFun := fun v => sideChart s (v.2, v.1)
      map_rel' := fun h => ⟨(sideChart_adj s _ _).mpr (by
        simpa [gridGraph, adjacent, or_comm] using h.1), h.2⟩ }
  apply hacyc.comap f
  intro u v he
  have h := sideChart_injective s he
  exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

/-- Every horizontal FF edge in the nonpure rectangle is strictly interior
in depth. This includes shallow depth-one edges, and excludes the last deep
row using its full opposite boundary edge. -/
theorem cost_two_horizontal_edge_rows {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2)
    (x y : Nat) (hx : 2 ≤ x ∧ x + 3 < 3 * k + 2) (hy : y + 2 < 3 * k + 2)
    (h0 : sideChart s (⟨x, by omega⟩, ⟨y, by omega⟩) ∈ F)
    (h1 : sideChart s (⟨x + 1, by omega⟩, ⟨y, by omega⟩) ∈ F) :
    1 ≤ y ∧ y + 3 < 3 * k + 2 := by
  let n := 3 * k + 2
  have hzero : y ≠ 0 := by
    intro he
    subst y
    let u : GridVertex n n := sideChart s (⟨x, by omega⟩, ⟨0, by omega⟩)
    let v : GridVertex n n := sideChart s (⟨x + 1, by omega⟩, ⟨0, by omega⟩)
    have hus : OnOpenSide s u := (sideChart_openSide s _).mpr ⟨rfl, by dsimp; omega⟩
    have hvs : OnOpenSide s v := (sideChart_openSide s _).mpr ⟨rfl, by dsimp; omega⟩
    obtain ⟨w, hw, hwr, huw⟩ := missing_side_root_inward (by omega) F hacyc s hmissing u h0 hus
    obtain ⟨z, hz, hzr, hvz⟩ := missing_side_root_inward (by omega) F hacyc s hmissing v h1 hvs
    have hspace := radial_pair_spacing (by omega) F hacyc s h0 h1 hw hz hus hvs
      hwr hzr huw hvz (by dsimp [u, v]; rw [sideChart_position, sideChart_position]; dsimp; omega)
    dsimp [u, v] at hspace
    rw [sideChart_position, sideChart_position] at hspace
    dsimp only at hspace
    omega
  have hlast : y ≠ 3 * k - 1 := by
    intro he
    have hy' : y + 2 = 3 * k + 1 := by omega
    have hb0 := cost_two_frame_mem hk F hacyc s hW
      (⟨x, by omega⟩, ⟨3 * k + 1, by omega⟩) (Or.inr ⟨rfl, by dsimp; omega⟩)
    have hb1 := cost_two_frame_mem hk F hacyc s hW
      (⟨x + 1, by omega⟩, ⟨3 * k + 1, by omega⟩) (Or.inr ⟨rfl, by dsimp; omega⟩)
    apply forced_rectangle_two_rows_false (⟨y, by omega⟩ : Fin (n - 2))
      (⟨x, by omega⟩ : Fin (n - 1)) (chart_transpose_acyclic F hacyc s) h0 h1
    · change sideChart s (⟨x, by omega⟩, ⟨y + 2, by omega⟩) ∈ F
      simpa only [hy'] using hb0
    · change sideChart s (⟨x + 1, by omega⟩, ⟨y + 2, by omega⟩) ∈ F
      simpa only [hy'] using hb1
  omega

end GridGraphs.CarrierLayers.ThreeCarrier
