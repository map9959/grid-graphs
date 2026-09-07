import GridGraphs.Accounting.CarrierLayers.FourCarrier.ChartShadow

/-! # At most two shallow preimages on the missing side

Three positions in one parallel carrier would cast a five-position hole gap.
The actual fixed-map preimages are then injected into two consecutive positions.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- A chart-depth-one carrier segment on the missing side has span at most
one in a four-pure counterexample. Its expanded shadow cannot exceed four. -/
theorem chart_carrier_span_le_one {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 4)
    (C : ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).ConnectedComponent)
    (u v : (↑F : Set (GridVertex (3 * k + 2) (3 * k + 2))))
    (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (a b : Fin (3 * k + 2))
    (hua : u.val = sideChart s (a, ⟨1, by omega⟩))
    (hvb : v.val = sideChart s (b, ⟨1, by omega⟩))
    (ha : 0 < a.val ∧ a.val + 1 < 3 * k + 2)
    (hb : 0 < b.val ∧ b.val + 1 < 3 * k + 2) : b.val ≤ a.val + 1 := by
  by_cases hab : a.val < b.val
  · have hgeom := four_pure_missing_side_gap_geometry hk F hacyc s hmissing hf hp
    have ha' := chart_depth_one_away_from_ends (by omega) F hacyc hgeom.1 s a ha (hua ▸ u.property)
    have hb' := chart_depth_one_away_from_ends (by omega) F hacyc hgeom.1 s b hb (hvb ▸ v.property)
    have hgap := hgeom.2.2 (a.val - 1) (b.val + 1) (by omega) (by omega) (by omega) (by
      intro z hz hzs hlo hhi
      let t : Fin (3 * k + 2) := ⟨sidePosition s z, by have := sidePosition_bounds hzs; omega⟩
      have hs : OnOpenSide s (sideChart s (t, ⟨0, by omega⟩)) :=
        (sideChart_openSide s _).mpr (by have := sidePosition_bounds hzs; dsimp [t]; omega)
      have he := sidePosition_injective hzs hs (by rw [sideChart_position])
      have hU := chart_carrier_expanded_shadow (by omega) F hacyc s C u v hu hv a b hua hvb
        (by omega) hab hb.2 t ⟨hlo, hhi⟩
      exact hU (he ▸ hz))
    omega
  · omega

/-- Along a fixed-map side, a next-ring vertex is determined by its side
position. This is a coordinate injection, not an equivariance assertion. -/
theorem boundary_map_side_position_injective {n : Nat} (hn : 5 ≤ n) (s : Fin 4)
    (w z : {v : GridVertex n n // IsNextRing v})
    (hws : OnOpenSide s (nextRingBoundaryMap hn w))
    (hzs : OnOpenSide s (nextRingBoundaryMap hn z))
    (he : sidePosition s w.val = sidePosition s z.val) : w.val = z.val := by
  obtain ⟨a, _, _, ha⟩ := boundary_map_side_chart hn w s hws
  obtain ⟨b, _, _, hb⟩ := boundary_map_side_chart hn z s hzs
  rw [ha, hb, sideChart_position, sideChart_position] at he
  dsimp only at he
  rw [ha, hb, Fin.ext he]

/-- Same-carrier preimages on the missing side occupy at most two consecutive
positions. This applies to any actual carrier, not only the unique shallow one. -/
theorem same_carrier_map_positions_le_add_one {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 4)
    (w z : (↑F : Set (GridVertex (3 * k + 2) (3 * k + 2))))
    (hwr : IsNextRing w.val) (hzr : IsNextRing z.val)
    (hws : OnOpenSide s (nextRingBoundaryMap (by omega) ⟨w.val, hwr⟩))
    (hzs : OnOpenSide s (nextRingBoundaryMap (by omega) ⟨z.val, hzr⟩))
    (he : ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk w =
      ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk z) :
    sidePosition s z.val ≤ sidePosition s w.val + 1 := by
  obtain ⟨a, ha0, ha1, hwa⟩ := boundary_map_side_chart (by omega) ⟨w.val, hwr⟩ s hws
  obtain ⟨b, hb0, hb1, hzb⟩ := boundary_map_side_chart (by omega) ⟨z.val, hzr⟩ s hzs
  dsimp only at hwa hzb
  let C := ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk w
  have hw : w ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have hz : z ∈ C.supp := by
    dsimp [C]
    rw [he]
    simp [ConnectedComponent.mem_supp_iff]
  have h := chart_carrier_span_le_one hk F hacyc s hmissing hf hp C w z hw hz a b hwa hzb
    ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
  rw [hwa, hzb, sideChart_position, sideChart_position]
  exact h

/-- The unique shallow carrier contributes at most two actual preimages to
the chosen side of the fixed boundary injection. -/
theorem shallow_side_preimages_card_le_two {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 4) :
    (shallowSidePreimages (by omega) F s).card ≤ 2 := by
  classical
  let E := F.filter IsNextRing
  let J := shallowSidePreimages (by omega) F s
  let pos : E → Nat := fun v => sidePosition s v.val
  by_cases hJ : J = ∅
  · simp only [J] at hJ
    simp [hJ]
  let S := J.image pos
  have hS : S.Nonempty := (nonempty_iff_ne_empty.mpr hJ).image pos
  obtain ⟨x, hx, hxmin⟩ := mem_image.mp (min'_mem S hS)
  have hlow (v : J) : pos x ≤ pos v.val := by
    rw [hxmin]
    exact min'_le S _ (mem_image.mpr ⟨v.val, v.property, rfl⟩)
  have hN := (four_pure_missing_side_shallow_eq_one hk F hacyc s hmissing hf hp).1
  have hhigh (v : J) : pos v.val ≤ pos x + 1 := by
    have hx' := (mem_filter.mp hx).2
    have hv' := (mem_filter.mp v.property).2
    have he := (Finset.card_le_one.mp (by omega : (nextRingCarriers F).card ≤ 1)) _ hx'.2 _ hv'.2
    exact same_carrier_map_positions_le_add_one hk F hacyc s hmissing hf hp
      ⟨x.val, (mem_filter.mp x.property).1⟩
      ⟨v.val.val, (mem_filter.mp v.val.property).1⟩
      (mem_filter.mp x.property).2 (mem_filter.mp v.val.property).2 hx'.1 hv'.1 he
  let f : J → Fin 2 := fun v => ⟨pos v.val - pos x, by have := hhigh v; omega⟩
  have hinj : Function.Injective f := by
    intro v w he
    have he' := congrArg Fin.val he
    have hv := hlow v
    have hw := hlow w
    have hepos : pos v.val = pos w.val := by dsimp [f] at he'; omega
    have heq := boundary_map_side_position_injective (by omega) s
      ⟨v.val.val, (mem_filter.mp v.val.property).2⟩
      ⟨w.val.val, (mem_filter.mp w.val.property).2⟩
      (mem_filter.mp v.property).2.1 (mem_filter.mp w.property).2.1 hepos
    exact Subtype.ext (Subtype.ext heq)
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hinj

end GridGraphs.CarrierLayers.FourCarrier
