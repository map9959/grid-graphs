import GridGraphs.Accounting.CarrierLayers.FourCarrier.DeepSaturation

/-! # A deep second-position root in the exceptional image case

Two distinct shallow preimages cast a four-position gap. Its forced second
root cannot reuse that shallow carrier, because the carrier lies inward of
an actual boundary hole.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

theorem deep_second_root_of_two_shallow_preimages {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 4)
    (hJ : 2 ≤ (shallowSidePreimages (by omega) F s).card) :
    ∃ u : (↑F : Set (GridVertex (3 * k + 2) (3 * k + 2))),
      OnOpenSide s u.val ∧ (sidePosition s u.val = 2 ∨ sidePosition s u.val = 3 * k - 1) ∧
      ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk u ∉
        nextRingCarriers F := by
  classical
  let E := F.filter IsNextRing
  let J := shallowSidePreimages (by omega) F s
  change 2 ≤ J.card at hJ
  have hN := (four_pure_missing_side_shallow_eq_one hk F hacyc s hmissing hf hp).1
  have hgeom := four_pure_missing_side_gap_geometry hk F hacyc s hmissing hf hp
  have ordered (x y : E) (hx : x ∈ J) (hy : y ∈ J)
      (hlt : sidePosition s x.val < sidePosition s y.val) :
      ∃ u : (↑F : Set (GridVertex (3 * k + 2) (3 * k + 2))),
        OnOpenSide s u.val ∧ (sidePosition s u.val = 2 ∨ sidePosition s u.val = 3 * k - 1) ∧
        ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk u ∉
          nextRingCarriers F := by
    let w : (↑F : Set _) := ⟨x.val, (mem_filter.mp x.property).1⟩
    let z : (↑F : Set _) := ⟨y.val, (mem_filter.mp y.property).1⟩
    let C := ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk w
    have hw : w ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
    have he := Finset.card_le_one.mp (by omega : (nextRingCarriers F).card ≤ 1)
      _ (mem_filter.mp hx).2.2 _ (mem_filter.mp hy).2.2
    have hz : z ∈ C.supp := by
      change z ∈ (((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk w).supp
      rw [he]
      simp [z, ConnectedComponent.mem_supp_iff]
    obtain ⟨a, ha0, ha1, hxa⟩ := boundary_map_side_chart (by omega)
      ⟨x.val, (mem_filter.mp x.property).2⟩ s (mem_filter.mp hx).2.1
    obtain ⟨b, hb0, hb1, hyb⟩ := boundary_map_side_chart (by omega)
      ⟨y.val, (mem_filter.mp y.property).2⟩ s (mem_filter.mp hy).2.1
    dsimp only at hxa hyb
    have hab : a.val < b.val := by simpa only [hxa, hyb, sideChart_position] using hlt
    have ha' := chart_depth_one_away_from_ends (by omega) F hacyc hgeom.1 s a
      ⟨ha0, ha1⟩ (hxa ▸ (mem_filter.mp x.property).1)
    have hb' := chart_depth_one_away_from_ends (by omega) F hacyc hgeom.1 s b
      ⟨hb0, hb1⟩ (hyb ▸ (mem_filter.mp y.property).1)
    have hspan := chart_carrier_span_le_one hk F hacyc s hmissing hf hp C w z hw hz a b
      hxa hyb ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
    have hshadow (t : Fin (3 * k + 2)) (ht : a.val - 1 ≤ t.val ∧ t.val ≤ b.val + 1) :
        sideChart s (t, ⟨0, by omega⟩) ∉ F :=
      chart_carrier_expanded_shadow (by omega) F hacyc s C w z hw hz a b hxa hyb
        (by omega) hab hb1 t ht
    have hgap := hgeom.2.2 (a.val - 1) (b.val + 1) (by omega) (by omega) (by omega) (by
      intro v hv hs hlo hhi
      let t : Fin (3 * k + 2) := ⟨sidePosition s v, by have := sidePosition_bounds hs; omega⟩
      have hts := (sideChart_openSide s (t, ⟨0, by omega⟩)).mpr
        (by have := sidePosition_bounds hs; dsimp [t]; omega)
      have heq := sidePosition_injective hs hts (by rw [sideChart_position])
      exact hshadow t ⟨hlo, hhi⟩ (heq ▸ hv))
    obtain ⟨v, hvF, hvs, hvpos⟩ := hgap.2 (by omega)
    let u : (↑F : Set _) := ⟨v, hvF⟩
    refine ⟨u, hvs, hvpos, ?_⟩
    intro huN
    have huC := Finset.card_le_one.mp (by omega : (nextRingCarriers F).card ≤ 1)
      _ huN _ (mem_filter.mp hx).2.2
    have hholeSide : OnOpenSide s (sideChart s (a, ⟨0, by omega⟩)) :=
      (sideChart_openSide s _).mpr ⟨rfl, ha0, ha1⟩
    have hwb : ¬ IsGridBoundary w.val := by
      have hr := (mem_filter.mp x.property).2
      unfold IsNextRing at hr
      change ¬ IsGridBoundary x.val
      unfold IsGridBoundary
      omega
    have hadj : (gridGraph (3 * k + 2) (3 * k + 2)).Adj
        (sideChart s (a, ⟨0, by omega⟩)) w.val := by
      change (gridGraph _ _).Adj _ x.val
      rw [hxa, sideChart_adj]
      simp [gridGraph, adjacent]
    exact inward_hole_carrier_avoids_roots F hacyc s _ hholeSide
      (hshadow a (by omega)) w hwb hadj u hvs huC
  obtain ⟨x, hx, y, hy, hne⟩ := Finset.one_lt_card.mp (show 1 < J.card by omega)
  have hposne : sidePosition s x.val ≠ sidePosition s y.val := by
    intro he
    apply hne
    apply Subtype.ext
    exact boundary_map_side_position_injective (by omega) s
      ⟨x.val, (mem_filter.mp x.property).2⟩ ⟨y.val, (mem_filter.mp y.property).2⟩
      (mem_filter.mp hx).2.1 (mem_filter.mp hy).2.1 he
  rcases lt_or_gt_of_ne hposne with hlt | hlt
  · exact ordered x y hx hy hlt
  · exact ordered y x hy hx hlt

end GridGraphs.CarrierLayers.FourCarrier
