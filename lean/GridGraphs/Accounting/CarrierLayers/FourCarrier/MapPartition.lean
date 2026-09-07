import GridGraphs.Accounting.CarrierLayers.FourCarrier.ShortGaps

/-! # Partitioning the actual fixed boundary-map image

Deep carriers contribute at most one preimage on a chosen open side. Shallow
contributions are retained as an actual finite set, not a hypothetical charge.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Actual preserved next-ring preimages on the chosen side whose induced
carrier is shallow. The fixed boundary map is used without transporting it. -/
noncomputable def shallowSidePreimages {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n)) (s : Fin 4) : Finset (F.filter IsNextRing) :=
  univ.filter fun v =>
    OnOpenSide s (nextRingBoundaryMap hn ⟨v.val, (mem_filter.mp v.property).2⟩) ∧
      ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk
        ⟨v.val, (mem_filter.mp v.property).1⟩ ∈ nextRingCarriers F

/-- A fixed-map image on side `s` comes from the next-ring line parallel to
that side. This is a direct coordinate fact, not map equivariance. -/
theorem boundary_map_side_coordinates {n : Nat} (hn : 5 ≤ n)
    (w : {v : GridVertex n n // IsNextRing v}) (s : Fin 4)
    (hs : OnOpenSide s (nextRingBoundaryMap hn w)) :
    (s.val = 0 ∧ w.val.1.val = 1) ∨
    (s.val = 1 ∧ w.val.1.val = n - 2) ∨
    (s.val = 2 ∧ w.val.2.val = 1) ∨
    (s.val = 3 ∧ w.val.2.val = n - 2) := by
  have hw := w.property
  unfold IsNextRing at hw
  unfold nextRingBoundaryMap at hs
  split_ifs at hs <;> unfold OnOpenSide OnSide at hs <;> dsimp at hs <;> omega

/-- Chart coordinates for a preserved next-ring preimage on a fixed-map side. -/
theorem boundary_map_side_chart {n : Nat} (hn : 5 ≤ n)
    (w : {v : GridVertex n n // IsNextRing v}) (s : Fin 4)
    (hs : OnOpenSide s (nextRingBoundaryMap hn w)) :
    ∃ t : Fin n, 0 < t.val ∧ t.val + 1 < n ∧
      w.val = sideChart s (t, ⟨1, by omega⟩) := by
  have hc := boundary_map_side_coordinates hn w s hs
  have hw := w.property
  unfold IsNextRing at hw
  let t := if s.val < 2 then w.val.2 else w.val.1
  refine ⟨t, ?_, ?_, ?_⟩
  · dsimp [t]; split <;> omega
  · dsimp [t]; split <;> omega
  · fin_cases s <;> simp [t, sideChart, Prod.ext_iff, Fin.ext_iff] at hc ⊢ <;> omega

/-- Two preimages on the same fixed-map side cannot belong to the same deep
carrier. Other carriers are allowed to be shallow. -/
theorem deep_boundary_map_carrier_injective {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (w z : (↑F : Set (GridVertex n n)))
    (hwr : IsNextRing w.val) (hzr : IsNextRing z.val)
    (hws : OnOpenSide s (nextRingBoundaryMap hn ⟨w.val, hwr⟩))
    (hzs : OnOpenSide s (nextRingBoundaryMap hn ⟨z.val, hzr⟩))
    (hdeep : ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk w ∉ nextRingCarriers F)
    (he : ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk w =
      ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk z) : w = z := by
  classical
  let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk w
  have hw : w ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have hz : z ∈ C.supp := by
    dsimp [C]
    rw [he]
    simp [ConnectedComponent.mem_supp_iff]
  have hwb : ¬ IsGridBoundary w.val := by
    unfold IsNextRing at hwr
    unfold IsGridBoundary
    omega
  have hnonpure : C ∉ pureBoundaryCarriers F := fun h => hwb ((mem_filter.mp h).2 w hw)
  have hex : ∃ v ∈ C.supp, ¬ IsGridBoundary v.val ∧ ¬ IsNextRing v.val := by
    by_contra h
    push Not at h
    apply hdeep
    exact mem_filter.mpr ⟨mem_univ _, hnonpure, fun v hv => by
      by_cases hb : IsGridBoundary v.val
      · exact Or.inl hb
      · exact Or.inr (h v hv hb)⟩
  obtain ⟨v, hv, hvb, hvr⟩ := hex
  have hwc := boundary_map_side_coordinates hn ⟨w.val, hwr⟩ s hws
  have hzc := boundary_map_side_coordinates hn ⟨z.val, hzr⟩ s hzs
  dsimp only at hwc hzc
  have hvdeep : 2 ≤ v.val.1.val ∧ v.val.1.val < n - 2 ∧
      2 ≤ v.val.2.val ∧ v.val.2.val < n - 2 := by
    unfold IsGridBoundary at hvb
    unfold IsNextRing at hvr
    omega
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  all_goals
    rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
    · have hw' := congrArg Fin.val (hr w hw)
      have hz' := congrArg Fin.val (hr z hz)
      have hv' := congrArg Fin.val (hr v hv)
      omega
    · have hw' := congrArg Fin.val (hc w hw)
      have hz' := congrArg Fin.val (hc z hz)
      have hv' := congrArg Fin.val (hc v hv)
      omega

/-- The actual fixed-map partition gives `B+E+H_s <= perimeter+d+J`, where
`J` is the shallow preimage count on that side. -/
theorem layers_add_side_holes_le_deep_add_shallow_image {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) (s : Fin 4) :
    (F.filter IsGridBoundary).card + (F.filter IsNextRing).card +
      ((univ \ F).filter (OnOpenSide s)).card ≤ 4 * n - 4 +
        (Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent -
          (pureBoundaryCarriers F).card - (nextRingCarriers F).card) +
        (shallowSidePreimages (by omega) F s).card := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let E := F.filter IsNextRing
  let U := (univ \ F).filter IsGridBoundary
  let f : E → GridVertex n n := fun v =>
    nextRingBoundaryMap (by omega) ⟨v.val, (mem_filter.mp v.property).2⟩
  let M := univ.image f
  have hinj : Function.Injective f := by
    intro v w he
    have hvw : v.val = w.val := congrArg
      (fun u : {v : GridVertex n n // IsNextRing v} => u.val)
      (nextRingBoundaryMap_injective (by omega) he)
    exact Subtype.ext hvw
  have hMcard : M.card = E.card := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_coe]
  have hsub : M ⊆ U := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := mem_image.mp hx
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, nextRingBoundaryMap_notMem (by omega)
      F hacyc ⟨v.val, (mem_filter.mp v.property).2⟩ (mem_filter.mp v.property).1⟩,
      nextRingBoundaryMap_boundary (by omega) _⟩
  let S := (univ : Finset E).filter (fun v => OnOpenSide s (f v))
  let P := pureBoundaryCarriers F
  let N := nextRingCarriers F
  let R := (univ : Finset G.ConnectedComponent) \ (P ∪ N)
  let comp : E → G.ConnectedComponent := fun v =>
    G.connectedComponentMk ⟨v.val, (mem_filter.mp v.property).1⟩
  let A := S.filter (fun v => comp v ∉ N)
  have hPN : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro C hp hn
    exact (mem_filter.mp hn).2.1 hp
  have hcomp (v : A) : comp v.val ∈ R := by
    have hs : (⟨v.val.val, (mem_filter.mp v.val.property).1⟩ : (↑F : Set _)) ∈
        (comp v.val).supp := by simp [comp, ConnectedComponent.mem_supp_iff]
    have hr := (mem_filter.mp v.val.property).2
    have hb : ¬ IsGridBoundary v.val.val := by
      unfold IsNextRing at hr
      unfold IsGridBoundary
      omega
    apply mem_sdiff.mpr
    refine ⟨mem_univ _, ?_⟩
    simp only [mem_union, not_or]
    exact ⟨fun h => hb ((mem_filter.mp h).2 _ hs), (mem_filter.mp v.property).2⟩
  let g : A → R := fun v => ⟨comp v.val, hcomp v⟩
  have hginj : Function.Injective g := by
    intro v w he
    have he' : comp v.val = comp w.val := congrArg Subtype.val he
    have heq := deep_boundary_map_carrier_injective (by omega) F hacyc s
      ⟨v.val.val, (mem_filter.mp v.val.property).1⟩
      ⟨w.val.val, (mem_filter.mp w.val.property).1⟩
      (mem_filter.mp v.val.property).2 (mem_filter.mp w.val.property).2
      (mem_filter.mp (mem_filter.mp v.property).1).2
      (mem_filter.mp (mem_filter.mp w.property).1).2 (mem_filter.mp v.property).2 he'
    have hvw : v.val.val = w.val.val := congrArg
      (fun u : (↑F : Set (GridVertex n n)) => u.val) heq
    exact Subtype.ext (Subtype.ext hvw)
  have hA : A.card ≤ Fintype.card G.ConnectedComponent - P.card - N.card := by
    have h := Fintype.card_le_of_injective g hginj
    simpa only [Fintype.card_coe, R, card_sdiff_of_subset (subset_univ _), card_univ,
      card_union_of_disjoint hPN, Nat.sub_sub] using h
  have hJ : S.filter (fun v => ¬ comp v ∉ N) = shallowSidePreimages (by omega) F s := by
    ext v
    simp [S, f, comp, N, G, shallowSidePreimages]
  have hSpart := card_filter_add_card_filter_not (s := S) (p := fun v => comp v ∉ N)
  rw [hJ] at hSpart
  have himage : M.filter (OnOpenSide s) = S.image f := by
    ext x
    simp only [M, S, mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨⟨v, rfl⟩, hv⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, rfl⟩, hv⟩
  have hside : (M.filter (OnOpenSide s)).card ≤
      Fintype.card G.ConnectedComponent - P.card - N.card +
        (shallowSidePreimages (by omega) F s).card := by
    rw [himage, card_image_of_injective _ hinj]
    change A.card + _ = _ at hSpart
    omega
  have hoff := card_le_card (show M.filter (fun x => ¬ OnOpenSide s x) ⊆
      U.filter (fun x => ¬ OnOpenSide s x) from fun x hx =>
        mem_filter.mpr ⟨hsub (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩)
  have hMp := card_filter_add_card_filter_not (s := M) (p := OnOpenSide s)
  have hUp := card_filter_add_card_filter_not (s := U) (p := OnOpenSide s)
  have hUside : U.filter (OnOpenSide s) = (univ \ F).filter (OnOpenSide s) := by
    ext x
    simp only [U, mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, openSide_boundary h.2⟩, h.2⟩⟩
  have hper : (F.filter IsGridBoundary).card + U.card = 4 * n - 4 := by
    have he : (F.filter IsGridBoundary) ∪ U = univ.filter IsGridBoundary := by
      ext v
      by_cases hv : v ∈ F <;> simp [U, hv]
    have hd : Disjoint (F.filter IsGridBoundary) U := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact (mem_sdiff.mp (mem_filter.mp hw).1).2 (mem_filter.mp hv).1
    rw [← card_union_of_disjoint hd, he]
    simpa using BoundaryFiveConstruction.boundary_card hn
  rw [hUside] at hUp
  change (F.filter IsGridBoundary).card + E.card + _ ≤ 4 * n - 4 +
    (Fintype.card G.ConnectedComponent - P.card - N.card) + _
  omega

end GridGraphs.CarrierLayers.FourCarrier
