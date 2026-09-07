import GridGraphs.Accounting.CarrierLayers.GapGlobalCapacity

/-!
# Excluding minimal induced slack

When every nonpure carrier reaches the deep layer, the diagonal boundary
injection uses at most one hole on a fixed open side per nonpure carrier.
A missing side has many more holes. Count the unused holes, not an additional
boundary-deficiency charge; corners stay in the complementary part.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

private theorem map_side_coordinates {n : Nat} (hn : 5 ≤ n)
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

/-- In the absence of shallow nonpure carriers, the preimages of any one
open side under the boundary injection belong to distinct induced carriers. -/
theorem same_side_boundary_map_carrier_injective {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hzero : (nextRingCarriers F).card = 0) (s : Fin 4)
    (w z : (↑F : Set (GridVertex n n))) (hwr : IsNextRing w.val) (hzr : IsNextRing z.val)
    (hws : OnOpenSide s (nextRingBoundaryMap hn ⟨w.val, hwr⟩))
    (hzs : OnOpenSide s (nextRingBoundaryMap hn ⟨z.val, hzr⟩))
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
  have hnonpure : C ∉ pureBoundaryCarriers F := fun h =>
    hwb ((mem_filter.mp h).2 w hw)
  have hdeep : ∃ v ∈ C.supp, ¬ IsGridBoundary v.val ∧ ¬ IsNextRing v.val := by
    by_contra h
    push Not at h
    have hm : C ∈ nextRingCarriers F := mem_filter.mpr ⟨mem_univ _, hnonpure, by
      intro v hv
      by_cases hb : IsGridBoundary v.val
      · exact Or.inl hb
      · exact Or.inr (h v hv hb)⟩
    simp only [card_eq_zero.mp hzero, Finset.notMem_empty] at hm
  obtain ⟨v, hv, hvb, hvr⟩ := hdeep
  have hwc := map_side_coordinates hn ⟨w.val, hwr⟩ s hws
  have hzc := map_side_coordinates hn ⟨z.val, hzr⟩ s hzs
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

/-- Unused holes on a chosen open side are a global boundary/next-ring loss.
No side is assumed missing, and no corner is assumed preserved. -/
theorem layers_add_side_holes_le_perimeter_add_nonpure {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hzero : (nextRingCarriers F).card = 0) (s : Fin 4) :
    (F.filter IsGridBoundary).card + (F.filter IsNextRing).card +
      ((univ \ F).filter (OnOpenSide s)).card ≤ 4 * n - 4 +
        (Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent -
          (pureBoundaryCarriers F).card) := by
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
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,
      nextRingBoundaryMap_notMem (by omega) F hacyc
        ⟨v.val, (mem_filter.mp v.property).2⟩ (mem_filter.mp v.property).1⟩,
      nextRingBoundaryMap_boundary (by omega) _⟩
  let A := (univ : Finset E).filter (fun v => OnOpenSide s (f v))
  let P := pureBoundaryCarriers F
  let R := (univ : Finset G.ConnectedComponent) \ P
  let comp : E → G.ConnectedComponent := fun v =>
    G.connectedComponentMk ⟨v.val, (mem_filter.mp v.property).1⟩
  have hcomp (v : E) : comp v ∈ R := by
    have hs : (⟨v.val, (mem_filter.mp v.property).1⟩ : (↑F : Set _)) ∈
        (comp v).supp := by simp [comp, ConnectedComponent.mem_supp_iff]
    have hr := (mem_filter.mp v.property).2
    have hb : ¬ IsGridBoundary v.val := by
      unfold IsNextRing at hr
      unfold IsGridBoundary
      omega
    exact mem_sdiff.mpr ⟨mem_univ _, fun h => hb ((mem_filter.mp h).2 _ hs)⟩
  let g : A → R := fun v => ⟨comp v.val, hcomp v.val⟩
  have hginj : Function.Injective g := by
    intro v w he
    have he' : comp v.val = comp w.val := congrArg Subtype.val he
    have heq := same_side_boundary_map_carrier_injective (by omega) F hacyc hzero s
      ⟨v.val.val, (mem_filter.mp v.val.property).1⟩
      ⟨w.val.val, (mem_filter.mp w.val.property).1⟩
      (mem_filter.mp v.val.property).2 (mem_filter.mp w.val.property).2
      (mem_filter.mp v.property).2 (mem_filter.mp w.property).2 he'
    have hvw : v.val.val = w.val.val := congrArg
      (fun u : (↑F : Set (GridVertex n n)) => u.val) heq
    exact Subtype.ext (Subtype.ext hvw)
  have hA : A.card ≤ Fintype.card G.ConnectedComponent - P.card := by
    have h := Fintype.card_le_of_injective g hginj
    simpa only [Fintype.card_coe, R, card_sdiff_of_subset (subset_univ _), card_univ] using h
  have himage : M.filter (OnOpenSide s) = A.image f := by
    ext x
    simp only [M, A, mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨⟨v, rfl⟩, hv⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, rfl⟩, hv⟩
  have hside : (M.filter (OnOpenSide s)).card ≤
      Fintype.card G.ConnectedComponent - P.card := by
    rw [himage, card_image_of_injective _ hinj]
    exact hA
  have hoff := card_le_card (show M.filter (fun x => ¬ OnOpenSide s x) ⊆
      U.filter (fun x => ¬ OnOpenSide s x) from fun x hx =>
        mem_filter.mpr ⟨hsub (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩)
  have hMp := card_filter_add_card_filter_not (s := M) (p := OnOpenSide s)
  have hUp := card_filter_add_card_filter_not (s := U) (p := OnOpenSide s)
  have hUside : U.filter (OnOpenSide s) = (univ \ F).filter (OnOpenSide s) := by
    ext x
    simp only [U, mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩,
      fun h => ⟨⟨h.1, openSide_boundary h.2⟩, h.2⟩⟩
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
  change (F.filter IsGridBoundary).card + E.card +
    ((univ \ F).filter (OnOpenSide s)).card ≤ 4 * n - 4 +
      (Fintype.card G.ConnectedComponent - P.card)
  omega

/-- The entire three-pure-carrier minimal-induced branch satisfies the sharp
target, with arbitrary ambient component count and arbitrary corner holes. -/
theorem card_le_target_of_three_pure_minimal_induced {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hr : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 2) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  classical
  by_contra hf
  have hzero : (nextRingCarriers F).card = 0 := by
    have h := one_excess_shallow_carriers_le_induced_slack (a := 0) hk F hacyc hp
      (by omega) (by simpa using hr)
    omega
  obtain ⟨s, hs⟩ := exists_side_without_pure_carrier (by omega) F hacyc (by omega)
  have hq := missing_side_preserved_card_le (by omega) F hacyc s hs
  have hholes : 2 * k ≤ ((univ \ F).filter (OnOpenSide s)).card := by
    let S := univ.filter (OnOpenSide (n := 3 * k + 2) s)
    have hScard : S.card = 3 * k := by
      simpa only [Nat.add_sub_cancel] using openSide_card (by omega : 2 ≤ 3 * k + 2) s
    have hSF : S ∩ F = F.filter (OnOpenSide s) := by ext v; simp [S, and_comm]
    have hSU : S \ F = (univ \ F).filter (OnOpenSide s) := by
      ext v
      simp only [S, mem_sdiff, mem_filter, mem_univ, true_and]
      exact and_comm
    have hpart := card_sdiff_add_card_inter S F
    rw [hScard, hSF, hSU] at hpart
    omega
  have hlayers := layers_add_side_holes_le_perimeter_add_nonpure (by omega) F hacyc hzero s
  have hcap := card_le_layers_without_nextRing_carriers (by omega) F hacyc
  rw [hp, hr] at hlayers hcap
  rw [hzero, Nat.sub_zero] at hcap
  have hsub : k + 2 - 3 = k - 1 := by omega
  have hn : 3 * k + 2 - 4 = 3 * k - 2 := by omega
  have hper : 4 * (3 * k + 2) - 4 = 12 * k + 4 := by omega
  rw [hsub, hper] at hlayers
  rw [hsub, hn] at hcap
  have hk1 : k - 1 + 1 = k := by omega
  have hn2 : 3 * k - 2 + 2 = 3 * k := by omega
  nlinarith

end GridGraphs.CarrierLayers
