import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostThreeDefect

/-! # Mixed packing after removing the two possible frame defects -/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- A missing side contains no horizontal induced FF edge. -/
theorem missing_side_first_horizontal_columns_empty {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val) :
    rectangleHorizontalColumns F s 1 = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxI, hxn, _, h0, h1⟩ := mem_filter.mp hx
  have hxI' := mem_Icc.mp hxI
  let u : (↑F : Set (GridVertex n n)) := ⟨sideChart s (⟨x, by omega⟩, ⟨0, by omega⟩), h0⟩
  let v : (↑F : Set (GridVertex n n)) := ⟨sideChart s (⟨x + 1, hxn⟩, ⟨0, by omega⟩), h1⟩
  let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk u
  have hu : u ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have hv : v ∈ C.supp := by
    apply C.mem_supp_of_adj_mem_supp hu
    apply (sideChart_adj s _ _).mpr
    simp [gridGraph, adjacent, Fin.ext_iff]
  have hs : OnOpenSide s u.val := (sideChart_openSide s _).mpr ⟨rfl, by dsimp; omega⟩
  have he := root_carrier_constant_position hn F hacyc s hmissing u hs v hv
  dsimp [u, v] at he
  rw [sideChart_position, sideChart_position] at he
  dsimp only at he
  omega

/-- Nonempty interior horizontal rows inject into actual horizontal nonpure carriers. -/
theorem cost_three_interior_rows_le_three {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3) :
    ((Icc 2 (3 * k - 1)).filter (fun r => (rectangleHorizontalColumns F s r).Nonempty)).card ≤ 3 := by
  classical
  let R := (Icc 2 (3 * k - 1)).filter (fun r => (rectangleHorizontalColumns F s r).Nonempty)
  have hex (r : R) : ∃ x : Nat, ∃ hx : x + 1 < 3 * k + 2, ∃ hr : r.val - 1 < 3 * k + 2,
      2 ≤ x ∧ x + 3 < 3 * k + 2 ∧
      sideChart s (⟨x, by omega⟩, ⟨r.val - 1, hr⟩) ∈ F ∧
      sideChart s (⟨x + 1, hx⟩, ⟨r.val - 1, hr⟩) ∈ F := by
    obtain ⟨x, hx⟩ := (mem_filter.mp r.property).2
    obtain ⟨hxI, hxn, hrn, h0, h1⟩ := mem_filter.mp hx
    have hxI' := mem_Icc.mp hxI
    exact ⟨x, hxn, hrn, by omega, by omega, h0, h1⟩
  choose x hx hr hx0 hxn h0 h1 using hex
  have hrange (r : R) : 2 ≤ r.val ∧ r.val < 3 * k := by
    have h := mem_Icc.mp (mem_filter.mp r.property).1
    omega
  let u (r : R) : (↑F : Set (GridVertex (3 * k + 2) (3 * k + 2))) :=
    ⟨sideChart s (⟨x r, by have := hx r; omega⟩, ⟨r.val - 1, hr r⟩), h0 r⟩
  let v (r : R) : (↑F : Set (GridVertex (3 * k + 2) (3 * k + 2))) :=
    ⟨sideChart s (⟨x r + 1, hx r⟩, ⟨r.val - 1, hr r⟩), h1 r⟩
  let C (r : R) := ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk (u r)
  have hu (r : R) : u r ∈ (C r).supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have hv (r : R) : v r ∈ (C r).supp := by
    apply (C r).mem_supp_of_adj_mem_supp (hu r)
    apply (sideChart_adj s _ _).mpr
    simp [gridGraph, adjacent, Fin.ext_iff]
  have hC (r : R) : C r ∈ horizontalNonpureCarriers F s := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, u r, hu r, v r, hv r, ?_⟩
    · apply (cost_three_nonpure_rectangle_iff hk F hacyc s hmissing hW _ (h0 r)).mpr
      have := hrange r
      have := hx0 r
      have := hxn r
      dsimp only
      omega
    · dsimp [u, v]
      rw [sideChart_position, sideChart_position]
      dsimp only
      omega
  let f : R → horizontalNonpureCarriers F s := fun r => ⟨C r, hC r⟩
  have hinj : Function.Injective f := by
    intro r t he
    have heC : C r = C t := congrArg Subtype.val he
    have hut : u t ∈ (C r).supp := heC.symm ▸ hu t
    have hdepth := horizontal_carrier_constant_depth F hacyc s (C r)
      (u r) (v r) (u t) (hu r) (hv r) hut _ _ _ rfl rfl rfl (by dsimp; omega)
    have hrr := hrange r
    have htt := hrange t
    apply Subtype.ext
    dsimp only at hdepth
    omega
  have hcount := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe] at hcount
  have hthree := (horizontal_nonpure_card_le_slack hk F hacyc s hmissing hf hp).2
  change R.card ≤ 3
  omega

/-- All actual rectangle FF edges, including any defective frame edges, fit
the mixed baseline plus two. The extra hole's position is unrestricted. -/
theorem cost_three_mixed_edge_bound {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3) :
    (Icc 1 (3 * k)).sum (fun r => (rectangleHorizontalColumns F s r).card) +
      (Icc 1 (3 * k - 1)).sum (fun t => (rectangleVerticalColumns F s t).card) ≤
        (k - 1) * (3 * k - 1) + 2 := by
  classical
  let E := rectangleHorizontalColumns F s
  let V := rectangleVerticalColumns F s
  let G := fun t => V t ∩ Icc 3 (3 * k - 2)
  let R := (Icc 2 (3 * k - 1)).filter (fun r => (E r).Nonempty)
  have hRsub : R ⊆ Icc 2 (3 * k - 1) := filter_subset _ _
  have hRcard := cost_three_interior_rows_le_three hk F hacyc s hmissing hf hp hW
  obtain ⟨S, hRS, hSsub, hScard⟩ := exists_subsuperset_card_eq hRsub hRcard
    (show 3 ≤ (Icc 2 (3 * k - 1)).card by rw [Nat.card_Icc]; omega)
  let e := S.orderEmbOfFin hScard
  have hrow (i : Fin 3) : 2 ≤ e i ∧ e i < 3 * k := by
    have h := mem_Icc.mp (hSsub (S.orderEmbOfFin_mem hScard i))
    dsimp [e]
    omega
  have hE (r : Nat) : E r ⊆ Icc 2 (3 * (k - 1) + 1) := by
    intro x hx
    have h := mem_Icc.mp (mem_filter.mp hx).1
    apply mem_Icc.mpr
    omega
  have hV : ∀ t ∈ Icc 1 (3 * k - 1), MixedPacking.Spaced (G t) ∧
      G t ⊆ Icc 3 (3 * (k - 1) + 1) := by
    intro t ht
    have ht' := mem_Icc.mp ht
    constructor
    · intro x hx z hz hxz
      obtain ⟨_, hxn, htx, hx0, hx1⟩ := mem_filter.mp (mem_inter.mp hx).1
      obtain ⟨_, hzn, htz, hz0, hz1⟩ := mem_filter.mp (mem_inter.mp hz).1
      have he : t - 1 + 1 = t := by omega
      apply vertical_ff_spacing _ (sideChart_acyclic s F hacyc) x z (t - 1) hzn
        (by omega) hxz hx0 ?_ hz0 ?_
      · change sideChart s (⟨x, hxn⟩, ⟨t - 1 + 1, by omega⟩) ∈ F
        simpa only [he] using hx1
      · change sideChart s (⟨z, hzn⟩, ⟨t - 1 + 1, by omega⟩) ∈ F
        simpa only [he] using hz1
    · intro x hx
      have h := mem_Icc.mp (mem_inter.mp hx).2
      apply mem_Icc.mpr
      omega
  have hnear (i j : Fin 3) (hij : i < j) : e j ≤ e i + 2 → Disjoint (E (e i)) (E (e j)) := by
    intro h
    exact nearby_horizontal_columns_disjoint F hacyc s (e i) (e j)
      (by have := hrow i; omega) (e.strictMono hij) h
  have hshadow (i : Fin 3) : ∀ t ∈ Icc 1 (3 * k - 1), t ∈ Icc (e i - 2) (e i + 1) →
      ∀ v ∈ G t, ∀ x ∈ E (e i), v + 1 < x ∨ x + 2 < v := by
    intro t ht hb v hv x hx
    exact rectangle_ff_shadow F hacyc s (e i) t (hrow i).1 (mem_Icc.mp ht).1 hb
      v (mem_inter.mp hv).1 x hx
  have hbound := MixedPacking.rectangular_three_rod_edge_bound (k - 1) (3 * k)
    (e 0) (e 1) (e 2) (by omega) (hrow 0).1 (e.monotone (by decide))
    (e.monotone (by decide)) (hrow 2).2 (E (e 0)) (E (e 1)) (E (e 2)) G
    (hE _) (hE _) (hE _) (hnear 0 1 (by decide)) (hnear 0 2 (by decide))
    (hnear 1 2 (by decide)) hV (hshadow 0) (hshadow 1) (hshadow 2)
  have hsum : (Icc 2 (3 * k - 1)).sum (fun r => (E r).card) =
      (E (e 0)).card + (E (e 1)).card + (E (e 2)).card := by
    have hzero : ∀ r ∈ Icc 2 (3 * k - 1), r ∉ S → (E r).card = 0 := by
      intro r hr hn
      by_contra h
      exact hn (hRS (mem_filter.mpr ⟨hr, card_pos.mp (by omega)⟩))
    rw [← sum_subset hSsub hzero, ← S.image_orderEmbOfFin_univ hScard,
      sum_image (fun _ _ _ _ he => e.injective he)]
    exact Fin.sum_univ_three _
  have hHpart : (Icc 1 (3 * k)).sum (fun r => (E r).card) =
      (Icc 2 (3 * k - 1)).sum (fun r => (E r).card) + (E (3 * k)).card := by
    have he : Icc 1 (3 * k) = insert 1 (insert (3 * k) (Icc 2 (3 * k - 1))) := by
      ext r
      simp only [mem_Icc, mem_insert]
      omega
    rw [he, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
      sum_insert (by simp only [mem_Icc]; omega)]
    have hz : E 1 = ∅ := missing_side_first_horizontal_columns_empty (by omega) F hacyc s hmissing
    rw [hz, card_empty]
    omega
  have hVpart : (Icc 1 (3 * k - 1)).sum (fun t => (V t).card) =
      (Icc 1 (3 * k - 1)).sum (fun t => (G t).card) +
      (Icc 1 (3 * k - 1)).sum (fun t => (V t \ Icc 3 (3 * k - 2)).card) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro t _
    have h := card_sdiff_add_card_inter (V t) (Icc 3 (3 * k - 2))
    change (V t).card = (V t ∩ Icc 3 (3 * k - 2)).card + _
    omega
  have hbad := cost_three_bad_edges_le_two hk F hacyc s hW
  change (Icc 1 (3 * k - 1)).sum (fun t => (V t \ Icc 3 (3 * k - 2)).card) +
    (E (3 * k)).card ≤ 2 at hbad
  rw [hHpart, hVpart, hsum]
  omega

end GridGraphs.CarrierLayers.ThreeCarrier
