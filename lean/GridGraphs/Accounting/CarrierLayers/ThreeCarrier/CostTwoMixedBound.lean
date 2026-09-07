import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoEdgeGeometry
import GridGraphs.Accounting.CarrierLayers.MixedPacking.Rectangle

/-! # Mixed packing of the actual W2 edge sets

The nonempty horizontal rows inject into actual horizontal carriers. Extend
their row set to three interior rows, using empty edge sets as padding.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- Actual nonempty horizontal rows are interior and number at most three. -/
theorem cost_two_horizontal_rows {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) :
    let R := (Icc 1 (3 * k)).filter (fun r => (rectangleHorizontalColumns F s r).Nonempty)
    R ⊆ Icc 2 (3 * k - 1) ∧ R.card ≤ 3 := by
  classical
  let R := (Icc 1 (3 * k)).filter (fun r => (rectangleHorizontalColumns F s r).Nonempty)
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
    have hri := mem_Icc.mp (mem_filter.mp r.property).1
    have hh := cost_two_horizontal_edge_rows hk F hacyc s hmissing hW (x r) (r.val - 1)
      ⟨hx0 r, hxn r⟩ (by omega) (h0 r) (h1 r)
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
    · apply (cost_two_nonpure_rectangle_iff (by omega) F hacyc s hmissing hW _ (h0 r)).mpr
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
  change R ⊆ Icc 2 (3 * k - 1) ∧ R.card ≤ 3
  refine ⟨?_, by omega⟩
  intro r hr
  exact mem_Icc.mpr (by have := hrange ⟨r, hr⟩; dsimp only at this; omega)

/-- The actual enlarged-rectangle FF edge sets satisfy `V+H <= (k-1)(3k-1)`.
All shallow and boundary-root edges remain in these sets. -/
theorem cost_two_mixed_edge_bound {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) :
    (Icc 1 (3 * k)).sum (fun r => (rectangleHorizontalColumns F s r).card) +
      (Icc 1 (3 * k - 1)).sum (fun t => (rectangleVerticalColumns F s t).card) ≤
        (k - 1) * (3 * k - 1) := by
  classical
  let E := rectangleHorizontalColumns F s
  let V := rectangleVerticalColumns F s
  let R := (Icc 1 (3 * k)).filter (fun r => (E r).Nonempty)
  obtain ⟨hRsub, hRcard⟩ := cost_two_horizontal_rows hk F hacyc s hmissing hf hp hW
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
  have hV : ∀ t ∈ Icc 1 (3 * k - 1), MixedPacking.Spaced (V t) ∧
      V t ⊆ Icc 3 (3 * (k - 1) + 1) := by
    intro t ht
    exact cost_two_vertical_columns_eligible hk F hacyc s hW t ht
  have hnear (i j : Fin 3) (hij : i < j) : e j ≤ e i + 2 → Disjoint (E (e i)) (E (e j)) := by
    intro h
    exact nearby_horizontal_columns_disjoint F hacyc s (e i) (e j)
      (by have := hrow i; omega) (e.strictMono hij) h
  have hshadow (i : Fin 3) : ∀ t ∈ Icc 1 (3 * k - 1), t ∈ Icc (e i - 2) (e i + 1) →
      ∀ v ∈ V t, ∀ x ∈ E (e i), v + 1 < x ∨ x + 2 < v := by
    intro t ht hb v hv x hx
    exact rectangle_ff_shadow F hacyc s (e i) t (hrow i).1 (mem_Icc.mp ht).1 hb v hv x hx
  have hbound := MixedPacking.rectangular_three_rod_edge_bound (k - 1) (3 * k)
    (e 0) (e 1) (e 2) (by omega) (hrow 0).1 (e.monotone (by decide))
    (e.monotone (by decide)) (hrow 2).2 (E (e 0)) (E (e 1)) (E (e 2)) V
    (hE _) (hE _) (hE _) (hnear 0 1 (by decide)) (hnear 0 2 (by decide))
    (hnear 1 2 (by decide)) hV (hshadow 0) (hshadow 1) (hshadow 2)
  have hsum : (Icc 1 (3 * k)).sum (fun r => (E r).card) =
      (E (e 0)).card + (E (e 1)).card + (E (e 2)).card := by
    have hSouter : S ⊆ Icc 1 (3 * k) := by
      intro r hr
      have := mem_Icc.mp (hSsub hr)
      apply mem_Icc.mpr
      omega
    have hzero : ∀ r ∈ Icc 1 (3 * k), r ∉ S → (E r).card = 0 := by
      intro r hr hn
      by_contra h
      have hrR : r ∈ R := mem_filter.mpr ⟨hr, card_pos.mp (by omega)⟩
      exact hn (hRS hrR)
    rw [← sum_subset hSouter hzero, ← S.image_orderEmbOfFin_univ hScard,
      sum_image (fun _ _ _ _ he => e.injective he)]
    exact Fin.sum_univ_three _
  rw [hsum]
  exact hbound

end GridGraphs.CarrierLayers.ThreeCarrier
