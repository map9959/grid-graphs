import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.NonpureForest
import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoMixedBound

/-! # Covering every actual nonpure FF edge by the rectangle edge sets -/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- Every edge of the actual nonpure induced forest appears in the physical
horizontal or vertical rectangle count. The map on unordered edges is injective. -/
theorem cost_two_nonpure_edges_le_rectangle {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) :
    (nonpureGraph F).edgeFinset.card ≤
      (Icc 1 (3 * k)).sum (fun r => (rectangleHorizontalColumns F s r).card) +
      (Icc 1 (3 * k - 1)).sum (fun t => (rectangleVerticalColumns F s t).card) := by
  classical
  let n := 3 * k + 2
  let JH := Σ r : (Icc 1 (3 * k) : Finset Nat), (rectangleHorizontalColumns F s r.val)
  let JV := Σ t : (Icc 1 (3 * k - 1) : Finset Nat), (rectangleVerticalColumns F s t.val)
  have hbH (i : JH) : 1 ≤ i.1.val ∧ i.1.val ≤ 3 * k ∧
      2 ≤ i.2.val ∧ i.2.val ≤ 3 * k - 2 := by
    have h1 := mem_Icc.mp i.1.property
    have h2 := mem_Icc.mp (mem_filter.mp i.2.property).1
    omega
  have hbV (i : JV) : 1 ≤ i.1.val ∧ i.1.val ≤ 3 * k - 1 ∧
      2 ≤ i.2.val ∧ i.2.val ≤ 3 * k - 1 := by
    have h1 := mem_Icc.mp i.1.property
    have h2 := mem_Icc.mp (mem_filter.mp i.2.property).1
    omega
  let hEdge (i : JH) : Sym2 (GridVertex n n) :=
    s(sideChart s (⟨i.2.val, by have := hbH i; omega⟩,
        ⟨i.1.val - 1, by have := hbH i; omega⟩),
      sideChart s (⟨i.2.val + 1, by have := hbH i; omega⟩,
        ⟨i.1.val - 1, by have := hbH i; omega⟩))
  let vEdge (i : JV) : Sym2 (GridVertex n n) :=
    s(sideChart s (⟨i.2.val, by have := hbV i; omega⟩,
        ⟨i.1.val - 1, by have := hbV i; omega⟩),
      sideChart s (⟨i.2.val, by have := hbV i; omega⟩,
        ⟨i.1.val, by have := hbV i; omega⟩))
  let edge : JH ⊕ JV → Sym2 (GridVertex n n) := Sum.elim hEdge vEdge
  let N := (↑(nonpureVertices F) : Set (↑F : Set (GridVertex n n)))
  let val : N → GridVertex n n := fun u => u.val.val
  have hval : Function.Injective val := by
    intro u v he
    exact Subtype.ext (Subtype.ext he)
  have horizontal (a b : GridVertex n n)
      (ha : 2 ≤ a.1.val ∧ a.1.val + 2 < n ∧ a.2.val + 2 < n)
      (hb : 2 ≤ b.1.val ∧ b.1.val + 2 < n ∧ b.2.val + 2 < n)
      (haF : sideChart s a ∈ F) (hbF : sideChart s b ∈ F)
      (hy : a.2 = b.2) (hx : a.1.val + 1 = b.1.val) :
      ∃ i : JH, hEdge i = s(sideChart s a, sideChart s b) := by
    have hr : a.2.val + 1 ∈ Icc 1 (3 * k) := mem_Icc.mpr (by dsimp [n] at ha; omega)
    have hxM : a.1.val ∈ rectangleHorizontalColumns F s (a.2.val + 1) := by
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr (by dsimp [n] at ha hb; omega), by omega, by omega, ?_, ?_⟩
      · simpa only [Nat.add_sub_cancel, Fin.eta] using haF
      · have he : (⟨a.1.val + 1, by omega⟩, ⟨a.2.val + 1 - 1, by omega⟩) = b :=
          Prod.ext (Fin.ext hx) (by simpa only [Nat.add_sub_cancel, Fin.eta] using hy)
        simpa only [he] using hbF
    refine ⟨⟨⟨a.2.val + 1, hr⟩, ⟨a.1.val, hxM⟩⟩, ?_⟩
    change s(sideChart s a, sideChart s (⟨a.1.val + 1, by omega⟩, a.2)) = _
    exact congrArg (fun w => s(sideChart s a, sideChart s w)) (Prod.ext (Fin.ext hx) hy)
  have vertical (a b : GridVertex n n)
      (ha : 2 ≤ a.1.val ∧ a.1.val + 2 < n ∧ a.2.val + 2 < n)
      (hb : 2 ≤ b.1.val ∧ b.1.val + 2 < n ∧ b.2.val + 2 < n)
      (haF : sideChart s a ∈ F) (hbF : sideChart s b ∈ F)
      (hx : a.1 = b.1) (hy : a.2.val + 1 = b.2.val) :
      ∃ i : JV, vEdge i = s(sideChart s a, sideChart s b) := by
    have ht : b.2.val ∈ Icc 1 (3 * k - 1) := mem_Icc.mpr (by dsimp [n] at hb; omega)
    have hxM : a.1.val ∈ rectangleVerticalColumns F s b.2.val := by
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr (by dsimp [n] at ha; omega), a.1.isLt, b.2.isLt, ?_, ?_⟩
      · have he : (⟨a.1.val, a.1.isLt⟩, ⟨b.2.val - 1, by omega⟩) = a :=
          Prod.ext rfl (Fin.ext (by change b.2.val - 1 = a.2.val; omega))
        simpa only [he] using haF
      · simpa only [Fin.eta, hx] using hbF
    refine ⟨⟨⟨b.2.val, ht⟩, ⟨a.1.val, hxM⟩⟩, ?_⟩
    change s(sideChart s (a.1, ⟨b.2.val - 1, by omega⟩), sideChart s (a.1, b.2)) = _
    refine congrArg₂ Sym2.mk ?_ ?_
    · exact congrArg (sideChart s) (Prod.ext rfl (Fin.ext (by change b.2.val - 1 = a.2.val; omega)))
    · exact congrArg (sideChart s) (Prod.ext hx rfl)
  have hrect (u : N) (a : GridVertex n n) (he : val u = sideChart s a) :
      2 ≤ a.1.val ∧ a.1.val + 2 < n ∧ a.2.val + 2 < n := by
    have huF : sideChart s a ∈ F := he ▸ u.val.property
    have huNP := (mem_filter.mp u.property).2
    have hue : u.val = ⟨sideChart s a, huF⟩ := Subtype.ext he
    rw [hue] at huNP
    exact (cost_two_nonpure_rectangle_iff (by omega) F hacyc s hmissing hW a huF).mp huNP
  have hcover : ∀ e ∈ (nonpureGraph F).edgeFinset, ∃ i, edge i = Sym2.map val e := by
    intro e
    refine Sym2.inductionOn e ?_
    intro u v huv
    have hadj : (nonpureGraph F).Adj u v := by simpa using huv
    obtain ⟨a, hea⟩ := sideChart_surjective s (val u)
    obtain ⟨b, heb⟩ := sideChart_surjective s (val v)
    have ha := hrect u a hea.symm
    have hb := hrect v b heb.symm
    have haF : sideChart s a ∈ F := hea.symm ▸ u.val.property
    have hbF : sideChart s b ∈ F := heb.symm ▸ v.val.property
    have hadj' : (gridGraph n n).Adj a b := by
      apply (sideChart_adj s a b).mp
      rw [hea, heb]
      exact hadj
    have hc : (a.2 = b.2 ∧ a.1.val + 1 = b.1.val) ∨
        (b.2 = a.2 ∧ b.1.val + 1 = a.1.val) ∨
        (a.1 = b.1 ∧ a.2.val + 1 = b.2.val) ∨
        (b.1 = a.1 ∧ b.2.val + 1 = a.2.val) := by
      simp only [gridGraph, adjacent, Fin.ext_iff] at hadj'
      simp only [Fin.ext_iff]
      omega
    change ∃ i, edge i = s(val u, val v)
    rw [← hea, ← heb]
    rcases hc with ⟨hy, hx⟩ | ⟨hy, hx⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · obtain ⟨i, hi⟩ := horizontal a b ha hb haF hbF hy hx
      exact ⟨Sum.inl i, hi⟩
    · obtain ⟨i, hi⟩ := horizontal b a hb ha hbF haF hy hx
      exact ⟨Sum.inl i, hi.trans Sym2.eq_swap⟩
    · obtain ⟨i, hi⟩ := vertical a b ha hb haF hbF hx hy
      exact ⟨Sum.inr i, hi⟩
    · obtain ⟨i, hi⟩ := vertical b a hb ha hbF haF hx hy
      exact ⟨Sum.inr i, hi.trans Sym2.eq_swap⟩
  have hsub : (nonpureGraph F).edgeFinset.image (Sym2.map val) ⊆ univ.image edge := by
    intro e he
    obtain ⟨z, hz, heq⟩ := mem_image.mp he
    obtain ⟨i, hi⟩ := hcover z hz
    exact mem_image.mpr ⟨i, mem_univ _, hi.trans heq⟩
  have hcount := (card_le_card hsub).trans card_image_le
  rw [card_image_of_injective _ (Sym2.map.injective hval), card_univ, Fintype.card_sum] at hcount
  have hHC : Fintype.card JH = (Icc 1 (3 * k)).sum
      (fun r => (rectangleHorizontalColumns F s r).card) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    exact sum_coe_sort (Icc 1 (3 * k)) (fun r => (rectangleHorizontalColumns F s r).card)
  have hVC : Fintype.card JV = (Icc 1 (3 * k - 1)).sum
      (fun t => (rectangleVerticalColumns F s t).card) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    exact sum_coe_sort (Icc 1 (3 * k - 1)) (fun t => (rectangleVerticalColumns F s t).card)
  rwa [hHC, hVC] at hcount

end GridGraphs.CarrierLayers.ThreeCarrier
