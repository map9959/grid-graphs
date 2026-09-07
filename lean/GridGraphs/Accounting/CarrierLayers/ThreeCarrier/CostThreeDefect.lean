import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostThreeRectangle

/-! # A single frame deletion costs at most two FF edges

The two resources are the incident boundary edges at the same physical
noncorner deletion. Vertical and bottom-horizontal defects cannot coexist.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

theorem cost_three_bad_edges_le_two {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) (s : Fin 4)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3) :
    (Icc 1 (3 * k - 1)).sum (fun t =>
      (rectangleVerticalColumns F s t \ Icc 3 (3 * k - 2)).card) +
      (rectangleHorizontalColumns F s (3 * k)).card ≤ 2 := by
  classical
  let n := 3 * k + 2
  let P : Set (GridVertex n n) := {v | sideChart s v ∈ F}
  have hP := sideChart_acyclic s F hacyc
  have hPT := chart_transpose_acyclic F hacyc s
  obtain ⟨c, hc, hframe⟩ := cost_three_frame_defect hk F hacyc s hW
  have hvertical (t x : Nat) (ht : t ∈ Icc 1 (3 * k - 1))
      (hx : x ∈ rectangleVerticalColumns F s t \ Icc 3 (3 * k - 2)) :
      ((x = 2 ∧ c.1.val = 0) ∨ (x = 3 * k - 1 ∧ c.1.val = 3 * k + 1)) ∧
        (t = c.2.val ∨ t = c.2.val + 1) := by
    obtain ⟨hxV, hxN⟩ := mem_sdiff.mp hx
    obtain ⟨hxI, hxn, htn, h0, h1⟩ := mem_filter.mp hxV
    have hxI' := mem_Icc.mp hxI
    have ht' := mem_Icc.mp ht
    have hxN' : ¬ (3 ≤ x ∧ x ≤ 3 * k - 2) := by simpa only [mem_Icc] using hxN
    have hxcase : x = 2 ∨ x = 3 * k - 1 := by omega
    let i := if x = 2 then 0 else 3 * k + 1
    let a : GridVertex n n := (⟨i, by dsimp [i, n]; split <;> omega⟩, ⟨t - 1, by omega⟩)
    let b : GridVertex n n := (⟨i, by dsimp [i, n]; split <;> omega⟩, ⟨t, htn⟩)
    have hab : c = a ∨ c = b := by
      by_contra h
      push Not at h
      have haF : a ∈ P := hframe a (Or.inl (by dsimp [a, i]; split <;> omega)) (Ne.symm h.1)
      have hbF : b ∈ P := hframe b (Or.inl (by dsimp [b, i]; split <;> omega)) (Ne.symm h.2)
      have he : t - 1 + 1 = t := by omega
      rcases hxcase with hx | hx
      · subst x
        apply forced_rectangle_two_rows_false (⟨0, by omega⟩ : Fin (n - 2))
          (⟨t - 1, by omega⟩ : Fin (n - 1)) hP
        · simpa only [a, i, if_pos rfl] using haF
        · simpa only [b, i, if_pos rfl, he] using hbF
        · exact h0
        · change sideChart s (⟨2, by omega⟩, ⟨t - 1 + 1, by omega⟩) ∈ F
          simpa only [he] using h1
      · have hi : i = 3 * k + 1 := by dsimp [i]; split <;> omega
        have he' : x + 2 = 3 * k + 1 := by omega
        apply forced_rectangle_two_rows_false (⟨x, by omega⟩ : Fin (n - 2))
          (⟨t - 1, by omega⟩ : Fin (n - 1)) hP h0
        · change sideChart s (⟨x, by omega⟩, ⟨t - 1 + 1, by omega⟩) ∈ F
          simpa only [he] using h1
        · change (⟨x + 2, by omega⟩, ⟨t - 1, by omega⟩) ∈ P
          simpa only [a, hi, he'] using haF
        · change (⟨x + 2, by omega⟩, ⟨t - 1 + 1, by omega⟩) ∈ P
          simpa only [b, hi, he', he] using hbF
    simp only [Prod.ext_iff, Fin.ext_iff] at hab
    dsimp [a, b, i] at hab
    split_ifs at hab <;> omega
  have hhorizontal (x : Nat) (hx : x ∈ rectangleHorizontalColumns F s (3 * k)) :
      c.2.val = 3 * k + 1 ∧ (x = c.1.val ∨ x + 1 = c.1.val) := by
    obtain ⟨hxI, hxn, hrn, h0, h1⟩ := mem_filter.mp hx
    have hxI' := mem_Icc.mp hxI
    let a : GridVertex n n := (⟨x, by omega⟩, ⟨3 * k + 1, by omega⟩)
    let b : GridVertex n n := (⟨x + 1, hxn⟩, ⟨3 * k + 1, by omega⟩)
    have hab : c = a ∨ c = b := by
      by_contra h
      push Not at h
      have haF : a ∈ P := hframe a (Or.inr (by dsimp [a]; omega)) (Ne.symm h.1)
      have hbF : b ∈ P := hframe b (Or.inr (by dsimp [b]; omega)) (Ne.symm h.2)
      have he : 3 * k - 1 + 2 = 3 * k + 1 := by omega
      apply forced_rectangle_two_rows_false (⟨3 * k - 1, by omega⟩ : Fin (n - 2))
        (⟨x, by omega⟩ : Fin (n - 1)) hPT h0 h1
      · change (⟨x, by omega⟩, ⟨3 * k - 1 + 2, by omega⟩) ∈ P
        simpa only [a, he] using haF
      · change (⟨x + 1, by omega⟩, ⟨3 * k - 1 + 2, by omega⟩) ∈ P
        simpa only [b, he] using hbF
    simp only [Prod.ext_iff, Fin.ext_iff] at hab
    dsimp [a, b] at hab
    omega
  let JV := Σ t : (Icc 1 (3 * k - 1) : Finset Nat),
    ↥(rectangleVerticalColumns F s t.val \ Icc 3 (3 * k - 2))
  let JH := rectangleHorizontalColumns F s (3 * k)
  let f : JV ⊕ JH → Fin 2 := Sum.elim
    (fun i => if i.1.val = c.2.val then 0 else 1)
    (fun x => if x.val = c.1.val then 0 else 1)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) he
    · have ha := hvertical a.1.val a.2.val a.1.property a.2.property
      have hb := hvertical b.1.val b.2.val b.1.property b.2.property
      have he' := congrArg Fin.val he
      dsimp [f] at he'
      have ht : a.1 = b.1 := by apply Subtype.ext; split_ifs at he' <;> omega
      have hx : a.2.val = b.2.val := by omega
      apply congrArg Sum.inl
      rcases a with ⟨ta, xa⟩
      rcases b with ⟨tb, xb⟩
      dsimp only at ht hx
      subst tb
      exact congrArg (Sigma.mk ta) (Subtype.ext hx)
    · have ha := hvertical a.1.val a.2.val a.1.property a.2.property
      have hb := hhorizontal b.val b.property
      unfold BoundarySix.Corner at hc
      omega
    · have ha := hhorizontal a.val a.property
      have hb := hvertical b.1.val b.2.val b.1.property b.2.property
      unfold BoundarySix.Corner at hc
      omega
    · have ha := hhorizontal a.val a.property
      have hb := hhorizontal b.val b.property
      have he' := congrArg Fin.val he
      dsimp [f] at he'
      apply congrArg Sum.inr
      apply Subtype.ext
      split_ifs at he' <;> omega
  have hcount := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] at hcount
  have hVC : Fintype.card JV = (Icc 1 (3 * k - 1)).sum (fun t =>
      (rectangleVerticalColumns F s t \ Icc 3 (3 * k - 2)).card) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    exact sum_coe_sort _ (fun t => (rectangleVerticalColumns F s t \ Icc 3 (3 * k - 2)).card)
  rwa [hVC] at hcount

end GridGraphs.CarrierLayers.ThreeCarrier
