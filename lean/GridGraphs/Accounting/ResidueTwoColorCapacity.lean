import GridGraphs.Routing.CanonicalDemandPhase
import GridGraphs.Accounting.CheckerboardContourMarks

/-!
# Color capacity of residue-two contour markings

This file records only finite-cardinality consequences of a hypothetical
color-respecting injection of canonical demands into one anchor and the cotree
contour marks.  In particular, none of the marking structures below is asserted
to exist.
-/

namespace GridGraphs

open Finset SimpleGraph

private def sumSubtypeEquiv {A R : Type*} (s : A ⊕ R → Prop)
    (p : A → Prop) (q : R → Prop) (hl : ∀ a, s (.inl a) ↔ p a)
    (hr : ∀ r, s (.inr r) ↔ q r) : {x // s x} ≃ {a // p a} ⊕ {r // q r} where
  toFun x := by
    rcases x with ⟨a | r, h⟩
    · exact Sum.inl ⟨a, (hl a).mp h⟩
    · exact Sum.inr ⟨r, (hr r).mp h⟩
  invFun x := by
    rcases x with a | r
    · exact ⟨Sum.inl a.1, (hl a.1).mpr a.2⟩
    · exact ⟨Sum.inr r.1, (hr r.1).mpr r.2⟩
  left_inv x := by rcases x with ⟨a | r, h⟩ <;> rfl
  right_inv x := by rcases x with a | r <;> rfl

/-- A colored injection into one colored anchor and a finite colored resource
has the corresponding colorwise capacity bounds. -/
theorem colored_anchor_capacity {D R A : Type*} [Fintype D] [Fintype R]
    [Fintype A] [Unique A]
    [DecidableEq D] [DecidableEq R] (dBlack : D → Prop) (rBlack : R → Prop)
    [DecidablePred dBlack] [DecidablePred rBlack] (anchorBlack : Bool)
    (f : D ↪ A ⊕ R)
    (hcolor : ∀ d, dBlack d ↔ match f d with
      | .inl _ => anchorBlack = true
      | .inr r => rBlack r) :
    Fintype.card {d // dBlack d} ≤
        (if anchorBlack then 1 else 0) +
          Fintype.card {r // rBlack r} ∧
      Fintype.card {d // ¬dBlack d} ≤
        (if anchorBlack then 0 else 1) +
          Fintype.card {r // ¬rBlack r} := by
  classical
  let targetBlack : A ⊕ R → Prop
    | .inl _ => anchorBlack = true
    | .inr r => rBlack r
  let blackMap : {d // dBlack d} ↪ {x // targetBlack x} :=
    { toFun := fun d => ⟨f d.1,
        show targetBlack (f d.1) from (hcolor d.1).mp d.2⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        exact f.injective (congrArg Subtype.val hxy) }
  let whiteMap : {d // ¬dBlack d} ↪ {x // ¬targetBlack x} :=
    { toFun := fun d => ⟨f d.1,
        show ¬targetBlack (f d.1) from fun hx => d.2 ((hcolor d.1).mpr hx)⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        exact f.injective (congrArg Subtype.val hxy) }
  have hblack := Fintype.card_le_of_injective blackMap blackMap.injective
  have hwhite := Fintype.card_le_of_injective whiteMap whiteMap.injective
  have hblackCard : Fintype.card {x : A ⊕ R // targetBlack x} =
      (if anchorBlack then 1 else 0) + Fintype.card {r // rBlack r} := by
    rw [Fintype.card_congr (sumSubtypeEquiv targetBlack
      (fun _ : A => anchorBlack = true) rBlack (by simp [targetBlack])
      (by simp [targetBlack])), Fintype.card_sum]
    cases anchorBlack <;> simp [Fintype.card_unique]
  have hwhiteCard : Fintype.card {x : A ⊕ R // ¬targetBlack x} =
      (if anchorBlack then 0 else 1) + Fintype.card {r // ¬rBlack r} := by
    rw [Fintype.card_congr (sumSubtypeEquiv (fun x => ¬targetBlack x)
      (fun _ : A => anchorBlack ≠ true) (fun r => ¬rBlack r)
      (by simp [targetBlack]) (by simp [targetBlack])), Fintype.card_sum]
    cases anchorBlack <;> simp [Fintype.card_unique]
  exact ⟨hblack.trans_eq hblackCard, hwhite.trans_eq hwhiteCard⟩

/-- A hypothetical canonical-demand marking with one explicitly colored anchor.
Every image, including the anchor, has the checkerboard color of its demand. -/
structure ColorAnchoredContourMarking {n : Nat} (axis : ShoreSweepAxis)
    (hn : 2 ≤ n) (T : SimpleGraph (GridVertex n n)) (inst : DecidableRel T.Adj) where
  anchorBlack : Bool
  toEmbedding : CanonicalShoreDemand axis n ↪ PUnit ⊕ @CotreeContourMark n n T inst
  markBlack : @CotreeContourMark n n T inst → Prop
  markBlack_iff : ∀ mark, markBlack mark ↔
    (@CotreeContourMark.vertex n n T inst mark) ∈ gridBlack n n
  color_respecting : ∀ q,
    (CanonicalShoreDemand.boundaryIncidence axis hn q).1 ∈ gridBlack n n ↔
      match toEmbedding q with
      | .inl _ => anchorBlack = true
      | .inr mark => markBlack mark

namespace ColorAnchoredContourMarking

/-- Black and white canonical demands fit respectively into the anchor, when it
has that color, and the corresponding contour-mark fiber. -/
theorem demand_color_capacities {n : Nat} {axis : ShoreSweepAxis} {hn : 2 ≤ n}
    {T : SimpleGraph (GridVertex n n)} [inst : DecidableRel T.Adj]
    (M : ColorAnchoredContourMarking axis hn T inst) :
    (CanonicalShoreDemand.blackDemands axis hn).card ≤
        (if M.anchorBlack then 1 else 0) +
          Fintype.card (BlackCotreeContourMark T) ∧
      (CanonicalShoreDemand.whiteDemands axis hn).card ≤
        (if M.anchorBlack then 0 else 1) +
          Fintype.card (WhiteCotreeContourMark T) := by
  classical
  rcases M with ⟨anchorBlack, toEmbedding, markBlack, markBlack_iff,
    color_respecting⟩
  have h := colored_anchor_capacity
    (fun q : CanonicalShoreDemand axis n =>
      (CanonicalShoreDemand.boundaryIncidence axis hn q).1 ∈ gridBlack n n)
    markBlack
    anchorBlack toEmbedding (by
      intro q
      rcases hq : toEmbedding q with u | mark
      · simpa [hq] using color_respecting q
      · simpa [hq] using color_respecting q)
  have hmarkBlack : Fintype.card {mark // markBlack mark} =
      Fintype.card (BlackCotreeContourMark T) := by
    exact Fintype.card_congr (Equiv.subtypeEquivRight markBlack_iff)
  have hmarkWhite : Fintype.card {mark // ¬markBlack mark} =
      Fintype.card (WhiteCotreeContourMark T) := by
    apply Fintype.card_congr (Equiv.subtypeEquivRight _)
    intro mark
    simp [gridWhite, markBlack_iff]
  rw [hmarkBlack] at h
  rw [hmarkWhite] at h
  constructor
  · simpa [CanonicalShoreDemand.blackDemands, BlackCotreeContourMark,
      CotreeContourMarkOn, Fintype.card_subtype] using h.1
  · simpa [CanonicalShoreDemand.whiteDemands, WhiteCotreeContourMark,
      CotreeContourMarkOn, gridWhite, Fintype.card_subtype] using h.2

end ColorAnchoredContourMarking

/-! The next four lemmas are the reusable pure `Nat` rigidity calculation. -/

theorem residueTwo_tight_even_capacity {a b w : Nat} {anchorBlack : Bool}
    (hsum : b + w = 2 * a)
    (hblack : 3 * a + 2 ≤ (if anchorBlack then 1 else 0) + (3 * b + 2))
    (hwhite : 3 * a + 3 ≤ (if anchorBlack then 0 else 1) + (3 * w + 2)) :
    anchorBlack = false ∧ b = a ∧ w = a := by
  cases anchorBlack <;> simp_all <;> omega

theorem residueTwo_tight_odd_capacity {a b w : Nat} {anchorBlack : Bool}
    (hsum : b + w = 2 * a + 1)
    (hblack : 3 * a + 6 ≤ (if anchorBlack then 1 else 0) + (3 * b + 2))
    (hwhite : 3 * a + 2 ≤ (if anchorBlack then 0 else 1) + (3 * w + 2)) :
    anchorBlack = true ∧ b = a + 1 ∧ w = a := by
  cases anchorBlack <;> simp_all <;> omega

theorem residueTwo_near_even_capacity {a b w : Nat} {anchorBlack : Bool}
    (hsum : b + w = 2 * a + 1)
    (hblack : 3 * a + 2 ≤ (if anchorBlack then 1 else 0) + (3 * b + 2))
    (hwhite : 3 * a + 3 ≤ (if anchorBlack then 0 else 1) + (3 * w + 2)) :
    (anchorBlack = true ∧ b = a ∧ w = a + 1) ∨
      (anchorBlack = false ∧
        ((b = a + 1 ∧ w = a) ∨ (b = a ∧ w = a + 1))) := by
  cases anchorBlack <;> simp_all <;> omega

theorem residueTwo_near_odd_capacity {a b w : Nat} {anchorBlack : Bool}
    (hsum : b + w = 2 * a + 2)
    (hblack : 3 * a + 6 ≤ (if anchorBlack then 1 else 0) + (3 * b + 2))
    (hwhite : 3 * a + 2 ≤ (if anchorBlack then 0 else 1) + (3 * w + 2)) :
    (b = a + 2 ∧ w = a) ∨
      (anchorBlack = true ∧ b = a + 1 ∧ w = a + 1) := by
  cases anchorBlack <;> simp_all <;> omega

/-! Thin geometric wrappers combine those calculations with the existing color
counts and waste normal forms. -/

theorem residueTwo_tight_color_capacity_even (axis : ShoreSweepAxis) (a : Nat)
    {T : SimpleGraph (GridVertex (3 * (2 * a) + 2) (3 * (2 * a) + 2))}
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * (2 * a) + 2) (3 * (2 * a) + 2)) T)
    (M : ColorAnchoredContourMarking axis (by omega) T (inferInstance))
    (heq : incidenceWaste (gridGraph (3 * (2 * a) + 2) (3 * (2 * a) + 2) \ T) =
      (3 * (2 * a) + 2) + 2) :
    M.anchorBlack = false ∧
      incidenceWasteOn (gridGraph (3 * (2 * a) + 2) (3 * (2 * a) + 2) \ T)
          (gridBlack _ _) = 3 * a + 2 ∧
      incidenceWasteOn (gridGraph (3 * (2 * a) + 2) (3 * (2 * a) + 2) \ T)
          (gridWhite _ _) = 3 * a + 2 := by
  obtain ⟨b, w, hb, hw, hsum⟩ :=
    residueTwo_color_waste_normal_form (k := 2 * a) hT heq
  obtain ⟨hcapB, hcapW⟩ := M.demand_color_capacities
  rw [(CanonicalShoreDemand.card_colors_even axis a).1,
    card_blackCotreeContourMark_eq_incidenceWasteOn (by omega) (by omega) hT,
    hb] at hcapB
  rw [(CanonicalShoreDemand.card_colors_even axis a).2,
    card_whiteCotreeContourMark_eq_incidenceWasteOn (by omega) (by omega) hT,
    hw] at hcapW
  obtain ⟨ha, rfl, rfl⟩ := residueTwo_tight_even_capacity hsum hcapB hcapW
  exact ⟨ha, by simpa using hb, by simpa using hw⟩

theorem residueTwo_tight_color_capacity_odd (axis : ShoreSweepAxis) (a : Nat)
    {T : SimpleGraph (GridVertex (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2))}
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree
      (gridGraph (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2)) T)
    (M : ColorAnchoredContourMarking axis (by omega) T (inferInstance))
    (heq : incidenceWaste
      (gridGraph (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2) \ T) =
        (3 * (2 * a + 1) + 2) + 2) :
    M.anchorBlack = true ∧
      incidenceWasteOn
          (gridGraph (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2) \ T)
          (gridBlack _ _) = 3 * (a + 1) + 2 ∧
      incidenceWasteOn
          (gridGraph (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2) \ T)
          (gridWhite _ _) = 3 * a + 2 := by
  obtain ⟨b, w, hb, hw, hsum⟩ :=
    residueTwo_color_waste_normal_form (k := 2 * a + 1) hT heq
  obtain ⟨hcapB, hcapW⟩ := M.demand_color_capacities
  rw [(CanonicalShoreDemand.card_colors_odd axis a).1,
    card_blackCotreeContourMark_eq_incidenceWasteOn (by omega) (by omega) hT,
    hb] at hcapB
  rw [(CanonicalShoreDemand.card_colors_odd axis a).2,
    card_whiteCotreeContourMark_eq_incidenceWasteOn (by omega) (by omega) hT,
    hw] at hcapW
  obtain ⟨ha, rfl, rfl⟩ := residueTwo_tight_odd_capacity hsum hcapB hcapW
  exact ⟨ha, by simpa using hb, by simpa using hw⟩

theorem residueTwo_near_color_capacity_even (axis : ShoreSweepAxis) (a : Nat)
    {T : SimpleGraph (GridVertex (3 * (2 * a) + 2) (3 * (2 * a) + 2))}
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * (2 * a) + 2) (3 * (2 * a) + 2)) T)
    (M : ColorAnchoredContourMarking axis (by omega) T (inferInstance))
    (heq : incidenceWaste (gridGraph (3 * (2 * a) + 2) (3 * (2 * a) + 2) \ T) =
      (3 * (2 * a) + 2) + 5) :
    (M.anchorBlack = true ∧
      incidenceWasteOn (gridGraph _ _ \ T) (gridBlack _ _) = 3 * a + 2 ∧
      incidenceWasteOn (gridGraph _ _ \ T) (gridWhite _ _) = 3 * (a + 1) + 2) ∨
    (M.anchorBlack = false ∧
      ((incidenceWasteOn (gridGraph _ _ \ T) (gridBlack _ _) = 3 * (a + 1) + 2 ∧
        incidenceWasteOn (gridGraph _ _ \ T) (gridWhite _ _) = 3 * a + 2) ∨
       (incidenceWasteOn (gridGraph _ _ \ T) (gridBlack _ _) = 3 * a + 2 ∧
        incidenceWasteOn (gridGraph _ _ \ T) (gridWhite _ _) = 3 * (a + 1) + 2))) := by
  obtain ⟨b, w, hb, hw, hsum⟩ :=
    residueTwo_near_color_waste_normal_form (k := 2 * a) hT heq
  obtain ⟨hcapB, hcapW⟩ := M.demand_color_capacities
  rw [(CanonicalShoreDemand.card_colors_even axis a).1,
    card_blackCotreeContourMark_eq_incidenceWasteOn (by omega) (by omega) hT,
    hb] at hcapB
  rw [(CanonicalShoreDemand.card_colors_even axis a).2,
    card_whiteCotreeContourMark_eq_incidenceWasteOn (by omega) (by omega) hT,
    hw] at hcapW
  rcases residueTwo_near_even_capacity hsum hcapB hcapW with h | h
  · obtain ⟨ha, rfl, rfl⟩ := h
    exact Or.inl ⟨ha, by simpa using hb, by simpa using hw⟩
  · obtain ⟨ha, h | h⟩ := h
    · obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨ha, Or.inl ⟨by simpa using hb, by simpa using hw⟩⟩
    · obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨ha, Or.inr ⟨by simpa using hb, by simpa using hw⟩⟩

theorem residueTwo_near_color_capacity_odd (axis : ShoreSweepAxis) (a : Nat)
    {T : SimpleGraph (GridVertex (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2))}
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree
      (gridGraph (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2)) T)
    (M : ColorAnchoredContourMarking axis (by omega) T (inferInstance))
    (heq : incidenceWaste
      (gridGraph (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2) \ T) =
        (3 * (2 * a + 1) + 2) + 5) :
    (incidenceWasteOn (gridGraph _ _ \ T) (gridBlack _ _) = 3 * (a + 2) + 2 ∧
      incidenceWasteOn (gridGraph _ _ \ T) (gridWhite _ _) = 3 * a + 2) ∨
    (M.anchorBlack = true ∧
      incidenceWasteOn (gridGraph _ _ \ T) (gridBlack _ _) = 3 * (a + 1) + 2 ∧
      incidenceWasteOn (gridGraph _ _ \ T) (gridWhite _ _) = 3 * (a + 1) + 2) := by
  obtain ⟨b, w, hb, hw, hsum⟩ :=
    residueTwo_near_color_waste_normal_form (k := 2 * a + 1) hT heq
  obtain ⟨hcapB, hcapW⟩ := M.demand_color_capacities
  rw [(CanonicalShoreDemand.card_colors_odd axis a).1,
    card_blackCotreeContourMark_eq_incidenceWasteOn (by omega) (by omega) hT,
    hb] at hcapB
  rw [(CanonicalShoreDemand.card_colors_odd axis a).2,
    card_whiteCotreeContourMark_eq_incidenceWasteOn (by omega) (by omega) hT,
    hw] at hcapW
  rcases residueTwo_near_odd_capacity hsum hcapB hcapW with h | h
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨by simpa using hb, by simpa using hw⟩
  · obtain ⟨ha, rfl, rfl⟩ := h
    exact Or.inr ⟨ha, by simpa using hb, by simpa using hw⟩

end GridGraphs
