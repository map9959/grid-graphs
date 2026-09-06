import GridGraphs.Geometry.ContourMarks
import GridGraphs.Accounting.CheckerboardColorWaste

/-!
# Checkerboard fibers of cotree contour marks

Each abstract contour mark retains its cotree-supported grid vertex.  Splitting
marks by that actual vertex realizes the black and white incidence-waste
ledgers, rather than merely choosing color classes of the right cardinality.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace CotreeContourMark

/-- The cotree-supported grid vertex carrying a contour mark. -/
def vertex {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj] :
    CotreeContourMark T → GridVertex m n
  | Sum.inl mark => mark.1.1
  | Sum.inr mark => mark.1.1

@[simp] theorem vertex_mem_supportFinset {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (mark : CotreeContourMark T) :
    mark.vertex ∈ supportFinset (gridGraph m n \ T) := by
  rcases mark with mark | mark <;> exact mark.1.2

end CotreeContourMark

/-- Contour marks whose supported vertex lies in `C`. -/
def CotreeContourMarkOn {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (C : Finset (GridVertex m n)) :=
  {mark : CotreeContourMark T // mark.vertex ∈ C}

/-- The black checkerboard fiber of cotree contour marks. -/
abbrev BlackCotreeContourMark {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] :=
  CotreeContourMarkOn T (gridBlack m n)

/-- The white checkerboard fiber of cotree contour marks. -/
abbrev WhiteCotreeContourMark {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] :=
  CotreeContourMarkOn T (gridWhite m n)

noncomputable instance {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (C : Finset (GridVertex m n)) : Fintype (CotreeContourMarkOn T C) := by
  unfold CotreeContourMarkOn
  infer_instance

/-- A color fiber is the same pair of sigma families, restricted at their
existing supported vertex. -/
private def cotreeContourMarkOnEquiv {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj]
    (C : Finset (GridVertex m n)) :
    CotreeContourMarkOn T C ≃
      ((Σ v : ↥(supportFinset (gridGraph m n \ T) ∩ C),
          Fin (gridBoundaryDeficiency m n v.1)) ⊕
        (Σ v : ↥(supportFinset (gridGraph m n \ T) ∩ C),
          Fin (T.degree v.1 - 1))) where
  toFun mark := by
    rcases mark with ⟨mark, hC⟩
    rcases mark with ⟨v, i⟩ | ⟨v, i⟩
    · exact Sum.inl ⟨⟨v.1, Finset.mem_inter.mpr ⟨v.2, hC⟩⟩, i⟩
    · exact Sum.inr ⟨⟨v.1, Finset.mem_inter.mpr ⟨v.2, hC⟩⟩, i⟩
  invFun mark := by
    rcases mark with ⟨v, i⟩ | ⟨v, i⟩
    · exact ⟨Sum.inl ⟨⟨v.1, (Finset.mem_inter.mp v.2).1⟩, i⟩,
        (Finset.mem_inter.mp v.2).2⟩
    · exact ⟨Sum.inr ⟨⟨v.1, (Finset.mem_inter.mp v.2).1⟩, i⟩,
        (Finset.mem_inter.mp v.2).2⟩
  left_inv mark := by
    rcases mark with ⟨⟨v, i⟩ | ⟨v, i⟩, hC⟩ <;> rfl
  right_inv mark := by
    rcases mark with ⟨v, i⟩ | ⟨v, i⟩ <;> rfl

/-- Restricted contour marks realize restricted incidence waste. -/
theorem card_cotreeContourMarkOn_eq_incidenceWasteOn
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T)
    (C : Finset (GridVertex m n)) :
    Fintype.card (CotreeContourMarkOn T C) =
      incidenceWasteOn (gridGraph m n \ T) C := by
  classical
  let U := supportFinset (gridGraph m n \ T)
  rw [Fintype.card_congr (cotreeContourMarkOnEquiv T C)]
  change Fintype.card
      ((Σ v : ↥(U ∩ C), Fin (gridBoundaryDeficiency m n v.1)) ⊕
        (Σ v : ↥(U ∩ C), Fin (T.degree v.1 - 1))) = _
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.univ_eq_attach, Finset.sum_attach,
    (U ∩ C).sum_attach (fun v => T.degree v - 1)]
  unfold incidenceWasteOn
  change (∑ v ∈ U ∩ C, gridBoundaryDeficiency m n v) +
      ∑ v ∈ U ∩ C, (T.degree v - 1) =
        ∑ v ∈ U ∩ C, (3 - (gridGraph m n \ T).degree v)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  exact (cotree_local_waste_eq_boundary_add_tree_returns hm hn hT v).symm

/-- Black contour marks count black cotree incidence waste. -/
theorem card_blackCotreeContourMark_eq_incidenceWasteOn
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    Fintype.card (BlackCotreeContourMark T) =
      incidenceWasteOn (gridGraph m n \ T) (gridBlack m n) :=
  card_cotreeContourMarkOn_eq_incidenceWasteOn hm hn hT _

/-- White contour marks count white cotree incidence waste. -/
theorem card_whiteCotreeContourMark_eq_incidenceWasteOn
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    Fintype.card (WhiteCotreeContourMark T) =
      incidenceWasteOn (gridGraph m n \ T) (gridWhite m n) :=
  card_cotreeContourMarkOn_eq_incidenceWasteOn hm hn hT _

/-- Every mark lies in exactly one of its two checkerboard fibers. -/
theorem cotreeContourMark_black_or_white {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (mark : CotreeContourMark T) :
    (mark.vertex ∈ gridBlack m n ∨ mark.vertex ∈ gridWhite m n) ∧
      ¬(mark.vertex ∈ gridBlack m n ∧ mark.vertex ∈ gridWhite m n) := by
  by_cases hblack : mark.vertex ∈ gridBlack m n
  · exact ⟨Or.inl hblack, fun h => (Finset.mem_sdiff.mp h.2).2 h.1⟩
  · exact ⟨Or.inr (by simp [gridWhite, hblack]), fun h => hblack h.1⟩

/-- The cardinal sum of the two color fibers is total cotree incidence waste. -/
theorem card_black_add_card_white_eq_incidenceWaste
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    Fintype.card (BlackCotreeContourMark T) +
        Fintype.card (WhiteCotreeContourMark T) =
      incidenceWaste (gridGraph m n \ T) := by
  rw [card_blackCotreeContourMark_eq_incidenceWasteOn hm hn hT,
    card_whiteCotreeContourMark_eq_incidenceWasteOn hm hn hT,
    grid_incidenceWaste_eq_black_add_white]

/-- The two color fibers partition all contour marks cardinally. -/
theorem card_black_add_card_white_eq_card_cotreeContourMark
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    Fintype.card (BlackCotreeContourMark T) +
        Fintype.card (WhiteCotreeContourMark T) =
      Fintype.card (CotreeContourMark T) := by
  rw [card_black_add_card_white_eq_incidenceWaste hm hn hT,
    card_cotreeContourMark_eq_incidenceWaste hm hn hT]

end GridGraphs
