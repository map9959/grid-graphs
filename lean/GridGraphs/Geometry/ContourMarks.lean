import GridGraphs.Accounting.ContourWaste
import GridGraphs.Geometry.TreeContour

/-!
# Finite marked events on the grid-tree contour

Supported exterior sectors and supported contour returns are represented as one
finite type.  Its cardinality is exactly cotree incidence waste.  Subsequent
width arguments can therefore construct an injection into this type rather than
reasoning about a numerical sum.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- Marked contour events: exterior sectors at cotree-supported vertices, or
tree-contour visits after the first at such a vertex. -/
def CotreeContourMark {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] :=
  let U := supportFinset (gridGraph m n \ T)
  (Σ v : ↥U,
      Fin (gridBoundaryDeficiency m n v.1)) ⊕
    (Σ v : ↥U, Fin (T.degree v.1 - 1))

noncomputable instance {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] :
    Fintype (CotreeContourMark T) := by
  unfold CotreeContourMark
  infer_instance

/-- The finite mark type realizes the exact incidence-waste ledger. -/
theorem card_cotreeContourMark_eq_incidenceWaste
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    Fintype.card (CotreeContourMark T) =
      incidenceWaste (gridGraph m n \ T) := by
  let U := supportFinset (gridGraph m n \ T)
  have hwaste := cotree_incidenceWaste_eq_boundary_add_tree_returns hm hn hT
  change Fintype.card
      ((Σ v : ↥U,
          Fin (gridBoundaryDeficiency m n v.1)) ⊕
        (Σ v : ↥U, Fin (T.degree v.1 - 1))) = _
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.univ_eq_attach, Finset.sum_attach,
    U.sum_attach (fun v => T.degree v - 1)]
  simpa [boundaryDeficiencySum, supportedTreeReturnSum, U] using hwaste.symm

/-- A transverse injection into marked contour events is exactly the remaining
combinatorial certificate needed for the weak linear waste bound. -/
def TransverseContourMarking {n : Nat}
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj] :=
  Fin n ↪ CotreeContourMark T

/-- Any transverse marking certificate proves `W ≥ n`. -/
theorem n_le_incidenceWaste_of_transverseContourMarking
    {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (marking : TransverseContourMarking T) :
    n ≤ incidenceWaste (gridGraph n n \ T) := by
  have hcard : Fintype.card (Fin n) ≤ Fintype.card (CotreeContourMark T) :=
    Fintype.card_le_of_injective marking.toFun
      marking.injective
  rw [Fintype.card_fin,
    card_cotreeContourMark_eq_incidenceWaste hn hn hT] at hcard
  exact hcard

end GridGraphs
