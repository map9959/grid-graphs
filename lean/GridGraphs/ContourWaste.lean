import GridGraphs.CotreeWaste
import GridGraphs.ComponentReduction

/-!
# Local marks for the primal-tree contour

At a cotree-supported vertex, incidence waste splits into exterior grid sectors
and repeated visits of the boundary contour of the primal tree.  The latter are
counted algebraically here as `tree degree - 1`; the geometric contour model can
therefore target this proved ledger directly.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- Number of primal-tree contour visits after the first, summed over cotree
support. -/
def supportedTreeReturnSum {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] : Nat :=
  ∑ v ∈ supportFinset (gridGraph m n \ T), (T.degree v - 1)

/-- Pointwise split of cotree waste into missing exterior sectors and repeated
primal-tree contour visits. -/
theorem cotree_local_waste_eq_boundary_add_tree_returns
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T)
    (v : GridVertex m n) :
    3 - (gridGraph m n \ T).degree v =
      gridBoundaryDeficiency m n v + (T.degree v - 1) := by
  have hcotree := degree_sdiff_of_le (gridGraph m n) T hT.le v
  have htree : 1 ≤ T.degree v := tree_degree_pos (by nlinarith) hT v
  have htreeGrid : T.degree v ≤ (gridGraph m n).degree v :=
    T.degree_le_of_le hT.le
  have hgrid : (gridGraph m n).degree v ≤ 4 :=
    gridGraph_degree_le_four m n v
  have hcotreeThree := grid_cotree_degree_le_three hm hn hT v
  unfold gridBoundaryDeficiency
  omega

/-- Exact global marked-contour ledger: cotree incidence waste is supported
boundary deficiency plus supported primal-tree returns. -/
theorem cotree_incidenceWaste_eq_boundary_add_tree_returns
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    incidenceWaste (gridGraph m n \ T) =
      boundaryDeficiencySum m n (supportFinset (gridGraph m n \ T)) +
        supportedTreeReturnSum T := by
  unfold incidenceWaste boundaryDeficiencySum supportedTreeReturnSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  exact cotree_local_waste_eq_boundary_add_tree_returns hm hn hT v

end GridGraphs
