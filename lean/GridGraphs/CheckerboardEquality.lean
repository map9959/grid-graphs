import GridGraphs.CheckerboardWaste

/-!
# Equality levels in the checkerboard boundary bound

The slack of the checkerboard inequality is exactly the excess incidence waste
above `n + 2`.  This lets equality and near-equality be studied directly in the
two checkerboard forests.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- The checkerboard boundary equation at slack `q`. -/
def CheckerboardBoundaryLevel (n q : Nat)
    (U : Finset (GridVertex n n)) : Prop :=
  let F := (Finset.univ : Finset (GridVertex n n)) \ U
  boundaryDeficiencySum n n F + U.card + 4 + q =
    3 * n + checkerboardComponentCount n U

/-- Checkerboard slack is exactly cotree waste above the universal target. -/
theorem square_grid_tree_checkerboardBoundaryLevel_iff_waste
    {n q : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    CheckerboardBoundaryLevel n q
        (supportFinset (gridGraph n n \ T)) ↔
      incidenceWaste (gridGraph n n \ T) = n + 2 + q := by
  let U := supportFinset (gridGraph n n \ T)
  let F := (Finset.univ : Finset (GridVertex n n)) \ U
  have hacyc : (forcedEdgeGraph (gridGraph n n)
      (↑F : Set (GridVertex n n))).IsAcyclic := by
    simpa only [U, F] using grid_tree_complement_forcedEdgeGraph_isAcyclic hT
  have hcount := checkerboardComponentCount_eq_component_charge_add_support U hacyc
  have hbridge := square_grid_tree_component_bridge hn hT
  have hboundary := boundaryDeficiencySum_add_compl n n U
  have htotal := total_boundaryDeficiencySum hn hn
  change checkerboardComponentCount n U = U.card +
      Fintype.card ((gridGraph n n).induce
        (↑F : Set (GridVertex n n))).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (gridGraph n n)
        (↑F : Set (GridVertex n n))).ConnectedComponent at hcount
  unfold CheckerboardBoundaryLevel
  change boundaryDeficiencySum n n F + U.card + 4 + q =
      3 * n + checkerboardComponentCount n U ↔ _
  change boundaryDeficiencySum n n U +
      Fintype.card ((gridGraph n n).induce
        (↑F : Set (GridVertex n n))).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (gridGraph n n)
        (↑F : Set (GridVertex n n))).ConnectedComponent =
      incidenceWaste (gridGraph n n \ T) + 2 at hbridge
  change boundaryDeficiencySum n n U + boundaryDeficiencySum n n F =
      boundaryDeficiencySum n n Finset.univ at hboundary
  omega

/-- Tight universal waste is the zero-slack checkerboard profile. -/
theorem square_grid_tree_checkerboard_tight_iff
    {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    CheckerboardBoundaryLevel n 0
        (supportFinset (gridGraph n n \ T)) ↔
      incidenceWaste (gridGraph n n \ T) = n + 2 := by
  simpa using square_grid_tree_checkerboardBoundaryLevel_iff_waste hn hT (q := 0)

/-- The first near-equality profile is checkerboard slack three. -/
theorem square_grid_tree_checkerboard_slack_three_iff
    {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    CheckerboardBoundaryLevel n 3
        (supportFinset (gridGraph n n \ T)) ↔
      incidenceWaste (gridGraph n n \ T) = n + 5 := by
  simpa [Nat.add_assoc] using
    square_grid_tree_checkerboardBoundaryLevel_iff_waste hn hT (q := 3)

end GridGraphs
