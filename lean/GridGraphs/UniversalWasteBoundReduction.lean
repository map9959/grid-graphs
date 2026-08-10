import GridGraphs.LinearWaste

/-!
# Exact four-side reduction of the universal waste bound

This module closes the bookkeeping between the tree component bridge and the
four-side component rank.  The remaining inequality is thereby stated purely
as a rank inequality, with no loss in either direction.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- On the cotree support of a square grid tree, the four-side component rank
is exactly two more than cotree incidence waste. -/
theorem fourSideComponentRank_cotree_support_eq_incidenceWaste_add_two
    {n : Nat} (hn : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    fourSideComponentRank n (supportFinset (gridGraph n n \ T)) =
      incidenceWaste (gridGraph n n \ T) + 2 := by
  let U := supportFinset (gridGraph n n \ T)
  have hrank := fourSideComponentRank_eq_component_charge (by omega : 2 ≤ n) U
  have hbridge := square_grid_tree_component_bridge (by omega : 2 ≤ n) hT
  dsimp only at hbridge
  change fourSideComponentRank n U =
    incidenceWaste (gridGraph n n \ T) + 2
  rw [hrank]
  exact hbridge

/-- Exact rank form of the universal diagonal waste inequality.  In
particular, proving the right side requires precisely the requested
`n + 4` four-side rank bound, with no scalar annular surrogate. -/
theorem square_grid_tree_universalWaste_iff_fourSideComponentRank
    {n : Nat} (hn : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) ↔
      n + 4 ≤ fourSideComponentRank n
        (supportFinset (gridGraph n n \ T)) := by
  rw [fourSideComponentRank_cotree_support_eq_incidenceWaste_add_two hn hT]
  omega

end GridGraphs
