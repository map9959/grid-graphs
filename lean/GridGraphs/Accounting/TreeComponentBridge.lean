import GridGraphs.Accounting.ComponentReduction
import GridGraphs.Accounting.CotreeWaste

/-!
# Tree component bridge

Vertices outside the support of a grid tree's cotree preserve every incident
grid edge.  Their forced-edge graph is therefore a forest, allowing the
component reduction identity to be combined with the cotree waste identity.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- The forced-edge graph on vertices outside the cotree support of a grid
spanning subtree is acyclic. -/
theorem grid_tree_complement_forcedEdgeGraph_isAcyclic {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    let U := supportFinset (gridGraph m n \ T)
    let F := (Finset.univ : Finset (GridVertex m n)) \ U
    (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).IsAcyclic := by
  classical
  dsimp only
  apply grid_forcedEdgeGraph_isAcyclic_of_preserves hT.isAcyclic
  intro v hv
  have hvU : v ∉ supportFinset (gridGraph m n \ T) := by
    change v ∈ (Finset.univ : Finset (GridVertex m n)) \
      supportFinset (gridGraph m n \ T) at hv
    exact (Finset.mem_sdiff.mp hv).2
  by_contra hpres
  exact hvU ((mem_supportFinset_sdiff_iff_not_preserves
    (gridGraph m n) T hT.le v).2 hpres)

/-- Exact bridge between cotree incidence waste and the two component counts
on the complement of the cotree support in a square grid. -/
theorem square_grid_tree_component_bridge {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T) :
    let U := supportFinset (gridGraph n n \ T)
    let F := (Finset.univ : Finset (GridVertex n n)) \ U
    boundaryDeficiencySum n n U +
        Fintype.card
          ((gridGraph n n).induce
            (↑F : Set (GridVertex n n))).ConnectedComponent +
        Fintype.card
          (forcedEdgeGraph (gridGraph n n)
            (↑F : Set (GridVertex n n))).ConnectedComponent =
      incidenceWaste (gridGraph n n \ T) + 2 := by
  classical
  dsimp only
  let U := supportFinset (gridGraph n n \ T)
  have hforced :
      (forcedEdgeGraph (gridGraph n n)
        (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
          Set (GridVertex n n))).IsAcyclic := by
    simpa only [U] using grid_tree_complement_forcedEdgeGraph_isAcyclic hT
  have hcomponents := square_grid_component_reduction_compl hn U hforced
  have hwaste := grid_cotree_incidenceWaste_identity hn hn hT
  have hsupport : U.card + numPreserved n n T = n * n := by
    simpa only [U] using grid_cotree_support_card_add_numPreserved hT.le
  have hD := D_expand (m := n) (n := n) (by omega) (by omega)
  change boundaryDeficiencySum n n U +
      Fintype.card
        ((gridGraph n n).induce
          (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
            Set (GridVertex n n))).ConnectedComponent +
      Fintype.card
        (forcedEdgeGraph (gridGraph n n)
          (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
            Set (GridVertex n n))).ConnectedComponent =
    incidenceWaste (gridGraph n n \ T) + 2
  omega

end GridGraphs
