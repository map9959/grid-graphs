import GridGraphs.TreeComponentBridge
import GridGraphs.Diagonal

/-!
# Structural progress toward the universal diagonal waste bound

For a grid spanning tree, let `U` be the support of its cotree.  The forced
forest on the complement of `U` cannot contain a unit-cell cycle.  Consequently
every unit cell has a whole boundary edge with both endpoints in `U`, not just
one vertex in `U`.  This is a local, tree-specific obstruction needed by any
boundary-component proof of the universal waste bound.

The remaining global step is not asserted here: for `n >= 3`, the component
charge in `square_grid_tree_component_bridge` must be at least `n + 4`.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- Every unit cell of a grid spanning tree has a boundary edge whose two
endpoints are in the support of the cotree. -/
theorem grid_tree_cotree_support_hits_cell_edge {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T)
    (r : Fin (m - 1)) (c : Fin (n - 1)) :
    let U := supportFinset (gridGraph m n \ T)
    (cell00 r c ∈ U ∧ cell01 r c ∈ U) ∨
      (cell01 r c ∈ U ∧ cell11 r c ∈ U) ∨
      (cell11 r c ∈ U ∧ cell10 r c ∈ U) ∨
      (cell10 r c ∈ U ∧ cell00 r c ∈ U) := by
  classical
  dsimp only
  let U := supportFinset (gridGraph m n \ T)
  let F := (Finset.univ : Finset (GridVertex m n)) \ U
  have hforced :
      (forcedEdgeGraph (gridGraph m n)
        (↑F : Set (GridVertex m n))).IsAcyclic := by
    simpa only [F, U] using grid_tree_complement_forcedEdgeGraph_isAcyclic hT
  have hcell := grid_cell_has_unforced_edge r c hforced
  have hnotF (v : GridVertex m n) :
      v ∉ (↑F : Set (GridVertex m n)) ↔ v ∈ U := by
    simp only [Finset.mem_coe, F, Finset.mem_sdiff,
      Finset.mem_univ, true_and, not_not]
  simpa only [hnotF] using hcell

/-- A nondegenerate grid tree's cotree is supported on at least two vertices.
The stronger preceding lemma shows that such a pair occurs on every unit cell. -/
theorem two_le_grid_tree_cotree_support_card {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    2 ≤ (supportFinset (gridGraph m n \ T)).card := by
  classical
  let r : Fin (m - 1) := ⟨0, by omega⟩
  let c : Fin (n - 1) := ⟨0, by omega⟩
  let U := supportFinset (gridGraph m n \ T)
  have hpairs := grid_tree_cotree_support_hits_cell_edge hT r c
  have pair_card_le {v w : GridVertex m n} (hvw : v ≠ w)
      (hv : v ∈ U) (hw : w ∈ U) : 2 ≤ U.card := by
    have hsubset : ({v, w} : Finset (GridVertex m n)) ⊆ U := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact hw
    simpa [Finset.card_pair hvw] using Finset.card_le_card hsubset
  change 2 ≤ U.card
  rcases hpairs with h | h | h | h
  · exact pair_card_le
      ((gridGraph m n).ne_of_adj (gridGraph_cell_adj_top r c)) h.1 h.2
  · exact pair_card_le
      ((gridGraph m n).ne_of_adj (gridGraph_cell_adj_right r c)) h.1 h.2
  · exact pair_card_le
      ((gridGraph m n).ne_of_adj (gridGraph_cell_adj_bot r c)) h.1 h.2
  · exact pair_card_le
      ((gridGraph m n).ne_of_adj (gridGraph_cell_adj_left r c)) h.1 h.2

end GridGraphs
