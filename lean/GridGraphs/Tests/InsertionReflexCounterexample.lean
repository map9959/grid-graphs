import GridGraphs.Surgery.ForcedExchange

/-!
# Degenerate counterexample to the insertion-reflex inequality

Without a hypothesis `2 <= n`, the proposed inequality

`2 * R + 3 * F.card + cU + 3 <= n * n + 3 * n`

is false.  On the `1 x 1` grid, take every vertex to be forced.  The forced
graph is a forest, maximality is vacuous, and the numerical data are
`R = 0`, `F.card = 1`, and `cU = 0`.
-/

namespace GridGraphs

open Finset SimpleGraph

theorem gridGraph_one_one_eq_bot :
    gridGraph 1 1 = (⊥ : SimpleGraph (GridVertex 1 1)) := by
  ext v w
  simp only [gridGraph, adjacent, SimpleGraph.bot_adj, iff_false]
  omega

theorem univ_maximalForcedAcyclic_one_one :
    MaximalForcedAcyclic (gridGraph 1 1)
      (Set.univ : Set (GridVertex 1 1)) := by
  constructor
  · rw [gridGraph_one_one_eq_bot]
    have hforced : forcedEdgeGraph (⊥ : SimpleGraph (GridVertex 1 1)) Set.univ = ⊥ := by
      ext v w
      simp [forcedEdgeGraph]
    rw [hforced]
    exact isAcyclic_bot
  · intro u hu
    exact (hu (Set.mem_univ u)).elim

theorem insertion_reflex_inequality_false_at_one :
    ¬(2 * 0 + 3 * (Finset.univ : Finset (GridVertex 1 1)).card + 0 + 3 ≤
      1 * 1 + 3 * 1) := by
  native_decide

end GridGraphs
