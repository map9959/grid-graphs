import GridGraphs.Core.Spanning
import GridGraphs.Accounting.IncidenceWaste

/-!
# Cotree support and incidence waste

For a spanning subtree `T` of a grid, the cotree `gridGraph m n \ T` records
exactly the degree deficiency at every vertex.  This gives a subtraction-free
partition of the vertices and an exact incidence-waste ledger.
-/

namespace GridGraphs

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Removing a subgraph subtracts its degree at each vertex. -/
theorem degree_sdiff_of_le (G T : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel T.Adj] (hTG : T ≤ G) (v : V) :
    (G \ T).degree v = G.degree v - T.degree v := by
  have hneighbors : T.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    simp only [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hTG hw
  show ((G \ T).neighborFinset v).card = G.degree v - T.degree v
  rw [show (G \ T).neighborFinset v = G.neighborFinset v \ T.neighborFinset v by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff]
    rfl]
  exact Finset.card_sdiff_of_subset hneighbors

/-- The cotree supports a vertex exactly when deleting `T` changes its degree. -/
theorem mem_supportFinset_sdiff_iff_degree_ne (G T : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel T.Adj] (hTG : T ≤ G) (v : V) :
    v ∈ supportFinset (G \ T) ↔ T.degree v ≠ G.degree v := by
  rw [mem_supportFinset, degree_sdiff_of_le G T hTG]
  have hle : T.degree v ≤ G.degree v := T.degree_le_of_le hTG
  omega

/-- Equivalently, cotree support is failure to preserve incident edges. -/
theorem mem_supportFinset_sdiff_iff_not_preserves (G T : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel T.Adj] (hTG : T ≤ G) (v : V) :
    v ∈ supportFinset (G \ T) ↔ ¬ preservesIncidentEdges G T v := by
  rw [mem_supportFinset_sdiff_iff_degree_ne G T hTG]
  constructor
  · intro hne hp
    apply hne
    have heq : T.neighborFinset v = G.neighborFinset v := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => hTG h, fun h => hp h⟩
    exact congrArg Finset.card heq
  · intro hnp heq
    apply hnp
    intro w hGw
    have hsub : T.neighborFinset v ⊆ G.neighborFinset v := by
      intro x hx
      simp only [SimpleGraph.mem_neighborFinset] at hx ⊢
      exact hTG hx
    have hfin : T.neighborFinset v = G.neighborFinset v :=
      Finset.eq_of_subset_of_card_le hsub (by simpa only [SimpleGraph.degree] using heq.symm.le)
    simpa only [← SimpleGraph.mem_neighborFinset, ← hfin] using hGw

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

/-- In a grid cotree, degree is exactly vertex deficiency. -/
theorem grid_cotree_degree_eq_vertexDeficiency (hTG : T ≤ gridGraph m n)
    (v : GridVertex m n) :
    (gridGraph m n \ T).degree v = vertexDeficiency m n T v := by
  exact degree_sdiff_of_le (gridGraph m n) T hTG v

/-- The support of the grid cotree is precisely the non-preserved vertices. -/
theorem grid_cotree_supportFinset_eq (hTG : T ≤ gridGraph m n) :
    supportFinset (gridGraph m n \ T) =
      (Finset.univ : Finset (GridVertex m n)).filter
        (fun v => ¬ isPreserved m n T v) := by
  ext v
  rw [mem_supportFinset_sdiff_iff_degree_ne (gridGraph m n) T hTG]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold isPreserved
  rfl

/-- Cotree-supported and preserved vertices partition the grid. -/
theorem grid_cotree_support_card_add_numPreserved (hTG : T ≤ gridGraph m n) :
    (supportFinset (gridGraph m n \ T)).card + numPreserved m n T = m * n := by
  rw [grid_cotree_supportFinset_eq hTG]
  unfold numPreserved
  rw [add_comm, Finset.card_filter_add_card_filter_not]
  unfold GridVertex
  simp [Fintype.card_prod]

/-- Every cotree degree of a grid spanning subtree is at most three. -/
theorem grid_cotree_degree_le_three (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph m n) T) (v : GridVertex m n) :
    (gridGraph m n \ T).degree v ≤ 3 := by
  rw [grid_cotree_degree_eq_vertexDeficiency hT.le]
  exact vertexDeficiency_le_three hm hn hT v

/-- The sum over cotree support equals the total grid deficiency. -/
theorem sum_grid_cotree_degrees_support
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    ∑ v ∈ supportFinset (gridGraph m n \ T), (gridGraph m n \ T).degree v = D m n := by
  rw [← total_deficiency hT]
  rw [Finset.sum_congr rfl (fun v _ =>
    (grid_cotree_degree_eq_vertexDeficiency hT.le v).symm)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  rw [grid_cotree_degree_eq_vertexDeficiency hT.le]
  have hle : (gridGraph m n \ T).degree v ≤ 0 := by
    simpa only [mem_supportFinset, Nat.not_lt] using hv
  have hzero : (gridGraph m n \ T).degree v = 0 := Nat.eq_zero_of_le_zero hle
  rw [grid_cotree_degree_eq_vertexDeficiency hT.le] at hzero
  exact hzero

/-- Exact additive cotree waste identity for a grid spanning subtree. -/
theorem grid_cotree_incidenceWaste_identity (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    incidenceWaste (gridGraph m n \ T) + D m n + 3 * numPreserved m n T =
      3 * (m * n) := by
  have hw := incidenceWaste_add_degreeSum (gridGraph m n \ T)
    (grid_cotree_degree_le_three hm hn hT)
  rw [sum_grid_cotree_degrees_support hT] at hw
  have hc := grid_cotree_support_card_add_numPreserved hT.le
  omega

/-- On a square grid, the conjectural incidence-waste lower bound is exactly
the corresponding full-degree spanning-tree bound.  The additive statement
avoids truncated subtraction in the upper bound. -/
theorem diagonal_cotree_incidenceWaste_ge_iff_preserved_bound {n : Nat}
    (hn : 2 ≤ n) {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) ↔
      3 * numPreserved n n T + 4 ≤ n * n + 3 * n := by
  have hw := grid_cotree_incidenceWaste_identity hn hn hT
  have hD := D_expand (m := n) (n := n) (by omega) (by omega)
  constructor <;> intro h <;> omega

/-- Equality form of `diagonal_cotree_incidenceWaste_ge_iff_preserved_bound`. -/
theorem diagonal_cotree_incidenceWaste_eq_iff_preserved_eq {n : Nat}
    (hn : 2 ≤ n) {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    incidenceWaste (gridGraph n n \ T) = n + 2 ↔
      3 * numPreserved n n T + 4 = n * n + 3 * n := by
  have hw := grid_cotree_incidenceWaste_identity hn hn hT
  have hD := D_expand (m := n) (n := n) (by omega) (by omega)
  constructor <;> intro h <;> omega

end GridGraphs
