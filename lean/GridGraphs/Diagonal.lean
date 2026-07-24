import Mathlib
import GridGraphs.Forced

/-!
# Diagonal-grid proof reductions

This module formalizes the graph-theoretic reductions behind
`analysis/proofs_diagonal.md`. It does not prove the final diagonal counting
theorem; instead it names the induced-edge decycling condition and proves the
local 4-cycle obstruction that every future counting argument may use.
-/

namespace GridGraphs

open SimpleGraph

variable {V : Type*}

/-- `U` is an induced-edge decycling set for `G` if deleting all edges internal
to `U` leaves a forest. Equivalently, the forced-edge graph of `Uᶜ` is
acyclic. -/
def IsInducedEdgeDecyclingSet (G : SimpleGraph V) (U : Set V) : Prop :=
  (forcedEdgeGraph G Uᶜ).IsAcyclic

/-- The forced-edge graph of the complement `Uᶜ` consists of exactly the
`G`-edges that are not internal to `U`. -/
theorem forcedEdgeGraph_compl_adj_iff (G : SimpleGraph V) (U : Set V) (v w : V) :
    (forcedEdgeGraph G Uᶜ).Adj v w ↔ G.Adj v w ∧ ¬ (v ∈ U ∧ w ∈ U) := by
  constructor
  · intro h
    rcases h with ⟨hG, hv | hw⟩
    · exact ⟨hG, by intro huv; exact hv huv.1⟩
    · exact ⟨hG, by intro huv; exact hw huv.2⟩
  · intro h
    rcases h with ⟨hG, hnot⟩
    refine ⟨hG, ?_⟩
    by_cases hv : v ∈ U
    · right
      intro hw
      exact hnot ⟨hv, hw⟩
    · left
      exact hv

/-- If `F` is a set of vertices preserving all incident `G`-edges in an
acyclic graph `T`, then the complementary set of non-preserved vertices is an
induced-edge decycling set. -/
theorem compl_isInducedEdgeDecyclingSet_of_preserves {G T : SimpleGraph V} {F : Set V}
    (hT : T.IsAcyclic)
    (hF : ∀ ⦃v : V⦄, v ∈ F → preservesIncidentEdges G T v) :
    IsInducedEdgeDecyclingSet G Fᶜ := by
  unfold IsInducedEdgeDecyclingSet
  simpa using forcedEdgeGraph_isAcyclic_of_preserves hT hF

/-- If a genuine 4-cycle is acyclic in the forced-edge graph, then at least one
of its four boundary edges is not forced; equivalently, both endpoints of that
edge lie outside `F`. -/
theorem fourCycle_has_unforced_edge {G : SimpleGraph V} {F : Set V}
    {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (h_ab_cd : a ≠ c) (h_bd : b ≠ d)
    (hacyc : (forcedEdgeGraph G F).IsAcyclic) :
    (a ∉ F ∧ b ∉ F) ∨
      (b ∉ F ∧ c ∉ F) ∨
      (c ∉ F ∧ d ∉ F) ∨
      (d ∉ F ∧ a ∉ F) := by
  by_contra hnone
  push_neg at hnone
  rcases hnone with ⟨habF, hbcF, hcdF, hdaF⟩
  let H := forcedEdgeGraph G F
  have habFor : a ∈ F ∨ b ∈ F := by
    by_cases ha : a ∈ F
    · exact Or.inl ha
    · exact Or.inr (habF ha)
  have hbcFor : b ∈ F ∨ c ∈ F := by
    by_cases hb : b ∈ F
    · exact Or.inl hb
    · exact Or.inr (hbcF hb)
  have hcdFor : c ∈ F ∨ d ∈ F := by
    by_cases hc : c ∈ F
    · exact Or.inl hc
    · exact Or.inr (hcdF hc)
  have hdaFor : d ∈ F ∨ a ∈ F := by
    by_cases hd : d ∈ F
    · exact Or.inl hd
    · exact Or.inr (hdaF hd)
  have habH : H.Adj a b := ⟨hab, habFor⟩
  have hbcH : H.Adj b c := ⟨hbc, hbcFor⟩
  have hcdH : H.Adj c d := ⟨hcd, hcdFor⟩
  have hdaH : H.Adj d a := ⟨hda, hdaFor⟩
  have h_ab : a ≠ b := H.ne_of_adj habH
  have h_bc : b ≠ c := H.ne_of_adj hbcH
  have h_cd : c ≠ d := H.ne_of_adj hcdH
  have h_da : d ≠ a := H.ne_of_adj hdaH
  let q : H.Walk b a :=
    SimpleGraph.Walk.cons hbcH
      (SimpleGraph.Walk.cons hcdH
        (SimpleGraph.Walk.cons hdaH SimpleGraph.Walk.nil))
  let p : H.Walk a a := SimpleGraph.Walk.cons habH q
  have hq_path : q.IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    constructor
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      constructor
      · exact SimpleGraph.Walk.IsPath.of_adj hdaH
      · simp [h_cd, h_ab_cd.symm]
    · simp [h_bc, h_bd, h_ab.symm]
  have hq_no_ab : s(a, b) ∉ q.edges := by
    simp [q, h_ab, h_ab_cd, h_bd, h_da.symm]
  have hp_cycle : p.IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    exact ⟨hq_path, hq_no_ab⟩
  exact hacyc p hp_cycle

/-! ## Grid-cell specialization -/

def cell00 {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) : GridVertex m n :=
  (⟨r.val, by omega⟩, ⟨c.val, by omega⟩)

def cell01 {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) : GridVertex m n :=
  (⟨r.val, by omega⟩, ⟨c.val + 1, by omega⟩)

def cell11 {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) : GridVertex m n :=
  (⟨r.val + 1, by omega⟩, ⟨c.val + 1, by omega⟩)

def cell10 {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) : GridVertex m n :=
  (⟨r.val + 1, by omega⟩, ⟨c.val, by omega⟩)

/-! ### Adjacency of the four cell-edges in `gridGraph` -/

lemma gridGraph_cell_adj_top {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) :
    (gridGraph m n).Adj (cell00 r c) (cell01 r c) := by
  left; exact ⟨rfl, Or.inl rfl⟩

lemma gridGraph_cell_adj_right {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) :
    (gridGraph m n).Adj (cell01 r c) (cell11 r c) := by
  right; exact ⟨rfl, Or.inl rfl⟩

lemma gridGraph_cell_adj_bot {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) :
    (gridGraph m n).Adj (cell11 r c) (cell10 r c) := by
  left; exact ⟨rfl, Or.inr rfl⟩

lemma gridGraph_cell_adj_left {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) :
    (gridGraph m n).Adj (cell10 r c) (cell00 r c) := by
  right; exact ⟨rfl, Or.inr rfl⟩

/-! ### Diagonal disequalities of cell corners -/

lemma cell00_ne_cell11 {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) :
    cell00 r c ≠ cell11 r c := by
  intro h
  have hrow : (cell00 r c).1.val = (cell11 r c).1.val := by rw [h]
  dsimp [cell00, cell11] at hrow
  omega

lemma cell01_ne_cell10 {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1)) :
    cell01 r c ≠ cell10 r c := by
  intro h
  have hrow : (cell01 r c).1.val = (cell10 r c).1.val := by rw [h]
  dsimp [cell01, cell10] at hrow
  omega

/-- Every grid unit cell in an acyclic forced-edge graph has at least one
boundary edge whose endpoints both lie outside the full-degree set. -/
theorem grid_cell_has_unforced_edge {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1))
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic) :
    (cell00 r c ∉ F ∧ cell01 r c ∉ F) ∨
      (cell01 r c ∉ F ∧ cell11 r c ∉ F) ∨
      (cell11 r c ∉ F ∧ cell10 r c ∉ F) ∨
      (cell10 r c ∉ F ∧ cell00 r c ∉ F) :=
  fourCycle_has_unforced_edge (G := gridGraph m n)
    (gridGraph_cell_adj_top r c) (gridGraph_cell_adj_right r c)
    (gridGraph_cell_adj_bot r c) (gridGraph_cell_adj_left r c)
    (cell00_ne_cell11 r c) (cell01_ne_cell10 r c) hacyc

/-- Existence form of the cell-hitting condition: in any acyclic forced-edge
graph on the grid, every unit cell contains at least one corner outside the
full-degree set. This is a direct corollary of `grid_cell_has_unforced_edge`,
dropping the (stronger) edge-pair statement. -/
theorem grid_cell_has_unforced_corner {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1))
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic) :
    cell00 r c ∉ F ∨ cell01 r c ∉ F ∨ cell11 r c ∉ F ∨ cell10 r c ∉ F := by
  rcases grid_cell_has_unforced_edge r c hacyc with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- Spanning-subgraph specialisation of `grid_cell_has_unforced_corner`:
in any acyclic subgraph `T` of the grid graph, the set `F` of full-degree
(preserved) vertices misses at least one corner of every unit cell. -/
theorem preserved_set_cell_corner {m n : Nat}
    (r : Fin (m - 1)) (c : Fin (n - 1))
    {T : SimpleGraph (GridVertex m n)} (hT : T.IsAcyclic)
    {F : Set (GridVertex m n)}
    (hF : ∀ ⦃v : GridVertex m n⦄, v ∈ F →
            preservesIncidentEdges (gridGraph m n) T v) :
    cell00 r c ∉ F ∨ cell01 r c ∉ F ∨ cell11 r c ∉ F ∨ cell10 r c ∉ F :=
  grid_cell_has_unforced_corner r c
    (grid_forcedEdgeGraph_isAcyclic_of_preserves hT hF)

/-! ## Generic connected-supergraph tree existence -/

/-- Any connected graph admits a spanning tree subgraph. This is a thin wrapper
around mathlib's `Connected.exists_isTree_le`, recorded here because it is the
eventual endpoint of the construction side: after adding enough connector edges
to make a graph connected, a spanning tree exists inside it.

For a specified forced forest, use
`exists_isTree_preserving_of_forcedEdgeGraph_isAcyclic`. -/
theorem connected_graph_has_spanning_tree {G : SimpleGraph V} [Finite V]
    (hG : G.Connected) : ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree := by
  simpa using hG.exists_isTree_le

end GridGraphs
