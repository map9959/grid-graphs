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

theorem grid_cell_has_unforced_edge {m n : Nat} (r : Fin (m - 1)) (c : Fin (n - 1))
    {F : Set (GridVertex m n)}
    (hacyc : (forcedEdgeGraph (gridGraph m n) F).IsAcyclic) :
    (cell00 r c ∉ F ∧ cell01 r c ∉ F) ∨
      (cell01 r c ∉ F ∧ cell11 r c ∉ F) ∨
      (cell11 r c ∉ F ∧ cell10 r c ∉ F) ∨
      (cell10 r c ∉ F ∧ cell00 r c ∉ F) := by
  apply fourCycle_has_unforced_edge (G := gridGraph m n)
  · left
    constructor
    · rfl
    · left
      rfl
  · right
    constructor
    · rfl
    · left
      rfl
  · left
    constructor
    · rfl
    · right
      rfl
  · right
    constructor
    · rfl
    · right
      rfl
  · intro h
    have hrow : (cell00 r c).1.val = (cell11 r c).1.val := by rw [h]
    dsimp [cell00, cell11] at hrow
    omega
  · intro h
    have hrow : (cell01 r c).1.val = (cell10 r c).1.val := by rw [h]
    dsimp [cell01, cell10] at hrow
    omega
  · exact hacyc

/-! ## Generic connected-supergraph tree existence -/

/-- Any connected graph admits a spanning tree subgraph. This is a thin wrapper
around mathlib's `Connected.exists_isTree_le`, recorded here because it is the
eventual endpoint of the construction side: after adding enough connector edges
to make a graph connected, a spanning tree exists inside it.

This lemma does **not** say that the spanning tree contains a specified forced
forest. That stronger forest-extension statement remains a separate target. -/
theorem connected_graph_has_spanning_tree {G : SimpleGraph V} [Finite V]
    (hG : G.Connected) : ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree := by
  simpa using hG.exists_isTree_le

end GridGraphs
