import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import GridGraphs.Defs
import GridGraphs.ForestExtension

/-!
# Forced edges from full-degree vertices

If a vertex is full-degree in a spanning tree/subgraph `T` of a graph `G`,
then every `G`-edge incident to that vertex is forced to lie in `T`.
Consequently, the graph consisting of all edges incident to a chosen set `F`
of full-degree vertices is a subgraph of `T`. In particular, if `T` is
acyclic, the forced-edge graph is acyclic.

This is the graph-theoretic lemma behind the proposed upper-bound DP on
possible full-degree vertex sets.
-/

namespace GridGraphs

open SimpleGraph

variable {V : Type*}

/-- The graph consisting of every `G`-edge incident to at least one vertex in
`F`. If `F` is a set of full-degree vertices in a tree `T`, these are exactly
the edges that are forced to be present in `T` by fullness. -/
def forcedEdgeGraph (G : SimpleGraph V) (F : Set V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (v ∈ F ∨ w ∈ F)
  symm := by
    intro v w h
    constructor
    · exact G.symm h.1
    · rcases h.2 with hv | hw
      · exact Or.inr hv
      · exact Or.inl hw
  loopless := by
    intro v h
    exact G.loopless v h.1

/-- Vertex `v` preserves all incident `G`-edges in `T`. This avoids committing
to a particular finite-degree API: it is the edge-containment formulation of
full-degree preservation. -/
def preservesIncidentEdges (G T : SimpleGraph V) (v : V) : Prop :=
  ∀ ⦃w : V⦄, G.Adj v w → T.Adj v w

/-- Every forced edge is an edge of the ambient graph. -/
theorem forcedEdgeGraph_le (G : SimpleGraph V) (F : Set V) :
    forcedEdgeGraph G F ≤ G := by
  intro v w h
  exact h.1

/-- Enlarging the forced vertex set can only add forced edges. -/
theorem forcedEdgeGraph_mono (G : SimpleGraph V) {F₁ F₂ : Set V}
    (hF : F₁ ⊆ F₂) :
    forcedEdgeGraph G F₁ ≤ forcedEdgeGraph G F₂ := by
  intro v w hvw
  refine ⟨hvw.1, ?_⟩
  exact hvw.2.elim (fun hv => Or.inl (hF hv)) (fun hw => Or.inr (hF hw))

/-- De-forcing vertices only removes edges from the forced-edge graph. -/
theorem forcedEdgeGraph_diff_le (G : SimpleGraph V) (F D : Set V) :
    forcedEdgeGraph G (F \ D) ≤ forcedEdgeGraph G F :=
  forcedEdgeGraph_mono G Set.diff_subset

/-- De-forcing vertices preserves acyclicity of the forced-edge graph. -/
theorem forcedEdgeGraph_diff_isAcyclic (G : SimpleGraph V) {F : Set V}
    (hF : (forcedEdgeGraph G F).IsAcyclic) (D : Set V) :
    (forcedEdgeGraph G (F \ D)).IsAcyclic :=
  hF.anti (forcedEdgeGraph_diff_le G F D)

/-- An edge between an already unforced vertex and a deleted forced vertex is
absent after the deletion. -/
theorem not_forcedEdgeGraph_diff_adj_of_not_mem_of_mem
    (G : SimpleGraph V) {F D : Set V} {x y : V}
    (hx : x ∉ F) (hy : y ∈ D) :
    ¬(forcedEdgeGraph G (F \ D)).Adj x y := by
  rintro ⟨_, hxy⟩
  exact hxy.elim (fun hxF => hx hxF.1) (fun hyF => hyF.2 hy)

/-- Containing the forced-edge graph preserves every ambient edge incident to
a vertex in `F`. -/
theorem preservesIncidentEdges_of_forcedEdgeGraph_le {G T : SimpleGraph V}
    {F : Set V} (h : forcedEdgeGraph G F ≤ T) :
    ∀ ⦃v : V⦄, v ∈ F → preservesIncidentEdges G T v := by
  intro v hv w hvw
  exact h ⟨hvw, Or.inl hv⟩

/-- A subgraph containing every ambient edge incident to `v` has the same
degree as the ambient graph at `v`. -/
theorem degree_eq_of_le_of_preservesIncidentEdges [Fintype V]
    (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hTG : T ≤ G) (v : V) (hv : preservesIncidentEdges G T v) :
    T.degree v = G.degree v := by
  apply congrArg Finset.card
  ext w
  simp only [SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => hTG h, fun h => hv h⟩

/-- In a finite graph, equality of degrees in a subgraph forces containment of
every ambient edge incident to that vertex. -/
theorem preservesIncidentEdges_of_le_of_degree_eq [Fintype V]
    (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hTG : T ≤ G) (v : V) (hdegree : T.degree v = G.degree v) :
    preservesIncidentEdges G T v := by
  intro w hGw
  have hsub : T.neighborFinset v ⊆ G.neighborFinset v := by
    intro x hx
    simp only [SimpleGraph.mem_neighborFinset] at hx ⊢
    exact hTG hx
  have hfin : T.neighborFinset v = G.neighborFinset v :=
    Finset.eq_of_subset_of_card_le hsub
      (by simpa only [SimpleGraph.degree] using hdegree.symm.le)
  simpa only [← SimpleGraph.mem_neighborFinset, ← hfin] using hGw

/-- If every vertex of `F` preserves all incident `G`-edges in `T`, then the
forced-edge graph of `F` is a subgraph of `T`. -/
theorem forcedEdgeGraph_le_of_preserves {G T : SimpleGraph V} {F : Set V}
    (hF : ∀ ⦃v : V⦄, v ∈ F → preservesIncidentEdges G T v) :
    forcedEdgeGraph G F ≤ T := by
  intro v w h
  rcases h with ⟨hG, hv | hw⟩
  · exact hF hv hG
  · exact T.symm (hF hw (G.symm hG))

/-- Main forced-edge lemma: if `T` is acyclic, then any forced-edge graph
coming from vertices that preserve all incident `G`-edges in `T` is acyclic. -/
theorem forcedEdgeGraph_isAcyclic_of_preserves {G T : SimpleGraph V} {F : Set V}
    (hT : T.IsAcyclic)
    (hF : ∀ ⦃v : V⦄, v ∈ F → preservesIncidentEdges G T v) :
    (forcedEdgeGraph G F).IsAcyclic := by
  exact SimpleGraph.IsAcyclic.anti (forcedEdgeGraph_le_of_preserves hF) hT

/-- Tree-specialized corollary of `forcedEdgeGraph_isAcyclic_of_preserves`. -/
theorem forcedEdgeGraph_isAcyclic_of_preserves_tree {G T : SimpleGraph V} {F : Set V}
    (hT : T.IsTree)
    (hF : ∀ ⦃v : V⦄, v ∈ F → preservesIncidentEdges G T v) :
    (forcedEdgeGraph G F).IsAcyclic := by
  exact forcedEdgeGraph_isAcyclic_of_preserves hT.IsAcyclic hF

/-- Grid-graph specialization: any set of full-degree/preserved grid vertices
in an acyclic graph forces an acyclic subgraph of the grid. -/
theorem grid_forcedEdgeGraph_isAcyclic_of_preserves {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} {F : Set (GridVertex m n)}
    (hT : T.IsAcyclic)
    (hF : ∀ ⦃v : GridVertex m n⦄, v ∈ F → preservesIncidentEdges (gridGraph m n) T v) :
    (forcedEdgeGraph (gridGraph m n) F).IsAcyclic := by
  exact forcedEdgeGraph_isAcyclic_of_preserves hT hF

/-- An acyclic forced-edge graph in a finite connected graph extends to a tree
that preserves all incident edges at the forced vertices. -/
theorem exists_isTree_preserving_of_forcedEdgeGraph_isAcyclic
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {F : Set V} (hG : G.Connected) (hforced : (forcedEdgeGraph G F).IsAcyclic) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧
      ∀ ⦃v : V⦄, v ∈ F → preservesIncidentEdges G T v := by
  obtain ⟨T, hforced_le, hT_le, hT_tree⟩ :=
    SimpleGraph.isAcyclic_extends_to_isTree (forcedEdgeGraph_le G F) hforced hG
  exact ⟨T, hT_le, hT_tree,
    preservesIncidentEdges_of_forcedEdgeGraph_le hforced_le⟩

end GridGraphs
