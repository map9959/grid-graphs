import GridGraphs.Core.Forced
import GridGraphs.Accounting.ForestLedger

/-!
# Forest ledgers for forced edges

An acyclic forced-edge graph is a forest both on the ambient vertex type and,
after restriction to the forced vertices, on the induced graph of those
vertices.
-/

namespace GridGraphs

open SimpleGraph

variable {V : Type*}

instance forcedEdgeGraph_decidableRel_finset (G : SimpleGraph V) (F : Finset V)
    [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel (forcedEdgeGraph G (↑F : Set V)).Adj := by
  intro v w
  change Decidable (G.Adj v w ∧ (v ∈ F ∨ w ∈ F))
  infer_instance

/-- On the forced vertices, the forced-edge graph and the ambient graph induce
the same graph. -/
theorem forcedEdgeGraph_induce_finset (G : SimpleGraph V) (F : Finset V) :
    (forcedEdgeGraph G (↑F : Set V)).induce (↑F : Set V) =
      G.induce (↑F : Set V) := by
  ext v w
  change (G.Adj v.1 w.1 ∧ (v.1 ∈ F ∨ w.1 ∈ F)) ↔ G.Adj v.1 w.1
  exact and_iff_left (Or.inl v.property)

/-- Acyclicity of the forced-edge graph implies acyclicity of the graph induced
by the forced vertices. -/
theorem induce_finset_isAcyclic_of_forcedEdgeGraph_isAcyclic
    (G : SimpleGraph V) (F : Finset V)
    (hH : (forcedEdgeGraph G (↑F : Set V)).IsAcyclic) :
    (G.induce (↑F : Set V)).IsAcyclic := by
  rw [← forcedEdgeGraph_induce_finset G F]
  exact hH.induce (↑F : Set V)

/-- Additive edge/component ledger for an acyclic forced-edge graph on the
ambient vertex type. Isolated vertices outside `F` are included. -/
theorem forcedEdgeGraph_forest_ledger (G : SimpleGraph V) (F : Finset V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hH : (forcedEdgeGraph G (↑F : Set V)).IsAcyclic) :
    (forcedEdgeGraph G (↑F : Set V)).edgeFinset.card +
        Fintype.card (forcedEdgeGraph G (↑F : Set V)).ConnectedComponent =
      Fintype.card V := by
  exact hH.card_edgeFinset_add_card_connectedComponent

/-- Additive edge/component ledger for the graph induced by the forced
vertices. In particular, when `F` is empty all three terms are zero. -/
theorem induce_finset_forest_ledger (G : SimpleGraph V) (F : Finset V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hH : (forcedEdgeGraph G (↑F : Set V)).IsAcyclic) :
    (G.induce (↑F : Set V)).edgeFinset.card +
        Fintype.card (G.induce (↑F : Set V)).ConnectedComponent =
      F.card := by
  have hInduced := induce_finset_isAcyclic_of_forcedEdgeGraph_isAcyclic G F hH
  simpa using hInduced.card_edgeFinset_add_card_connectedComponent

/-- The ambient forced-forest ledger for an `m` by `n` grid has `m * n`
vertices on its right-hand side. -/
theorem grid_forcedEdgeGraph_forest_ledger (m n : Nat)
    (F : Finset (GridVertex m n))
    (hH : (forcedEdgeGraph (gridGraph m n) (↑F : Set (GridVertex m n))).IsAcyclic) :
    (forcedEdgeGraph (gridGraph m n) (↑F : Set (GridVertex m n))).edgeFinset.card +
        Fintype.card
          (forcedEdgeGraph (gridGraph m n) (↑F : Set (GridVertex m n))).ConnectedComponent =
      m * n := by
  simpa [GridVertex] using forcedEdgeGraph_forest_ledger (gridGraph m n) F hH

end GridGraphs
