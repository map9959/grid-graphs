import GridGraphs.RootedTreeShore
import GridGraphs.Spanning
import GridGraphs.RetainedSupportEdgePassThrough

/-!
# Alternating displacement through a tree edge

This module isolates the basis exchange justified by a residual internal tree
edge.  A continuation edge is a cotree port of that edge's fundamental shore,
equivalently its fundamental tree path contains the displaced edge.

Transition edges are evidence for a continuation.  They are not declared to be
matching resources, and this file makes no Hall assertion.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

namespace GridDirectionalDart

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

/-- Delete a tree edge and insert a coordinate edge. -/
noncomputable def basisExchange (d : GridDirectionalDart T) (e : GridEdge m n) :
    SimpleGraph (GridVertex m n) :=
  T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n))) ⊔
    SimpleGraph.edge e.primalEndpoints.1 e.primalEndpoints.2

/-- Feasibility data for displacement through `d`.  Membership in
`cotreePorts` simultaneously records that `e` is omitted from `T` and crosses
the fundamental cut of `d`. -/
structure BasisExchangeFeasible (d : GridDirectionalDart T) (e : GridEdge m n) : Prop where
  cotreePort : e ∈ d.cotreePorts

namespace BasisExchangeFeasible

variable {d : GridDirectionalDart T} {e : GridEdge m n}

theorem not_tree_adj (h : BasisExchangeFeasible d e) :
    ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2 :=
  (mem_cotreePorts d e).mp h.cotreePort |>.2

theorem crosses (h : BasisExchangeFeasible d e) :
    e.Crosses d.targetShoreVertices :=
  (mem_cotreePorts d e).mp h.cotreePort |>.1

/-- Fundamental-path form of feasibility, reusing the unique-path API from
`RootedTreeShore`. -/
theorem treeEdge_mem_fundamentalPath (h : BasisExchangeFeasible d e)
    (htree : T.IsTree)
    (p : T.Walk e.primalEndpoints.1 e.primalEndpoints.2) (hp : p.IsPath) :
    d.edgeSym2 ∈ p.edges :=
  (mem_cotreePorts_iff_mem_path_edges htree d e h.not_tree_adj p hp).mp h.cotreePort

/-- With cotree membership stated separately, feasibility is exactly occurrence
of the displaced edge on the fundamental tree path. -/
theorem iff_treeEdge_mem_fundamentalPath (htree : T.IsTree)
    (he : ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2)
    (p : T.Walk e.primalEndpoints.1 e.primalEndpoints.2) (hp : p.IsPath) :
    BasisExchangeFeasible d e ↔ d.edgeSym2 ∈ p.edges := by
  constructor
  · intro h
    exact (mem_cotreePorts_iff_mem_path_edges htree d e he p hp).mp h.cotreePort
  · intro h
    exact ⟨(mem_cotreePorts_iff_mem_path_edges htree d e he p hp).mpr h⟩

private theorem endpoints_ne (e : GridEdge m n) :
    e.primalEndpoints.1 ≠ e.primalEndpoints.2 := by
  cases e with
  | horizontal e =>
      intro h
      have hval := congrArg (fun v : GridVertex m n => v.2.val) h
      simp [GridEdge.primalEndpoints, horizontalPrimalEndpoints] at hval
  | vertical e =>
      intro h
      have hval := congrArg (fun v : GridVertex m n => v.1.val) h
      simp [GridEdge.primalEndpoints, verticalPrimalEndpoints] at hval

omit [DecidableRel T.Adj] in
private theorem deleted_le_exchange (d : GridDirectionalDart T) (e : GridEdge m n) :
    T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n))) ≤ d.basisExchange e :=
  le_sup_left

omit [DecidableRel T.Adj] in
private theorem inserted_adj (d : GridDirectionalDart T) (e : GridEdge m n) :
    (d.basisExchange e).Adj e.primalEndpoints.1 e.primalEndpoints.2 := by
  rw [basisExchange, SimpleGraph.sup_adj]
  right
  rw [SimpleGraph.edge_adj]
  exact ⟨Or.inl ⟨rfl, rfl⟩, endpoints_ne e⟩

/-- A feasible one-edge basis exchange is again a tree. -/
theorem isTree (h : BasisExchangeFeasible d e) (htree : T.IsTree) :
    (d.basisExchange e).IsTree := by
  classical
  have hsource (v : GridVertex m n) (hv : v ∉ d.targetShoreVertices) :
      (d.basisExchange e).Reachable d.source v :=
    ((not_mem_targetShoreVertices_iff_reachable_source htree d v).mp hv).mono
      (deleted_le_exchange d e)
  have htarget (v : GridVertex m n) (hv : v ∈ d.targetShoreVertices) :
      (d.basisExchange e).Reachable d.target v :=
    ((mem_targetShoreVertices d v).mp hv).mono (deleted_le_exchange d e)
  have hsourceTarget : (d.basisExchange e).Reachable d.source d.target := by
    rcases h.crosses with huv | hvu
    · exact (hsource e.primalEndpoints.2 huv.2).trans
        ((inserted_adj d e).symm.reachable.trans
          (htarget e.primalEndpoints.1 huv.1).symm)
    · exact (hsource e.primalEndpoints.1 hvu.2).trans
        ((inserted_adj d e).reachable.trans
          (htarget e.primalEndpoints.2 hvu.1).symm)
  have hconnected : (d.basisExchange e).Connected :=
    (connected_iff_exists_forall_reachable (d.basisExchange e)).2 ⟨d.source, fun v => by
      rcases mem_targetShoreVertices_or_reachable_source htree d v with hv | hv
      · exact hsourceTarget.trans (htarget v hv)
      · exact hv.mono (deleted_le_exchange d e)⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconnected, ?_⟩
  have hedgeMem : d.edgeSym2 ∈ T.edgeSet := by
    change T.Adj d.source d.target
    exact d.adj
  have heNotMem : e.primalSym2 ∉ T.edgeSet := by
    simpa [GridEdge.primalSym2, SimpleGraph.mem_edgeSet] using h.not_tree_adj
  have hexchangeEdges : (d.basisExchange e).edgeSet =
      (T.edgeSet \ {d.edgeSym2}) ∪ {e.primalSym2} := by
    rw [basisExchange, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges,
      SimpleGraph.edge_edgeSet_of_ne (endpoints_ne e)]
    rfl
  have hdisjoint : Disjoint (T.edgeSet \ {d.edgeSym2}) ({e.primalSym2} : Set _) := by
    rw [Set.disjoint_singleton_right]
    exact fun he => heNotMem he.1
  have htreeCard : T.edgeSet.ncard + 1 = Nat.card (GridVertex m n) :=
    (SimpleGraph.isTree_iff_connected_and_card.mp htree).2
  rw [Nat.card_coe_set_eq, hexchangeEdges,
    Set.ncard_union_eq hdisjoint, Set.ncard_singleton,
    Set.ncard_diff_singleton_add_one hedgeMem]
  exact htreeCard

/-- If the inserted edge belongs to the ambient graph, basis exchange preserves
the spanning-subtree property. -/
theorem isSpanningSubtree (h : BasisExchangeFeasible d e)
    {G : SimpleGraph (GridVertex m n)} (hT : IsSpanningSubtree G T)
    (heG : G.Adj e.primalEndpoints.1 e.primalEndpoints.2) :
    IsSpanningSubtree G (d.basisExchange e) := by
  refine ⟨?_, h.isTree hT.isTree⟩
  intro u v huv
  rw [basisExchange, SimpleGraph.sup_adj] at huv
  rcases huv with huv | huv
  · exact hT.le (T.deleteEdges_le _ huv)
  · rw [SimpleGraph.edge_adj] at huv
    rcases huv.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact heG
    · exact heG.symm

/-- Grid-specialized basis exchange: every feasible cotree continuation of a
grid spanning tree produces another grid spanning tree. -/
theorem isGridSpanningSubtree (h : BasisExchangeFeasible d e)
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    IsSpanningSubtree (gridGraph m n) (d.basisExchange e) := by
  apply h.isSpanningSubtree hT
  cases e <;> simp [GridEdge.primalEndpoints,
    horizontalPrimalEndpoints_adj, verticalPrimalEndpoints_adj]

end BasisExchangeFeasible

/-! ## Provenance-preserving exchange -/

/-- A feasible tree-basis exchange together with the dual face from which its
labelled cotree edge was entered.  The origin is occurrence provenance; neither
it nor the displaced tree edge is declared to be a resource. -/
structure AlternatingTreeExchange (Origin : Type*)
    (d : GridDirectionalDart T) (e : GridEdge m n) where
  origin : Origin
  enteredFace : GridFace m n
  entered_incident : enteredFace = e.dualEndpoints.1 ∨
    enteredFace = e.dualEndpoints.2
  feasible : BasisExchangeFeasible d e

namespace AlternatingTreeExchange

variable {Origin : Type*} {d : GridDirectionalDart T} {e : GridEdge m n}

/-- The continuation face after inserting the labelled cotree edge. -/
def oppositeFace (exchange : AlternatingTreeExchange Origin d e) : GridFace m n :=
  e.oppositeFace exchange.enteredFace

/-- The inserted cotree edge is incident with the entered and continuation
faces in the exact ordered-dual-endpoint API. -/
theorem hasDualEndpoints (exchange : AlternatingTreeExchange Origin d e) :
    HasDualEndpoints e.dualEndpoints exchange.enteredFace exchange.oppositeFace :=
  GridEdge.hasDualEndpoints_entered_oppositeFace e exchange.enteredFace
    exchange.entered_incident

/-- Exchange feasibility preserves the tree property. -/
theorem isTree (exchange : AlternatingTreeExchange Origin d e)
    (hT : T.IsTree) :
    (d.basisExchange e).IsTree :=
  exchange.feasible.isTree hT

/-- Grid-specialized tree preservation for an alternating exchange. -/
theorem isGridSpanningSubtree (exchange : AlternatingTreeExchange Origin d e)
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    IsSpanningSubtree (gridGraph m n) (d.basisExchange e) :=
  exchange.feasible.isGridSpanningSubtree hT

end AlternatingTreeExchange

/-! ## Occurrence-preserving continuation -/

/-- A one-step continuation vertex is either the residual tree edge being
displaced or the cotree edge that continues through it. -/
abbrev TreeExchangeVertex := GridDirectionalDart T ⊕ GridEdge m n

/-- Base continuation relation.  `ResidualInternal` is supplied by the caller,
so the graph-theoretic layer does not manufacture an internal-resource claim. -/
inductive ResidualTreeEdgeContinuation (ResidualInternal : GridDirectionalDart T → Prop) :
    TreeExchangeVertex (T := T) → TreeExchangeVertex (T := T) → Prop
  | throughInternal (d : GridDirectionalDart T) (e : GridEdge m n)
      (hinternal : ResidualInternal d) (hfeasible : BasisExchangeFeasible d e) :
      ResidualTreeEdgeContinuation ResidualInternal (.inl d) (.inr e)

/-- An occurrence label remains attached to every continuation vertex. -/
structure OccurrenceTreeExchangeState (Occurrence : Type*) where
  origin : Occurrence
  vertex : TreeExchangeVertex (T := T)

/-- Lift continuation without merging equal graph edges reached from distinct
occurrences. -/
def OccurrenceResidualTreeEdgeContinuation {Occurrence : Type*}
    (ResidualInternal : GridDirectionalDart T → Prop)
    (x y : OccurrenceTreeExchangeState (T := T) Occurrence) : Prop :=
  x.origin = y.origin ∧ ResidualTreeEdgeContinuation ResidualInternal x.vertex y.vertex

theorem occurrence_origin_eq {Occurrence : Type*}
    {ResidualInternal : GridDirectionalDart T → Prop}
    {x y : OccurrenceTreeExchangeState (T := T) Occurrence}
    (hxy : Relation.ReflTransGen
      (OccurrenceResidualTreeEdgeContinuation ResidualInternal) x y) :
    y.origin = x.origin := by
  induction hxy with
  | refl => rfl
  | tail _ hstep ih => exact hstep.1.symm.trans ih

/-- Every actual continuation step carries exactly the feasibility needed for
its associated basis exchange. -/
theorem spanningTree_of_continuation
    {ResidualInternal : GridDirectionalDart T → Prop}
    {d : GridDirectionalDart T} {e : GridEdge m n}
    (hstep : ResidualTreeEdgeContinuation ResidualInternal (.inl d) (.inr e))
    {G : SimpleGraph (GridVertex m n)} (hT : IsSpanningSubtree G T)
    (heG : G.Adj e.primalEndpoints.1 e.primalEndpoints.2) :
    IsSpanningSubtree G (d.basisExchange e) := by
  cases hstep with
  | throughInternal _ _ _ hfeasible => exact hfeasible.isSpanningSubtree hT heG

end GridDirectionalDart

end GridGraphs
