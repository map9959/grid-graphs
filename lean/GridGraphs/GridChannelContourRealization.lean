import GridGraphs.TreeEdgeMergerResources
import GridGraphs.GridCotreeSplitOuter

/-!
# Realized grid channel contours

This structure is the geometric interface required by the planar waste proof.
It retains actual split-boundary exits, rooted channel mergers, and preserved
component contacts; all embeddings into the numerical contour ledger are
derived from those data.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace GridDirectionalDart

/-- A pruned channel forest whose demands and terminal resources are realized
in a square-grid spanning tree. -/
structure GridChannelContourRealization {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) where
  Carrier : Type
  [carrierFintype : Fintype Carrier]
  [carrierDecidableEq : DecidableEq Carrier]
  axis : ShoreSweepAxis
  channels : PlaneChannelForest Carrier
  directExits : Finset (CanonicalShoreDemand axis n)
  continuingEmbedding :
    ↥((Finset.univ : Finset (CanonicalShoreDemand axis n)) \ directExits) ↪
      ↥channels.demand
  demand_subset_leaves : channels.demand ⊆ channels.forest.leaves
  exits_subset_roots : channels.exits ⊆ channels.forest.roots
  exitEmbedding : (↥directExits ⊕ ↥channels.exits) ↪ GridCotreeOuterPort T
  terminalResourceEmbedding :
    (channels.forest.MergerSlot ⊕
      ↥(channels.forest.roots \ channels.exits)) ↪
      (↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T))) ⊕
        ((gridGraph n n).induce
          (↑((Finset.univ : Finset (GridVertex n n)) \
            supportFinset (gridGraph n n \ T)) : Set (GridVertex n n))).ConnectedComponent)

namespace GridChannelContourRealization

variable {n : Nat}
variable {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
variable {hT : IsSpanningSubtree (gridGraph n n) T}

/-- Every realized channel contour supplies the sharp universal waste bound for
its spanning tree. -/
theorem incidenceWaste_ge (R : GridChannelContourRealization hT)
    (hn : 2 ≤ n) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) := by
  letI := R.carrierFintype
  letI := R.carrierDecidableEq
  apply PlaneChannelForest.incidenceWaste_ge_of_prunedRootChannelRoutingWithDirectExits
    hn R.axis hT R.channels R.directExits R.continuingEmbedding
    R.demand_subset_leaves R.exits_subset_roots
    (R.exitEmbedding.trans
      (gridCotreeOuterPortEquivBoundarySector hn hn hT).toEmbedding)
  exact R.terminalResourceEmbedding

/-- Constructing a realization for every square-grid spanning tree proves the
universal waste bound. -/
theorem square_grid_tree_universalWaste_of_exists_realization
    {n : Nat} (hn : 2 ≤ n)
    (realize : ∀ {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
      (hT : IsSpanningSubtree (gridGraph n n) T),
        Nonempty (GridChannelContourRealization hT))
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) :=
  (realize hT).elim fun R => R.incidenceWaste_ge hn

end GridChannelContourRealization

end GridDirectionalDart

end GridGraphs
