import GridGraphs.ChannelContourRouting

/-!
# Joint channel-to-contour routing

This file packages the purely finite-resource step in which direct exits and a
pruned channel forest are embedded jointly into the primal contour ledger.
No decomposition of that embedding among the ledger summands is required.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace PlaneChannelForest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A joint realization of direct exits and the pruned forest in the exact
primal contour resource implies the sharp incidence-waste bound. -/
theorem incidenceWaste_ge_of_jointChannelContourRoutingWithDirectExits
    {n : Nat} (hn : 2 ≤ n) (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (C : PlaneChannelForest V)
    (directExits : Finset (CanonicalShoreDemand axis n))
    (continuingEmbedding :
      ↥((Finset.univ : Finset (CanonicalShoreDemand axis n)) \ directExits) ↪
        ↥C.demand)
    (hdemand : C.demand ⊆ C.forest.leaves)
    (hexits : C.exits ⊆ C.forest.roots)
    (jointEmbedding : (↥directExits ⊕ C.PrunedRootResource) ↪
      PrimalContourResource T (supportFinset (gridGraph n n \ T))) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) := by
  let U := supportFinset (gridGraph n n \ T)
  let routed : CanonicalShoreDemand axis n ↪ PrimalContourResource T U :=
    (canonicalShoreDemandPrunedRootEmbeddingWithDirectExits axis C directExits
      continuingEmbedding hdemand hexits).trans jointEmbedding
  have hcard : n + 3 ≤ Fintype.card (PrimalContourResource T U) := by
    rw [← CanonicalShoreDemand.card axis n]
    exact Fintype.card_le_of_injective routed.toFun routed.injective
  have hledger :=
    cotree_incidenceWaste_add_one_eq_card_primalContourResource hn hT
  change incidenceWaste (gridGraph n n \ T) + 1 =
    Fintype.card (PrimalContourResource T U) at hledger
  rw [← hledger] at hcard
  change (n + 2) + 1 ≤ incidenceWaste (gridGraph n n \ T) + 1 at hcard
  exact Nat.le_of_add_le_add_right hcard

end PlaneChannelForest

end GridGraphs
