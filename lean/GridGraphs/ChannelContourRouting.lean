import GridGraphs.PlaneChannelForest
import GridGraphs.NoncrossingShoreChannels
import GridGraphs.MaxPreserved

/-!
# Channel forests routed into the primal contour ledger

This file is the generic bridge between an already-realized plane channel
forest and the exact primal contour resource.  The three geometric realization
maps remain explicit: exits use boundary sectors, merger slots use internal
tree edges, and roots use full components of the unsupported induced graph.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace PlaneChannelForest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Realize the abstract channel-forest resource in the corresponding three
summands of the primal contour resource. -/
def contourResourceEmbedding {n : Nat}
    (C : PlaneChannelForest V)
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj]
    (U : Finset (GridVertex n n))
    (exitEmbedding : (↥C.exits) ↪ BoundarySector U)
    (mergerEmbedding : C.forest.MergerSlot ↪ ↥(internalEdgeFinset T U))
    (rootEmbedding : (↥C.forest.roots) ↪
      ((gridGraph n n).induce
        (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
          Set (GridVertex n n))).ConnectedComponent) :
    C.Resource ↪ PrimalContourResource T U where
  toFun
    | Sum.inl exit => Sum.inl (exitEmbedding exit)
    | Sum.inr (Sum.inl merger) => Sum.inr (Sum.inl (mergerEmbedding merger))
    | Sum.inr (Sum.inr root) => Sum.inr (Sum.inr (rootEmbedding root))
  inj' := by
    intro a b h
    rcases a with exit | mergerOrRoot
    · rcases b with exit' | mergerOrRoot'
      · congr 1
        exact exitEmbedding.injective (Sum.inl.inj h)
      · cases mergerOrRoot' <;> simp at h
    · rcases mergerOrRoot with merger | root
      · rcases b with exit' | mergerOrRoot'
        · simp at h
        · rcases mergerOrRoot' with merger' | root'
          · congr 2
            exact mergerEmbedding.injective (Sum.inl.inj (Sum.inr.inj h))
          · exact (Sum.inl_ne_inr (Sum.inr.inj h)).elim
      · rcases b with exit' | mergerOrRoot'
        · simp at h
        · rcases mergerOrRoot' with merger' | root'
          · exact (Sum.inr_ne_inl (Sum.inr.inj h)).elim
          · congr 2
            exact rootEmbedding.injective (Sum.inr.inj (Sum.inr.inj h))

/-- A canonical shore demand embeds in the exact contour ledger once the
channel demands and each of the three kinds of geometric terminal have been
realized.  In particular, no embedding into the final resource is assumed. -/
noncomputable def canonicalShoreDemandContourEmbedding {n : Nat}
    (axis : ShoreSweepAxis) (C : PlaneChannelForest V)
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj]
    (U : Finset (GridVertex n n))
    (demandEmbedding : CanonicalShoreDemand axis n ↪ ↥C.demand)
    (exitEmbedding : (↥C.exits) ↪ BoundarySector U)
    (mergerEmbedding : C.forest.MergerSlot ↪ ↥(internalEdgeFinset T U))
    (rootEmbedding : (↥C.forest.roots) ↪
      ((gridGraph n n).induce
        (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
          Set (GridVertex n n))).ConnectedComponent) :
    CanonicalShoreDemand axis n ↪ PrimalContourResource T U :=
  demandEmbedding.trans <| (C.demandEmbedding.trans <|
    C.contourResourceEmbedding T U exitEmbedding mergerEmbedding rootEmbedding)

/-- Generic channel-to-contour bound.  All geometric content is confined to
the four typed embeddings; the conclusion then follows from forest pruning and
the exact contour ledger. -/
theorem incidenceWaste_ge_of_channelContourRouting {n : Nat} (hn : 2 ≤ n)
    (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (C : PlaneChannelForest V)
    (demandEmbedding : CanonicalShoreDemand axis n ↪ ↥C.demand)
    (exitEmbedding : (↥C.exits) ↪
      BoundarySector (supportFinset (gridGraph n n \ T)))
    (mergerEmbedding : C.forest.MergerSlot ↪
      ↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T))))
    (rootEmbedding : (↥C.forest.roots) ↪
      ((gridGraph n n).induce
        (↑((Finset.univ : Finset (GridVertex n n)) \
          supportFinset (gridGraph n n \ T)) :
          Set (GridVertex n n))).ConnectedComponent) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) := by
  let U := supportFinset (gridGraph n n \ T)
  let routed : CanonicalShoreDemand axis n ↪ PrimalContourResource T U :=
    C.canonicalShoreDemandContourEmbedding axis T U demandEmbedding
      exitEmbedding mergerEmbedding rootEmbedding
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

/-- A realized channel routing gives the sharp preservation envelope for its
spanning subtree. -/
theorem preserved_upper_of_channelContourRouting {n : Nat} (hn : 2 ≤ n)
    (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (C : PlaneChannelForest V)
    (demandEmbedding : CanonicalShoreDemand axis n ↪ ↥C.demand)
    (exitEmbedding : (↥C.exits) ↪
      BoundarySector (supportFinset (gridGraph n n \ T)))
    (mergerEmbedding : C.forest.MergerSlot ↪
      ↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T))))
    (rootEmbedding : (↥C.forest.roots) ↪
      ((gridGraph n n).induce
        (↑((Finset.univ : Finset (GridVertex n n)) \
          supportFinset (gridGraph n n \ T)) :
          Set (GridVertex n n))).ConnectedComponent) :
    3 * numPreserved n n T + 4 ≤ n * n + 3 * n := by
  apply (diagonal_cotree_incidenceWaste_ge_iff_preserved_bound hn hT).mp
  exact incidenceWaste_ge_of_channelContourRouting hn axis hT C
    demandEmbedding exitEmbedding mergerEmbedding rootEmbedding

/-- If the supplied realized spanning subtree is a maximizer, channel routing
gives the sharp absolute upper envelope for `maxPreserved`. -/
theorem maxPreserved_upper_of_channelContourRouting {n : Nat} (hn : 2 ≤ n)
    (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (hmax : numPreserved n n T = maxPreserved n n)
    (C : PlaneChannelForest V)
    (demandEmbedding : CanonicalShoreDemand axis n ↪ ↥C.demand)
    (exitEmbedding : (↥C.exits) ↪
      BoundarySector (supportFinset (gridGraph n n \ T)))
    (mergerEmbedding : C.forest.MergerSlot ↪
      ↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T))))
    (rootEmbedding : (↥C.forest.roots) ↪
      ((gridGraph n n).induce
        (↑((Finset.univ : Finset (GridVertex n n)) \
          supportFinset (gridGraph n n \ T)) :
          Set (GridVertex n n))).ConnectedComponent) :
    3 * maxPreserved n n + 4 ≤ n * n + 3 * n := by
  rw [← hmax]
  exact preserved_upper_of_channelContourRouting hn axis hT C
    demandEmbedding exitEmbedding mergerEmbedding rootEmbedding

/-- Residue-zero closed upper bound obtained from a realized maximizer. -/
theorem maxPreserved_three_mul_le_of_channelContourRouting
    (k : Nat) (hk : 1 ≤ k) (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex (3 * k) (3 * k))} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k) (3 * k)) T)
    (hmax : numPreserved (3 * k) (3 * k) T =
      maxPreserved (3 * k) (3 * k))
    (C : PlaneChannelForest V)
    (demandEmbedding : CanonicalShoreDemand axis (3 * k) ↪ ↥C.demand)
    (exitEmbedding : (↥C.exits) ↪
      BoundarySector (supportFinset (gridGraph (3 * k) (3 * k) \ T)))
    (mergerEmbedding : C.forest.MergerSlot ↪
      ↥(internalEdgeFinset T
        (supportFinset (gridGraph (3 * k) (3 * k) \ T))))
    (rootEmbedding : (↥C.forest.roots) ↪
      ((gridGraph (3 * k) (3 * k)).induce
        (↑((Finset.univ : Finset (GridVertex (3 * k) (3 * k))) \
          supportFinset (gridGraph (3 * k) (3 * k) \ T)) :
          Set (GridVertex (3 * k) (3 * k)))).ConnectedComponent) :
    maxPreserved (3 * k) (3 * k) ≤ 3 * k ^ 2 + 3 * k - 2 := by
  have h := maxPreserved_upper_of_channelContourRouting (by omega) axis hT
    hmax C demandEmbedding exitEmbedding mergerEmbedding rootEmbedding
  have hsquare : (3 * k) * (3 * k) + 3 * (3 * k) =
      9 * k ^ 2 + 9 * k := by ring
  rw [hsquare] at h
  omega

/-- Residue-one closed upper bound obtained from a realized maximizer. -/
theorem maxPreserved_three_mul_add_one_le_of_channelContourRouting
    (k : Nat) (hk : 1 ≤ k) (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex (3 * k + 1) (3 * k + 1))}
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 1) (3 * k + 1)) T)
    (hmax : numPreserved (3 * k + 1) (3 * k + 1) T =
      maxPreserved (3 * k + 1) (3 * k + 1))
    (C : PlaneChannelForest V)
    (demandEmbedding : CanonicalShoreDemand axis (3 * k + 1) ↪ ↥C.demand)
    (exitEmbedding : (↥C.exits) ↪ BoundarySector
      (supportFinset (gridGraph (3 * k + 1) (3 * k + 1) \ T)))
    (mergerEmbedding : C.forest.MergerSlot ↪
      ↥(internalEdgeFinset T
        (supportFinset (gridGraph (3 * k + 1) (3 * k + 1) \ T))))
    (rootEmbedding : (↥C.forest.roots) ↪
      ((gridGraph (3 * k + 1) (3 * k + 1)).induce
        (↑((Finset.univ :
            Finset (GridVertex (3 * k + 1) (3 * k + 1))) \
          supportFinset (gridGraph (3 * k + 1) (3 * k + 1) \ T)) :
          Set (GridVertex (3 * k + 1) (3 * k + 1)))).ConnectedComponent) :
    maxPreserved (3 * k + 1) (3 * k + 1) ≤ 3 * k ^ 2 + 5 * k := by
  have h := maxPreserved_upper_of_channelContourRouting (by omega) axis hT
    hmax C demandEmbedding exitEmbedding mergerEmbedding rootEmbedding
  have hsquare :
      (3 * k + 1) * (3 * k + 1) + 3 * (3 * k + 1) =
        9 * k ^ 2 + 15 * k + 4 := by ring
  rw [hsquare] at h
  omega

/-- The basic channel bound gives the coarse residue-two upper bound, two
above the expected closed form. -/
theorem maxPreserved_three_mul_add_two_le_of_channelContourRouting
    (k : Nat) (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2))}
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (hmax : numPreserved (3 * k + 2) (3 * k + 2) T =
      maxPreserved (3 * k + 2) (3 * k + 2))
    (C : PlaneChannelForest V)
    (demandEmbedding : CanonicalShoreDemand axis (3 * k + 2) ↪ ↥C.demand)
    (exitEmbedding : (↥C.exits) ↪ BoundarySector
      (supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T)))
    (mergerEmbedding : C.forest.MergerSlot ↪
      ↥(internalEdgeFinset T
        (supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T))))
    (rootEmbedding : (↥C.forest.roots) ↪
      ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑((Finset.univ :
            Finset (GridVertex (3 * k + 2) (3 * k + 2))) \
          supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T)) :
          Set (GridVertex (3 * k + 2) (3 * k + 2)))).ConnectedComponent) :
    maxPreserved (3 * k + 2) (3 * k + 2) ≤ 3 * k ^ 2 + 7 * k + 2 := by
  have h := maxPreserved_upper_of_channelContourRouting (by omega) axis hT
    hmax C demandEmbedding exitEmbedding mergerEmbedding rootEmbedding
  have hsquare :
      (3 * k + 2) * (3 * k + 2) + 3 * (3 * k + 2) =
        9 * k ^ 2 + 21 * k + 10 := by ring
  rw [hsquare] at h
  omega

end PlaneChannelForest

end GridGraphs
