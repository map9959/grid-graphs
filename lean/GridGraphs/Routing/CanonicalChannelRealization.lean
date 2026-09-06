import GridGraphs.Routing.CanonicalShoreForest
import GridGraphs.Routing.GridChannelContourRealization
import GridGraphs.Routing.TerminalCarrierQuotientRouting

/-!
# Conditional canonical channel realization

This module records what follows if the current canonical forest, whose exit
set is empty, has enough internal-edge and preserved-component resources.  That
condition is intentionally not asserted universally: later supported boundary
exits must be retained before an unconditional realization can be constructed.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace GridDirectionalDart

def canonicalShoreRoot {n : Nat} (hn : 3 ≤ n) : GridVertex n n :=
  (⟨0, by omega⟩, ⟨0, by omega⟩)

noncomputable def canonicalShoreExitEmbedding {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    (↥(CanonicalShoreDemand.directExits axis hn2 T) ⊕
      ↥(canonicalShorePlaneChannelForest axis hn2 hn3 hT
        (canonicalShoreRoot hn3)).exits) ↪ GridCotreeOuterPort T where
  toFun
    | .inl q => CanonicalShoreDemand.directExitEmbedding axis hn2 T q
    | .inr e => False.elim (by
        have he : e.1 ∈ (∅ : Finset _) := e.2
        exact (Finset.notMem_empty _ he).elim)
  inj' := by
    intro a b
    rcases a with a | a <;> rcases b with b | b
    · intro hab
      exact congrArg Sum.inl
        ((CanonicalShoreDemand.directExitEmbedding axis hn2 T).injective hab)
    · exact False.elim (by
        have hb : b.1 ∈ (∅ : Finset _) := b.2
        exact (Finset.notMem_empty _ hb).elim)
    · exact False.elim (by
        have ha : a.1 ∈ (∅ : Finset _) := a.2
        exact (Finset.notMem_empty _ ha).elim)
    · exact False.elim (by
        have ha : a.1 ∈ (∅ : Finset _) := a.2
        exact (Finset.notMem_empty _ ha).elim)

/-- The global resource condition for the exit-free canonical prototype.
Unlike edgewise terminal injectivity, this permits terminals in the same
preserved component when unused internal tree edges compensate for them.  It is
not universal because the prototype discards supported exits met after launch. -/
def CanonicalTerminalResources {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) : Prop :=
  Nonempty ((canonicalShorePlaneChannelForest axis hn2 hn3 hT
      (canonicalShoreRoot hn3)).forest.MergerSlot ⊕
        ↥((canonicalShorePlaneChannelForest axis hn2 hn3 hT
          (canonicalShoreRoot hn3)).forest.roots \
            (canonicalShorePlaneChannelForest axis hn2 hn3 hT
              (canonicalShoreRoot hn3)).exits) ↪
    (↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T))) ⊕
      ((gridGraph n n).induce
        (↑((Finset.univ : Finset (GridVertex n n)) \
          supportFinset (gridGraph n n \ T)) : Set (GridVertex n n))).ConnectedComponent))

/-- The exact unresolved routing condition for the canonical combined physical
terminal token. All internal tokens and one token per noninternal carrier class
are already canonically reserved; this asks only for routing the remaining
carrier collisions outside both reserved ranges. -/
def CanonicalTerminalCollisionRouting {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) : Prop :=
  Nonempty (PhysicalTreeTokenQuotientRouting
    (supportFinset (gridGraph n n \ T))
    (canonicalShoreTerminalTreeEdgeEmbedding axis hn2 hn3 hT
      (canonicalShoreRoot hn3)))

/-- The exact residual collision routing produces the full canonical terminal
resource embedding. -/
noncomputable def canonicalTerminalResourceEmbeddingOfCollisionRouting
    {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (hrouting : CanonicalTerminalCollisionRouting axis hn2 hn3 hT) :
    ((canonicalShorePlaneChannelForest axis hn2 hn3 hT
        (canonicalShoreRoot hn3)).forest.MergerSlot ⊕
      ↥((canonicalShorePlaneChannelForest axis hn2 hn3 hT
        (canonicalShoreRoot hn3)).forest.roots \
          (canonicalShorePlaneChannelForest axis hn2 hn3 hT
            (canonicalShoreRoot hn3)).exits)) ↪
      (↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T))) ⊕
        ((gridGraph n n).induce
          (↑((Finset.univ : Finset (GridVertex n n)) \
            supportFinset (gridGraph n n \ T)) :
              Set (GridVertex n n))).ConnectedComponent) := by
  classical
  simpa [canonicalShorePlaneChannelForest] using
    (Classical.choice hrouting).resourceEmbedding

theorem canonicalTerminalResources_of_collisionRouting
    {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (hrouting : CanonicalTerminalCollisionRouting axis hn2 hn3 hT) :
    CanonicalTerminalResources axis hn2 hn3 hT :=
  ⟨canonicalTerminalResourceEmbeddingOfCollisionRouting
    axis hn2 hn3 hT hrouting⟩

theorem canonicalTerminalResources_iff_card_le {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    CanonicalTerminalResources axis hn2 hn3 hT ↔
      Fintype.card
          ((canonicalShorePlaneChannelForest axis hn2 hn3 hT
            (canonicalShoreRoot hn3)).forest.MergerSlot ⊕
            ↥((canonicalShorePlaneChannelForest axis hn2 hn3 hT
              (canonicalShoreRoot hn3)).forest.roots \
                (canonicalShorePlaneChannelForest axis hn2 hn3 hT
                  (canonicalShoreRoot hn3)).exits)) ≤
        (internalEdgeFinset T (supportFinset (gridGraph n n \ T))).card +
          Fintype.card
            ((gridGraph n n).induce
              (↑((Finset.univ : Finset (GridVertex n n)) \
                supportFinset (gridGraph n n \ T)) :
                  Set (GridVertex n n))).ConnectedComponent := by
  rw [CanonicalTerminalResources,
    Function.Embedding.nonempty_iff_card_le]
  simp only [Fintype.card_sum, Fintype.card_coe]

/-- The explicit canonical forest becomes a complete contour realization once
its merger and root occurrences have enough global contour resources. -/
noncomputable def canonicalGridChannelContourRealization {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (hterminal : CanonicalTerminalResources axis hn2 hn3 hT) :
    GridChannelContourRealization hT where
  Carrier := CanonicalShoreCarrier axis hn2 hn3 hT (canonicalShoreRoot hn3)
  axis := axis
  channels := canonicalShorePlaneChannelForest axis hn2 hn3 hT
    (canonicalShoreRoot hn3)
  directExits := CanonicalShoreDemand.directExits axis hn2 T
  continuingEmbedding := canonicalShoreDemandEmbedding axis hn2 hn3 hT
    (canonicalShoreRoot hn3)
  demand_subset_leaves :=
    canonicalShoreDemands_subset_leaves axis hn2 hn3 hT (canonicalShoreRoot hn3)
  exits_subset_roots := by
    intro x hx
    have he : x ∈ (∅ : Finset _) := hx
    exact (Finset.notMem_empty _ he).elim
  exitEmbedding := canonicalShoreExitEmbedding axis hn2 hn3 hT
  terminalResourceEmbedding := Classical.choice hterminal

/-- Conditional canonical realization from only the residual physical-token
collision routing. No existence of that routing is asserted here. -/
noncomputable def canonicalGridChannelContourRealizationOfCollisionRouting
    {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (hrouting : CanonicalTerminalCollisionRouting axis hn2 hn3 hT) :
    GridChannelContourRealization hT where
  Carrier := CanonicalShoreCarrier axis hn2 hn3 hT (canonicalShoreRoot hn3)
  axis := axis
  channels := canonicalShorePlaneChannelForest axis hn2 hn3 hT
    (canonicalShoreRoot hn3)
  directExits := CanonicalShoreDemand.directExits axis hn2 T
  continuingEmbedding := canonicalShoreDemandEmbedding axis hn2 hn3 hT
    (canonicalShoreRoot hn3)
  demand_subset_leaves :=
    canonicalShoreDemands_subset_leaves axis hn2 hn3 hT (canonicalShoreRoot hn3)
  exits_subset_roots := by simp [canonicalShorePlaneChannelForest]
  exitEmbedding := canonicalShoreExitEmbedding axis hn2 hn3 hT
  terminalResourceEmbedding :=
    canonicalTerminalResourceEmbeddingOfCollisionRouting axis hn2 hn3 hT hrouting

theorem square_grid_tree_universalWaste_of_canonicalTerminalResources
    {n : Nat} (hn3 : 3 ≤ n)
    (hterminal : ∀ {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
      (hT : IsSpanningSubtree (gridGraph n n) T),
        CanonicalTerminalResources .rows (by omega) hn3 hT)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) :=
  (canonicalGridChannelContourRealization .rows (by omega) hn3 hT
    (hterminal hT)).incidenceWaste_ge (by omega)

/-- It is enough to route only the repeated preserved-component contacts of the
canonical physical terminal tokens. All noncolliding terminal resources are
reserved by the quotient factorization. -/
theorem square_grid_tree_universalWaste_of_canonicalCollisionRouting
    {n : Nat} (hn3 : 3 ≤ n)
    (hrouting : ∀ {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
      (hT : IsSpanningSubtree (gridGraph n n) T),
        CanonicalTerminalCollisionRouting .rows (by omega) hn3 hT)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) :=
  (canonicalGridChannelContourRealizationOfCollisionRouting
    .rows (by omega) hn3 hT (hrouting hT)).incidenceWaste_ge (by omega)

end GridDirectionalDart

end GridGraphs
