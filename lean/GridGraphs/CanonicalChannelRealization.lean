import GridGraphs.CanonicalShoreForest
import GridGraphs.GridChannelContourRealization

/-!
# Canonical channel realization endpoint

All canonical channel data are now explicit.  The sole remaining realization
condition is that selected noninternal terminal edges reach distinct preserved
components.
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

/-- The final global resource condition left by the canonical construction.
Unlike edgewise terminal injectivity, this permits terminals in the same
preserved component when unused internal tree edges compensate for them. -/
def CanonicalTerminalResources {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) : Prop :=
  Nonempty ((canonicalShorePlaneChannelForest axis hn2 hn3 hT
      (canonicalShoreRoot hn3)).forest.MergerSlot ⊕
        ↥(canonicalShorePlaneChannelForest axis hn2 hn3 hT
          (canonicalShoreRoot hn3)).forest.roots ↪
    (↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T))) ⊕
      ((gridGraph n n).induce
        (↑((Finset.univ : Finset (GridVertex n n)) \
          supportFinset (gridGraph n n \ T)) : Set (GridVertex n n))).ConnectedComponent))

theorem canonicalTerminalResources_iff_card_le {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    CanonicalTerminalResources axis hn2 hn3 hT ↔
      Fintype.card
          ((canonicalShorePlaneChannelForest axis hn2 hn3 hT
            (canonicalShoreRoot hn3)).forest.MergerSlot ⊕
            ↥(canonicalShorePlaneChannelForest axis hn2 hn3 hT
              (canonicalShoreRoot hn3)).forest.roots) ≤
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
  exitEmbedding := canonicalShoreExitEmbedding axis hn2 hn3 hT
  terminalResourceEmbedding := Classical.choice hterminal

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

end GridDirectionalDart

end GridGraphs
