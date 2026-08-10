import GridGraphs.PlaneChannelForest
import GridGraphs.GridShoreChannelForest
import GridGraphs.ChannelCarrierRoots
import GridGraphs.ChannelContourRouting

/-!
# Channel-merger resource factorization

This file separates the geometric input assigning merger slots to concrete
rooted channel mergers from the finite resource injection that it induces.
Slots whose separator edge is internal use that edge.  Every other slot uses
the preserved component supplied by the grid-tree dichotomy.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace GridDirectionalDart

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Whether the separator edge assigned to a merger slot is internal to `U`. -/
def MergerSlotIsInternal (F : ParentForest V) (root : GridVertex m n)
    (U : Finset (GridVertex m n))
    (separator : F.MergerSlot → RootedChannelMerger (T := T) root)
    (s : F.MergerSlot) : Prop :=
  ∀ v ∈ (separator s).1.edgeSym2, v ∈ U

/-- Merger slots whose assigned separator edge is not internal. -/
def NoninternalMergerSlot (F : ParentForest V) (root : GridVertex m n)
    (U : Finset (GridVertex m n))
    (separator : F.MergerSlot → RootedChannelMerger (T := T) root) :=
  {s : F.MergerSlot // ¬MergerSlotIsInternal F root U separator s}

/-- The preserved full-vertex component forced by a noninternal separator.
The definition uses only the current internal-or-preserved dichotomy. -/
noncomputable def noninternalMergerComponent
    (hT : IsSpanningSubtree (gridGraph m n) T) (F : ParentForest V)
    (root : GridVertex m n)
    (separator : F.MergerSlot → RootedChannelMerger (T := T) root)
    (s : NoninternalMergerSlot F root
      (supportFinset (gridGraph m n \ T)) separator) :
    ((gridGraph m n).induce
      (↑((Finset.univ : Finset (GridVertex m n)) \
        supportFinset (gridGraph m n \ T)) : Set (GridVertex m n))).ConnectedComponent := by
  classical
  let U := supportFinset (gridGraph m n \ T)
  have h := rootedChannelMerger_internal_or_preservedComponent hT root (separator s.1)
  dsimp only at h
  have hnotInternal : ¬∃ e : ↥(internalEdgeFinset T U),
      e.1 = (separator s.1).1.edgeSym2 := by
    intro hint
    apply s.2
    intro v hv
    rcases hint with ⟨e, he⟩
    rw [← he] at hv
    exact ((mem_internalEdgeFinset T U e.1).mp e.2).2 v hv
  have hpreserved := h.resolve_left hnotInternal
  let v := Classical.choose hpreserved
  let hvF := Classical.choose (Classical.choose_spec hpreserved)
  exact ((gridGraph m n).induce
    (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
      Set (GridVertex m n))).connectedComponentMk ⟨v, hvF⟩

/-- Injective separator labels and injective noninternal component terminals
factor all merger slots through internal edges or preserved components. -/
noncomputable def mergerSlotResourceEmbedding
    (hT : IsSpanningSubtree (gridGraph m n) T) (F : ParentForest V)
    (root : GridVertex m n)
    (separator : F.MergerSlot → RootedChannelMerger (T := T) root)
    (hseparator : Function.Injective fun s => (separator s).1.edgeSym2)
    (hterminal : Function.Injective
      (noninternalMergerComponent hT F root separator)) :
    F.MergerSlot ↪
      (↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T))) ⊕
        ((gridGraph m n).induce
          (↑((Finset.univ : Finset (GridVertex m n)) \
            supportFinset (gridGraph m n \ T)) :
              Set (GridVertex m n))).ConnectedComponent) where
  toFun s := by
    classical
    let U := supportFinset (gridGraph m n \ T)
    if hs : MergerSlotIsInternal F root U separator s then
      exact Sum.inl ⟨(separator s).1.edgeSym2, by
        rw [mem_internalEdgeFinset]
        exact ⟨(rootedChannelMergerEdgeEmbedding hT.isTree root (separator s)).2, hs⟩⟩
    else
      exact Sum.inr (noninternalMergerComponent hT F root separator ⟨s, hs⟩)
  inj' := by
    classical
    intro a b hab
    let U := supportFinset (gridGraph m n \ T)
    by_cases ha : MergerSlotIsInternal F root U separator a
    · by_cases hb : MergerSlotIsInternal F root U separator b
      · have hedge := congrArg
          (Sum.elim Subtype.val (fun _ => (separator a).1.edgeSym2)) hab
        simp [U, ha, hb] at hedge
        exact hseparator hedge
      · simp [U, ha, hb] at hab
    · by_cases hb : MergerSlotIsInternal F root U separator b
      · simp [U, ha, hb] at hab
      · simp [U, ha, hb] at hab
        exact congrArg Subtype.val (hterminal hab)

/-- Roots may be included in the same resource injection when they already
embed into preserved components and their image is disjoint from every
noninternal merger terminal. -/
noncomputable def mergerSlotSumRootsResourceEmbedding
    (hT : IsSpanningSubtree (gridGraph m n) T) (F : ParentForest V)
    (root : GridVertex m n)
    (separator : F.MergerSlot → RootedChannelMerger (T := T) root)
    (hseparator : Function.Injective fun s => (separator s).1.edgeSym2)
    (hterminal : Function.Injective
      (noninternalMergerComponent hT F root separator))
    (rootComponentEmbedding : ↥F.roots ↪
      ((gridGraph m n).induce
        (↑((Finset.univ : Finset (GridVertex m n)) \
          supportFinset (gridGraph m n \ T)) :
            Set (GridVertex m n))).ConnectedComponent)
    (hdisjoint : ∀ s, ∀ r,
      noninternalMergerComponent hT F root separator s ≠
        rootComponentEmbedding r) :
    (F.MergerSlot ⊕ ↥F.roots) ↪
      (↥(internalEdgeFinset T (supportFinset (gridGraph m n \ T))) ⊕
        ((gridGraph m n).induce
          (↑((Finset.univ : Finset (GridVertex m n)) \
            supportFinset (gridGraph m n \ T)) :
              Set (GridVertex m n))).ConnectedComponent) where
  toFun x := match x with
    | Sum.inl s => mergerSlotResourceEmbedding hT F root separator
        hseparator hterminal s
    | Sum.inr r => Sum.inr (rootComponentEmbedding r)
  inj' := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl
        ((mergerSlotResourceEmbedding hT F root separator
          hseparator hterminal).injective hab)
    · classical
      let U := supportFinset (gridGraph m n \ T)
      by_cases ha : MergerSlotIsInternal F root U separator a
      · simp [mergerSlotResourceEmbedding, U, ha] at hab
      · simp [mergerSlotResourceEmbedding, U, ha] at hab
        exact (hdisjoint ⟨a, ha⟩ b hab).elim
    · classical
      let U := supportFinset (gridGraph m n \ T)
      by_cases hb : MergerSlotIsInternal F root U separator b
      · simp [mergerSlotResourceEmbedding, U, hb] at hab
      · simp [mergerSlotResourceEmbedding, U, hb] at hab
        exact (hdisjoint ⟨b, hb⟩ a hab.symm).elim
    · exact congrArg Sum.inr (rootComponentEmbedding.injective (Sum.inr.inj hab))

/-- The merger factorization hypotheses feed directly into the joint
channel-to-contour routing bound. -/
theorem incidenceWaste_ge_of_channelMergerResources
    {n : Nat} (hn : 2 ≤ n) (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (C : PlaneChannelForest V)
    (demandEmbedding : CanonicalShoreDemand axis n ↪ ↥C.demand)
    (exitEmbedding : ↥C.exits ↪
      BoundarySector (supportFinset (gridGraph n n \ T)))
    (root : GridVertex n n)
    (separator : C.forest.MergerSlot → RootedChannelMerger (T := T) root)
    (hseparator : Function.Injective fun s => (separator s).1.edgeSym2)
    (hterminal : Function.Injective
      (noninternalMergerComponent hT C.forest root separator))
    (rootComponentEmbedding : ↥C.forest.roots ↪
      ((gridGraph n n).induce
        (↑((Finset.univ : Finset (GridVertex n n)) \
          supportFinset (gridGraph n n \ T)) :
            Set (GridVertex n n))).ConnectedComponent)
    (hdisjoint : ∀ s, ∀ r,
      noninternalMergerComponent hT C.forest root separator s ≠
        rootComponentEmbedding r) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) := by
  apply PlaneChannelForest.incidenceWaste_ge_of_combinedChannelContourRouting
    hn axis hT C demandEmbedding exitEmbedding
  exact mergerSlotSumRootsResourceEmbedding hT C.forest root separator
    hseparator hterminal rootComponentEmbedding hdisjoint

end GridDirectionalDart

end GridGraphs
