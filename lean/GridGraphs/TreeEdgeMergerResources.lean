import GridGraphs.ChannelContourRouting
import GridGraphs.ChannelCarrierRoots

/-!
# Tree-edge resources for channel merger slots

Merger slots need distinct physical tree edges, not a separate channel-merger
object.  An edge internal to cotree support uses the internal-edge resource;
otherwise an endpoint outside support supplies a preserved-component resource.
-/

namespace GridGraphs

open Finset SimpleGraph

def TreeEdgeTokenIsInternal {A : Type*} {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (U : Finset (GridVertex m n)) (tokenEdge : A ↪ ↥T.edgeFinset)
    (a : A) : Prop :=
  ∀ v ∈ (tokenEdge a).1, v ∈ U

def NoninternalTreeEdgeToken {A : Type*} {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (U : Finset (GridVertex m n)) (tokenEdge : A ↪ ↥T.edgeFinset) :=
  {a : A // ¬TreeEdgeTokenIsInternal U tokenEdge a}

noncomputable def noninternalTreeEdgeTokenComponent
    {A : Type*} {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (U : Finset (GridVertex m n)) (tokenEdge : A ↪ ↥T.edgeFinset)
    (a : NoninternalTreeEdgeToken U tokenEdge) :
    ((gridGraph m n).induce
      (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
        Set (GridVertex m n))).ConnectedComponent := by
  classical
  have hexists : ∃ v, v ∈ (tokenEdge a.1).1 ∧ v ∉ U := by
    simpa [TreeEdgeTokenIsInternal] using a.2
  let v := Classical.choose hexists
  have hv := Classical.choose_spec hexists
  exact ((gridGraph m n).induce
    (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
      Set (GridVertex m n))).connectedComponentMk
      ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv.2⟩⟩

/-- Distinct tree-edge tokens factor through internal edges or distinct
preserved components. -/
noncomputable def treeEdgeTokenResourceEmbedding
    {A : Type*} {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (U : Finset (GridVertex m n)) (tokenEdge : A ↪ ↥T.edgeFinset)
    (hterminal : Function.Injective
      (noninternalTreeEdgeTokenComponent U tokenEdge)) :
    A ↪ (↥(internalEdgeFinset T U) ⊕
      ((gridGraph m n).induce
        (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
          Set (GridVertex m n))).ConnectedComponent) where
  toFun a := by
    classical
    if ha : TreeEdgeTokenIsInternal U tokenEdge a then
      exact Sum.inl ⟨(tokenEdge a).1, by
        rw [mem_internalEdgeFinset]
        exact ⟨(tokenEdge a).2, ha⟩⟩
    else
      exact Sum.inr (noninternalTreeEdgeTokenComponent U tokenEdge ⟨a, ha⟩)
  inj' := by
    classical
    intro a b hab
    by_cases ha : TreeEdgeTokenIsInternal U tokenEdge a
    · by_cases hb : TreeEdgeTokenIsInternal U tokenEdge b
      · simp [ha, hb] at hab
        exact hab
      · simp [ha, hb] at hab
    · by_cases hb : TreeEdgeTokenIsInternal U tokenEdge b
      · simp [ha, hb] at hab
      · simp [ha, hb] at hab
        exact congrArg Subtype.val (hterminal hab)

namespace ParentForest

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]

def MergerSlotEdgeIsInternal (F : ParentForest V)
    (U : Finset (GridVertex m n))
    (slotEdge : F.MergerSlot ↪ ↥T.edgeFinset) (s : F.MergerSlot) : Prop :=
  ∀ v ∈ (slotEdge s).1, v ∈ U

def NoninternalMergerSlotEdge (F : ParentForest V)
    (U : Finset (GridVertex m n))
    (slotEdge : F.MergerSlot ↪ ↥T.edgeFinset) :=
  {s : F.MergerSlot // ¬F.MergerSlotEdgeIsInternal U slotEdge s}

noncomputable def noninternalMergerSlotEdgeComponent
    (F : ParentForest V) (U : Finset (GridVertex m n))
    (slotEdge : F.MergerSlot ↪ ↥T.edgeFinset)
    (s : F.NoninternalMergerSlotEdge U slotEdge) :
    ((gridGraph m n).induce
      (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
        Set (GridVertex m n))).ConnectedComponent := by
  classical
  have hexists : ∃ v, v ∈ (slotEdge s.1).1 ∧ v ∉ U := by
    simpa [MergerSlotEdgeIsInternal] using s.2
  let v := Classical.choose hexists
  have hv := Classical.choose_spec hexists
  exact ((gridGraph m n).induce
    (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
      Set (GridVertex m n))).connectedComponentMk
      ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv.2⟩⟩

noncomputable def mergerSlotTreeEdgeResourceEmbedding
    (F : ParentForest V) (U : Finset (GridVertex m n))
    (slotEdge : F.MergerSlot ↪ ↥T.edgeFinset)
    (hterminal : Function.Injective
      (F.noninternalMergerSlotEdgeComponent U slotEdge)) :
    F.MergerSlot ↪
      (↥(internalEdgeFinset T U) ⊕
        ((gridGraph m n).induce
          (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
            Set (GridVertex m n))).ConnectedComponent) where
  toFun s := by
    classical
    if hs : F.MergerSlotEdgeIsInternal U slotEdge s then
      exact Sum.inl ⟨(slotEdge s).1, by
        rw [mem_internalEdgeFinset]
        exact ⟨(slotEdge s).2, hs⟩⟩
    else
      exact Sum.inr (F.noninternalMergerSlotEdgeComponent U slotEdge ⟨s, hs⟩)
  inj' := by
    classical
    intro a b hab
    by_cases ha : F.MergerSlotEdgeIsInternal U slotEdge a
    · by_cases hb : F.MergerSlotEdgeIsInternal U slotEdge b
      · simp [ha, hb] at hab
        exact hab
      · simp [ha, hb] at hab
    · by_cases hb : F.MergerSlotEdgeIsInternal U slotEdge b
      · simp [ha, hb] at hab
      · simp [ha, hb] at hab
        exact congrArg Subtype.val (hterminal hab)

noncomputable def mergerSlotTreeEdgeSumRootsResourceEmbedding
    (F : ParentForest V) (U : Finset (GridVertex m n))
    (slotEdge : F.MergerSlot ↪ ↥T.edgeFinset)
    (hterminal : Function.Injective
      (F.noninternalMergerSlotEdgeComponent U slotEdge))
    (rootComponentEmbedding : ↥F.roots ↪
      ((gridGraph m n).induce
        (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
          Set (GridVertex m n))).ConnectedComponent)
    (hdisjoint : ∀ s r,
      F.noninternalMergerSlotEdgeComponent U slotEdge s ≠
        rootComponentEmbedding r) :
    (F.MergerSlot ⊕ ↥F.roots) ↪
      (↥(internalEdgeFinset T U) ⊕
        ((gridGraph m n).induce
          (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
            Set (GridVertex m n))).ConnectedComponent) where
  toFun
    | .inl s => F.mergerSlotTreeEdgeResourceEmbedding U slotEdge hterminal s
    | .inr r => Sum.inr (rootComponentEmbedding r)
  inj' := by
    classical
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl
        ((F.mergerSlotTreeEdgeResourceEmbedding U slotEdge hterminal).injective hab)
    · by_cases ha : F.MergerSlotEdgeIsInternal U slotEdge a
      · simp [mergerSlotTreeEdgeResourceEmbedding, ha] at hab
      · simp [mergerSlotTreeEdgeResourceEmbedding, ha] at hab
        exact (hdisjoint ⟨a, ha⟩ b hab).elim
    · by_cases hb : F.MergerSlotEdgeIsInternal U slotEdge b
      · simp [mergerSlotTreeEdgeResourceEmbedding, hb] at hab
      · simp [mergerSlotTreeEdgeResourceEmbedding, hb] at hab
        exact (hdisjoint ⟨b, hb⟩ a hab.symm).elim
    · exact congrArg Sum.inr (rootComponentEmbedding.injective (Sum.inr.inj hab))

end ParentForest

end GridGraphs
