import GridGraphs.CanonicalShoreContinuation
import GridGraphs.ParentForestPhysicalSlots

/-!
# Canonical launched-shore forest

The continuing channel forest contains only immediate-shore ancestors of
launched canonical germs.  Private source vertices make every continuing
demand a leaf even when one launched shore is an ancestor of another.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace GridDirectionalDart

def ImmediateShoreAncestorRel {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (htree : T.IsTree) {root : GridVertex m n}
    (a b : RootedTreeDart (T := T) root) : Prop :=
  immediateRootedShoreParent htree a = some b

/-- Rooted shores lying on an immediate-parent chain from a continuing
canonical germ. -/
def LaunchedShoreAncestor {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :=
  {a : RootedTreeDart (T := T) root //
    ∃ q : CanonicalShoreDemand.Unsupported axis hn2 T,
      Relation.ReflTransGen (ImmediateShoreAncestorRel hT.isTree)
        (launchedShoreEmbedding axis hn2 hn3 hT root q) a}

noncomputable instance launchedShoreAncestorFintype {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    Fintype (LaunchedShoreAncestor axis hn2 hn3 hT root) :=
  Fintype.ofInjective (fun a => a.1) Subtype.val_injective

noncomputable instance launchedShoreAncestorDecidableEq {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    DecidableEq (LaunchedShoreAncestor axis hn2 hn3 hT root) :=
  Classical.decEq _

/-- Every launched shore belongs to the ancestor closure. -/
noncomputable def launchedShoreAncestorEmbedding {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    CanonicalShoreDemand.Unsupported axis hn2 T ↪
      LaunchedShoreAncestor axis hn2 hn3 hT root where
  toFun q := ⟨launchedShoreEmbedding axis hn2 hn3 hT root q,
    ⟨q, .refl⟩⟩
  inj' := fun _ _ h => (launchedShoreEmbedding axis hn2 hn3 hT root).injective
    (congrArg Subtype.val h)

/-- The ancestor closure is closed under immediate shore parents. -/
theorem launchedShoreAncestor_parent_mem {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n)
    (a : LaunchedShoreAncestor axis hn2 hn3 hT root)
    {b : RootedTreeDart (T := T) root}
    (hab : immediateRootedShoreParent hT.isTree a.1 = some b) :
    b ∈ {x | ∃ q : CanonicalShoreDemand.Unsupported axis hn2 T,
      Relation.ReflTransGen (ImmediateShoreAncestorRel hT.isTree)
        (launchedShoreEmbedding axis hn2 hn3 hT root q) x} := by
  obtain ⟨q, hqa⟩ := a.2
  exact ⟨q, hqa.tail hab⟩

abbrev CanonicalShoreCarrier {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :=
  CanonicalShoreDemand.Unsupported axis hn2 T ⊕
    LaunchedShoreAncestor axis hn2 hn3 hT root

noncomputable def canonicalShoreParent {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    CanonicalShoreCarrier axis hn2 hn3 hT root →
      Option (CanonicalShoreCarrier axis hn2 hn3 hT root)
  | .inl q => some (.inr (launchedShoreAncestorEmbedding axis hn2 hn3 hT root q))
  | .inr a => by
      classical
      exact match hparent : immediateRootedShoreParent hT.isTree a.1 with
        | none => none
        | some b => some (.inr ⟨b,
            launchedShoreAncestor_parent_mem axis hn2 hn3 hT root a hparent⟩)

/-- Parent forest on private demands and their launched immediate-shore
ancestor closure. -/
noncomputable def canonicalShoreParentForest {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    ParentForest (CanonicalShoreCarrier axis hn2 hn3 hT root) where
  parent := canonicalShoreParent axis hn2 hn3 hT root
  rank
    | .inl q =>
        (immediateRootedShoreParentForest hT.isTree root).rank
          (launchedShoreEmbedding axis hn2 hn3 hT root q) + 1
    | .inr a => (immediateRootedShoreParentForest hT.isTree root).rank a.1
  rank_parent := by
    intro a b hab
    rcases a with q | a
    · simp only [canonicalShoreParent, Option.some.injEq] at hab
      subst b
      change (immediateRootedShoreParentForest hT.isTree root).rank
          (launchedShoreEmbedding axis hn2 hn3 hT root q) <
        (immediateRootedShoreParentForest hT.isTree root).rank
          (launchedShoreEmbedding axis hn2 hn3 hT root q) + 1
      omega
    · simp only [canonicalShoreParent] at hab
      split at hab
      · simp at hab
      · rename_i p hparent
        have hb : b = Sum.inr (⟨p,
            launchedShoreAncestor_parent_mem axis hn2 hn3 hT root a hparent⟩ :
              LaunchedShoreAncestor axis hn2 hn3 hT root) :=
          (Option.some.inj hab).symm
        subst b
        exact (immediateRootedShoreParentForest hT.isTree root).rank_parent hparent

/-- The private demand leaves of the canonical shore forest. -/
noncomputable def canonicalShoreDemands {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    Finset (CanonicalShoreCarrier axis hn2 hn3 hT root) := by
  classical
  exact Finset.univ.filter fun x => match x with
    | .inl _ => True
    | .inr _ => False

noncomputable def canonicalShoreDemandEmbedding {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    CanonicalShoreDemand.Unsupported axis hn2 T ↪
      ↥(canonicalShoreDemands axis hn2 hn3 hT root) where
  toFun q := ⟨.inl q, by simp [canonicalShoreDemands]⟩
  inj' := by
    intro a b hab
    exact Sum.inl.inj (congrArg Subtype.val hab)

theorem canonicalShoreDemands_subset_leaves {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    canonicalShoreDemands axis hn2 hn3 hT root ⊆
      (canonicalShoreParentForest axis hn2 hn3 hT root).leaves := by
  classical
  intro q hq
  rcases q with d | a
  · have hchildren :
        (canonicalShoreParentForest axis hn2 hn3 hT root).children
          (Sum.inl d) = ∅ := by
      ext x
      simp only [ParentForest.children, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      rcases x with x | x
      · simp [canonicalShoreParentForest, canonicalShoreParent]
      · simp only [canonicalShoreParentForest, canonicalShoreParent]
        split <;> simp
    simp only [ParentForest.leaves, Finset.mem_filter, Finset.mem_univ, true_and,
      ParentForest.childCount, hchildren, Finset.card_empty]
  · simp [canonicalShoreDemands] at hq

/-- The actual finite pruned forest of continuing canonical shore germs. -/
noncomputable def canonicalShorePlaneChannelForest {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    PlaneChannelForest (CanonicalShoreCarrier axis hn2 hn3 hT root) where
  forest := canonicalShoreParentForest axis hn2 hn3 hT root
  demand := canonicalShoreDemands axis hn2 hn3 hT root
  exits := ∅
  demand_leaf_or_exit := by
    intro q hq
    exact Finset.mem_union_left _
      (canonicalShoreDemands_subset_leaves axis hn2 hn3 hT root hq)

/-- Shore-state children are physical; private demand children are the sole
nonphysical kind. -/
def CanonicalShoreCarrier.IsPhysical {n : Nat}
    {axis : ShoreSweepAxis} {hn2 : 2 ≤ n} {hn3 : 3 ≤ n}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    {hT : IsSpanningSubtree (gridGraph n n) T}
    {root : GridVertex n n} :
    CanonicalShoreCarrier axis hn2 hn3 hT root → Prop
  | .inl _ => False
  | .inr _ => True

noncomputable instance canonicalShoreCarrierIsPhysicalDecidablePred {n : Nat}
    {axis : ShoreSweepAxis} {hn2 : 2 ≤ n} {hn3 : 3 ≤ n}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    {hT : IsSpanningSubtree (gridGraph n n) T}
    {root : GridVertex n n} :
    DecidablePred (CanonicalShoreCarrier.IsPhysical
      (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) (root := root)) := by
  classical
  intro x
  infer_instance

/-- Injectivity of launched germs implies that each shore state has at most one
private, nonphysical child. -/
theorem canonicalShore_nonphysicalChildren_card_le_one {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) (v : CanonicalShoreCarrier axis hn2 hn3 hT root) :
    ((canonicalShoreParentForest axis hn2 hn3 hT root).nonphysicalChildren
      CanonicalShoreCarrier.IsPhysical v).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  rcases x with q | x
  · rcases y with r | y
    · have hxparent := (Finset.mem_filter.mp hx'.1).2
      have hyparent := (Finset.mem_filter.mp hy'.1).2
      simp only [canonicalShoreParentForest, canonicalShoreParent] at hxparent hyparent
      have hlaunch :
          launchedShoreAncestorEmbedding axis hn2 hn3 hT root q =
            launchedShoreAncestorEmbedding axis hn2 hn3 hT root r := by
        exact Sum.inr.inj (Option.some.inj (hxparent.trans hyparent.symm))
      have hqr :=
        (launchedShoreAncestorEmbedding axis hn2 hn3 hT root).injective hlaunch
      subst r
      rfl
    · simp [CanonicalShoreCarrier.IsPhysical] at hy'
  · simp [CanonicalShoreCarrier.IsPhysical] at hx'

/-- Extract the rooted shore state from a physical carrier vertex. -/
def physicalCarrierAncestor {n : Nat}
    {axis : ShoreSweepAxis} {hn2 : 2 ≤ n} {hn3 : 3 ≤ n}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    {hT : IsSpanningSubtree (gridGraph n n) T}
    {root : GridVertex n n}
    (x : {x : CanonicalShoreCarrier axis hn2 hn3 hT root //
      CanonicalShoreCarrier.IsPhysical x}) :
    LaunchedShoreAncestor axis hn2 hn3 hT root := by
  rcases x with ⟨x, hx⟩
  rcases x with q | a
  · exact False.elim hx
  · exact a

/-- Physical shore children carry distinct tree attachment edges. -/
noncomputable def physicalCarrierTreeEdgeEmbedding {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    {x : CanonicalShoreCarrier axis hn2 hn3 hT root //
      CanonicalShoreCarrier.IsPhysical x} ↪ ↥T.edgeFinset where
  toFun x := ⟨(physicalCarrierAncestor x).1.1.edgeSym2, by
    rw [SimpleGraph.mem_edgeFinset]
    exact (physicalCarrierAncestor x).1.1.adj⟩
  inj' := by
    intro x y hxy
    have hedge : (physicalCarrierAncestor x).1.1.edgeSym2 =
        (physicalCarrierAncestor y).1.1.edgeSym2 := congrArg Subtype.val hxy
    have hdart := eq_of_edgeSym2_eq_of_awayFromRoot hT.isTree root
      (physicalCarrierAncestor x).1.2 (physicalCarrierAncestor y).1.2 hedge
    have hancestor : physicalCarrierAncestor x = physicalCarrierAncestor y := by
      apply Subtype.ext
      apply Subtype.ext
      exact hdart
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    rcases x with q | a
    · exact False.elim hx
    rcases y with r | b
    · exact False.elim hy
    apply Subtype.ext
    exact congrArg Sum.inr hancestor

/-- Every abstract merger-excess slot of the canonical forest receives a
distinct physical child tree edge. -/
noncomputable def canonicalShoreMergerSlotTreeEdgeEmbedding {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    (canonicalShoreParentForest axis hn2 hn3 hT root).MergerSlot ↪
      ↥T.edgeFinset :=
  ((canonicalShoreParentForest axis hn2 hn3 hT root).mergerSlotPhysicalChildEmbedding
      CanonicalShoreCarrier.IsPhysical
        (canonicalShore_nonphysicalChildren_card_le_one axis hn2 hn3 hT root)).trans
    (physicalCarrierTreeEdgeEmbedding axis hn2 hn3 hT root)

/-- A canonical forest root is necessarily a physical shore state. -/
def canonicalShoreRootAncestor {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n)
    (r : ↥(canonicalShoreParentForest axis hn2 hn3 hT root).roots) :
    LaunchedShoreAncestor axis hn2 hn3 hT root := by
  rcases r with ⟨r, hr⟩
  rcases r with q | a
  · have hnone := (Finset.mem_filter.mp hr).2
    simp [canonicalShoreParentForest, canonicalShoreParent] at hnone
  · exact a

noncomputable def canonicalShoreRootTreeEdgeEmbedding {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    ↥(canonicalShoreParentForest axis hn2 hn3 hT root).roots ↪ ↥T.edgeFinset where
  toFun r := ⟨(canonicalShoreRootAncestor axis hn2 hn3 hT root r).1.1.edgeSym2, by
    rw [SimpleGraph.mem_edgeFinset]
    exact (canonicalShoreRootAncestor axis hn2 hn3 hT root r).1.1.adj⟩
  inj' := by
    intro a b hab
    have hedge := congrArg Subtype.val hab
    have hdart := eq_of_edgeSym2_eq_of_awayFromRoot hT.isTree root
      (canonicalShoreRootAncestor axis hn2 hn3 hT root a).1.2
      (canonicalShoreRootAncestor axis hn2 hn3 hT root b).1.2 hedge
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    rcases a with q | a
    · have hnone := (Finset.mem_filter.mp ha).2
      simp [canonicalShoreParentForest, canonicalShoreParent] at hnone
    rcases b with r | b
    · have hnone := (Finset.mem_filter.mp hb).2
      simp [canonicalShoreParentForest, canonicalShoreParent] at hnone
    apply Subtype.ext
    apply congrArg Sum.inr
    apply Subtype.ext
    apply Subtype.ext
    exact hdart

/-- Merger-child edges and maximal-shore root edges are globally distinct. -/
theorem canonicalShore_mergerEdge_ne_rootEdge {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n)
    (s : (canonicalShoreParentForest axis hn2 hn3 hT root).MergerSlot)
    (r : ↥(canonicalShoreParentForest axis hn2 hn3 hT root).roots) :
    (canonicalShoreMergerSlotTreeEdgeEmbedding axis hn2 hn3 hT root s).1 ≠
      (canonicalShoreRootTreeEdgeEmbedding axis hn2 hn3 hT root r).1 := by
  intro hedge
  let F := canonicalShoreParentForest axis hn2 hn3 hT root
  let localChild := F.localMergerSlotPhysicalChildEmbedding
    CanonicalShoreCarrier.IsPhysical
      (canonicalShore_nonphysicalChildren_card_le_one axis hn2 hn3 hT root) s.1 s.2
  let child : {x : CanonicalShoreCarrier axis hn2 hn3 hT root //
      CanonicalShoreCarrier.IsPhysical x} :=
    ⟨localChild.1, (Finset.mem_filter.mp localChild.2).2⟩
  have hphysicalEdge :
      (physicalCarrierAncestor child).1.1.edgeSym2 =
        (canonicalShoreRootAncestor axis hn2 hn3 hT root r).1.1.edgeSym2 := by
    exact hedge
  have hdart := eq_of_edgeSym2_eq_of_awayFromRoot hT.isTree root
    (physicalCarrierAncestor child).1.2
    (canonicalShoreRootAncestor axis hn2 hn3 hT root r).1.2 hphysicalEdge
  rcases r with ⟨r, hr⟩
  have hcarrier : child.1 = r := by
    rcases child with ⟨child, hchildPhysical⟩
    rcases child with q | a
    · exact False.elim hchildPhysical
    rcases r with q | b
    · have hnone := (Finset.mem_filter.mp hr).2
      simp [canonicalShoreParentForest, canonicalShoreParent] at hnone
    apply congrArg Sum.inr
    apply Subtype.ext
    apply Subtype.ext
    exact hdart
  have hchildMem := (Finset.mem_filter.mp localChild.2).1
  have hchildParent := (Finset.mem_filter.mp hchildMem).2
  have hrootParent := (Finset.mem_filter.mp hr).2
  rw [hcarrier] at hchildParent
  rw [hrootParent] at hchildParent
  simp at hchildParent

/-- Joint physical tree-edge labels for merger excess and maximal shore roots. -/
noncomputable def canonicalShoreTerminalTreeEdgeEmbedding {n : Nat}
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    ((canonicalShoreParentForest axis hn2 hn3 hT root).MergerSlot ⊕
      ↥(canonicalShoreParentForest axis hn2 hn3 hT root).roots) ↪ ↥T.edgeFinset where
  toFun
    | .inl s => canonicalShoreMergerSlotTreeEdgeEmbedding axis hn2 hn3 hT root s
    | .inr r => canonicalShoreRootTreeEdgeEmbedding axis hn2 hn3 hT root r
  inj' := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl
        ((canonicalShoreMergerSlotTreeEdgeEmbedding axis hn2 hn3 hT root).injective hab)
    · exact (canonicalShore_mergerEdge_ne_rootEdge axis hn2 hn3 hT root a b
        (congrArg Subtype.val hab)).elim
    · exact (canonicalShore_mergerEdge_ne_rootEdge axis hn2 hn3 hT root b a
        (congrArg Subtype.val hab).symm).elim
    · exact congrArg Sum.inr
        ((canonicalShoreRootTreeEdgeEmbedding axis hn2 hn3 hT root).injective hab)

end GridDirectionalDart

end GridGraphs
