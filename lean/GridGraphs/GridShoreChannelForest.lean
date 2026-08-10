import GridGraphs.PlaneChannelForest
import GridGraphs.GridCotreeSplitOuter

/-!
# Rooted grid-shore channel forests

Rooted tree darts already carry a finite laminar hierarchy through inclusion of
their target shores.  This file turns that hierarchy into a `ParentForest`.
The rank is the number of grid vertices outside the shore, so moving to a
strict supershore decreases rank.

The construction does not assert the still-missing canonical routing of row
and corner demands.  It does identify two genuine kinds of merger location:
branching vertices of the shore hierarchy and darts occupied by at least two
labelled cotree channels.  In either case the rooted orientation makes the
attachment tree edge injective.  Restricting to locations whose two endpoints
belong to the cotree support gives the internal-tree-edge resource required by
the contour ledger.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

set_option maxHeartbeats 800000

namespace GridDirectionalDart

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

/-- Tree darts pointing away from a fixed root. -/
def RootedTreeDart (root : GridVertex m n) :=
  {d : GridDirectionalDart T // AwayFromRoot root d}

noncomputable instance rootedTreeDartFintype (root : GridVertex m n) :
    Fintype (RootedTreeDart (T := T) root) := by
  classical
  exact Fintype.ofInjective
    (fun d : RootedTreeDart (T := T) root => d.1) Subtype.val_injective

noncomputable instance rootedTreeDartDecidableEq (root : GridVertex m n) :
    DecidableEq (RootedTreeDart (T := T) root) := Classical.decEq _

/-- A possible parent shore is any strictly larger rooted shore. -/
def HasStrictSupershore {root : GridVertex m n}
    (a b : RootedTreeDart (T := T) root) : Prop :=
  a.1.targetShoreVertices ⊂ b.1.targetShoreVertices

private noncomputable def rootedShoreParent {root : GridVertex m n}
    (a : RootedTreeDart (T := T) root) :
    Option (RootedTreeDart (T := T) root) := by
  classical
  exact if h : ∃ b, HasStrictSupershore a b then some (Classical.choose h) else none

private theorem rootedShoreParent_strict {root : GridVertex m n}
    {a b : RootedTreeDart (T := T) root}
    (hparent : rootedShoreParent a = some b) :
    HasStrictSupershore a b := by
  classical
  unfold rootedShoreParent at hparent
  split at hparent
  · rename_i h
    have hb : Classical.choose h = b := Option.some.inj hparent
    simpa [hb] using Classical.choose_spec h
  · simp at hparent

/-- The finite forest obtained by directing each nonmaximal rooted shore to a
strict supershore.  No planar routing choices or demand inequalities enter the
construction. -/
noncomputable def rootedShoreParentForest (root : GridVertex m n) :
    ParentForest (RootedTreeDart (T := T) root) where
  parent := rootedShoreParent
  rank := fun d => Fintype.card (GridVertex m n) - d.1.targetShoreVertices.card
  rank_parent := by
    intro a b hparent
    have hstrict := rootedShoreParent_strict hparent
    have hcard : a.1.targetShoreVertices.card < b.1.targetShoreVertices.card :=
      Finset.card_lt_card hstrict
    have hbcard : b.1.targetShoreVertices.card ≤ Fintype.card (GridVertex m n) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    exact Nat.sub_lt_sub_left (hcard.trans_le hbcard) hcard

/-- Roots of the shore forest are exactly the maximal away-root shores. -/
theorem mem_rootedShoreParentForest_roots_iff (root : GridVertex m n)
    (a : RootedTreeDart (T := T) root) :
    a ∈ (rootedShoreParentForest (T := T) root).roots ↔
      ¬∃ b, HasStrictSupershore a b := by
  classical
  simp only [ParentForest.roots, Finset.mem_filter, Finset.mem_univ, true_and]
  change rootedShoreParent a = none ↔ _
  unfold rootedShoreParent
  simp

/-- A branching location in the rooted-shore hierarchy. -/
def RootedShoreMerger (root : GridVertex m n) :=
  ↥((rootedShoreParentForest (T := T) root).mergers)

/-- The attachment edge of every rooted-shore hierarchy merger is injective.
This is the structural reason one tree edge can account for at most one merger
location. -/
noncomputable def rootedShoreMergerEdgeEmbedding (htree : T.IsTree)
    (root : GridVertex m n) :
    RootedShoreMerger (T := T) root ↪ ↥T.edgeFinset where
  toFun a := ⟨a.1.1.edgeSym2, by
    rw [SimpleGraph.mem_edgeFinset]
    change T.Adj a.1.1.source a.1.1.target
    exact a.1.1.adj⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact eq_of_edgeSym2_eq_of_awayFromRoot htree root a.1.2 b.1.2
      (congrArg Subtype.val hab)

/-- A rooted dart is a concrete labelled-channel merger when at least two
distinct omitted grid edges occupy its channel position. -/
noncomputable def activeRootedChannels (root : GridVertex m n)
    (d : GridDirectionalDart T) : Finset (GridEdge m n) := by
  classical
  exact Finset.univ.filter fun e => d ∈ rootedPortChannel root e

/-- Concrete multi-channel merger locations, independent of the parent choice
used in `rootedShoreParentForest`. -/
def RootedChannelMerger (root : GridVertex m n) :=
  {d : GridDirectionalDart T //
    AwayFromRoot root d ∧ 2 ≤ (activeRootedChannels root d).card}

/-- Actual rooted channel mergers also inject into their attachment tree
edges.  The channel-count condition is geometric data, not a cardinal bound. -/
noncomputable def rootedChannelMergerEdgeEmbedding (htree : T.IsTree)
    (root : GridVertex m n) :
    RootedChannelMerger (T := T) root ↪ ↥T.edgeFinset where
  toFun a := ⟨a.1.edgeSym2, by
    rw [SimpleGraph.mem_edgeFinset]
    change T.Adj a.1.source a.1.target
    exact a.1.adj⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact eq_of_edgeSym2_eq_of_awayFromRoot htree root a.2.1 b.2.1
      (congrArg Subtype.val hab)

/-- Concrete rooted channel mergers whose attachment edge has both endpoints
in `U`.  This endpoint condition is exactly what is needed, and no final
resource inequality is assumed. -/
def InternalRootedChannelMerger (root : GridVertex m n)
    (U : Finset (GridVertex m n)) :=
  {a : RootedChannelMerger (T := T) root // ∀ v ∈ a.1.edgeSym2, v ∈ U}

/-- Supported concrete channel mergers inject into the internal tree-edge
summand of the primal contour ledger. -/
noncomputable def internalRootedChannelMergerEmbedding (htree : T.IsTree)
    (root : GridVertex m n) (U : Finset (GridVertex m n)) :
    InternalRootedChannelMerger (T := T) root U ↪
      ↥(internalEdgeFinset T U) where
  toFun a := ⟨a.1.1.edgeSym2, by
    rw [mem_internalEdgeFinset]
    exact ⟨(rootedChannelMergerEdgeEmbedding htree root a.1).2, a.2⟩⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact eq_of_edgeSym2_eq_of_awayFromRoot htree root a.1.2.1 b.1.2.1
      (congrArg Subtype.val hab)

/-- A concrete merger is witnessed by two distinct omitted grid edges.  Their
endpoints, unlike the endpoints of the attachment tree edge, necessarily lie
in the cotree support. -/
theorem rootedChannelMerger_two_cotreePorts
    (root : GridVertex m n) (a : RootedChannelMerger (T := T) root) :
    let U := supportFinset (gridGraph m n \ T)
    ∃ e f : GridEdge m n, e ≠ f ∧ e ∈ a.1.cotreePorts ∧ f ∈ a.1.cotreePorts ∧
      e.primalEndpoints.1 ∈ U ∧ e.primalEndpoints.2 ∈ U ∧
      f.primalEndpoints.1 ∈ U ∧ f.primalEndpoints.2 ∈ U := by
  classical
  dsimp only
  have hcard : 1 < (activeRootedChannels root a.1).card := by
    have := a.2.2
    omega
  rcases Finset.one_lt_card.mp hcard with ⟨e, he, f, hf, hef⟩
  have heChannel := (Finset.mem_filter.mp he).2
  have hfChannel := (Finset.mem_filter.mp hf).2
  have hePort := ((mem_rootedPortChannel root e a.1).mp heChannel).2
  have hfPort := ((mem_rootedPortChannel root f a.1).mp hfChannel).2
  have endpoints_mem_support (g : GridEdge m n) (hg : g ∈ a.1.cotreePorts) :
      g.primalEndpoints.1 ∈ supportFinset (gridGraph m n \ T) ∧
        g.primalEndpoints.2 ∈ supportFinset (gridGraph m n \ T) := by
    have hgNotTree := (mem_cotreePorts a.1 g).mp hg |>.2
    have hgGrid : (gridGraph m n).Adj g.primalEndpoints.1 g.primalEndpoints.2 := by
      rw [← SimpleGraph.mem_edgeSet]
      exact GridEdge.primalSym2_mem_gridGraph_edgeSet g
    have hgCotree : (gridGraph m n \ T).Adj
        g.primalEndpoints.1 g.primalEndpoints.2 := ⟨hgGrid, hgNotTree⟩
    constructor <;> rw [mem_supportFinset]
    · exact ((gridGraph m n \ T).degree_pos_iff_exists_adj _).mpr
        ⟨g.primalEndpoints.2, hgCotree⟩
    · exact ((gridGraph m n \ T).degree_pos_iff_exists_adj _).mpr
        ⟨g.primalEndpoints.1, hgCotree.symm⟩
  have heSupport := endpoints_mem_support e hePort
  have hfSupport := endpoints_mem_support f hfPort
  exact ⟨e, f, hef, hePort, hfPort, heSupport.1, heSupport.2,
    hfSupport.1, hfSupport.2⟩

/-- Unconditional attachment-resource dichotomy for a concrete grid merger.
If its tree edge is not internal to cotree support, an unsupported endpoint is
a preserved vertex and canonically roots a component of the full-vertex
induced graph.  Thus multi-channel occupancy alone does not imply the endpoint
hypothesis of `internalRootedChannelMergerEmbedding`. -/
theorem rootedChannelMerger_internal_or_preservedComponent
    (hT : IsSpanningSubtree (gridGraph m n) T) (root : GridVertex m n)
    (a : RootedChannelMerger (T := T) root) :
    let U := supportFinset (gridGraph m n \ T)
    let F := (Finset.univ : Finset (GridVertex m n)) \ U
    (∃ e : ↥(internalEdgeFinset T U), e.1 = a.1.edgeSym2) ∨
      ∃ (v : GridVertex m n) (hvF : v ∈ F),
        v ∈ a.1.edgeSym2 ∧ preservesIncidentEdges (gridGraph m n) T v ∧
          (⟨v, hvF⟩ : ↥(↑F : Set (GridVertex m n))) ∈
            ((gridGraph m n).induce
              (↑F : Set (GridVertex m n))).connectedComponentMk ⟨v, hvF⟩ := by
  classical
  dsimp only
  let U := supportFinset (gridGraph m n \ T)
  by_cases hs : a.1.source ∈ U
  · by_cases ht : a.1.target ∈ U
    · left
      refine ⟨⟨a.1.edgeSym2, ?_⟩, rfl⟩
      rw [mem_internalEdgeFinset]
      refine ⟨(rootedChannelMergerEdgeEmbedding hT.isTree root a).2, ?_⟩
      intro v hv
      rw [edgeSym2, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact hs
      · exact ht
    · right
      have htF : a.1.target ∈
          (Finset.univ : Finset (GridVertex m n)) \ U :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ht⟩
      refine ⟨a.1.target, htF, ?_, ?_, ?_⟩
      · simp [edgeSym2, Sym2.mem_iff]
      · by_contra hnot
        exact ht ((mem_supportFinset_sdiff_iff_not_preserves
          (gridGraph m n) T hT.le a.1.target).mpr hnot)
      · exact ConnectedComponent.connectedComponentMk_mem
  · right
    have hsF : a.1.source ∈
        (Finset.univ : Finset (GridVertex m n)) \ U :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hs⟩
    refine ⟨a.1.source, hsF, ?_, ?_, ?_⟩
    · simp [edgeSym2, Sym2.mem_iff]
    · by_contra hnot
      exact hs ((mem_supportFinset_sdiff_iff_not_preserves
        (gridGraph m n) T hT.le a.1.source).mpr hnot)
    · exact ConnectedComponent.connectedComponentMk_mem

end GridDirectionalDart

end GridGraphs
