import GridGraphs.Forests.ReconvergenceLens
import GridGraphs.Routing.CanonicalExpandedCollisionRouting
import GridGraphs.Geometry.GridExpandedContourCollar
import GridGraphs.Geometry.GridCellBoundaryEdges
import GridGraphs.Routing.LocalizedHallRouting
import GridGraphs.Routing.RankedTransitionOwnership
import GridGraphs.Forests.ParentForestPhysicalSlots
import GridGraphs.Geometry.GridBoundaryNonalternation
import GridGraphs.Geometry.OccurrenceLabelledCotreeDualForest
import GridGraphs.Forests.ParentForestAncestorHull
import GridGraphs.Routing.MinimalAncestorHullRouting

/-!
# Canonical expanded-contour reconvergence lenses

This module identifies each canonical physical merger occurrence with the
generic reconvergence lens on the expanded contour.  It records both physical
tree-edge ownership and the outer cotree port reached by the shared suffix.
It also packages the rigorous interval data currently available: originating
start occurrences, merger slot, and terminal slot.  This is not yet a region
of grid cells, and no planar-region or cardinality assertion is made here.

The former U3 endpoint `CanonicalUpperU3RootHall` is retained as an audited
no-go API.  The current root escape emits only one outer-port candidate per
root, so that Hall statement forces every root active fiber to have size at
most one.  A complete route must replace it with transport exposing internal
edges and raw components.  The older component-split hull APIs are likewise
retained for build compatibility and audit lemmas; their copied continuation
roots, root-port debts, and branch slots are not additional physical resources.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace CanonicalExpandedContourForest

variable {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
  {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
  (hT : IsSpanningSubtree (gridGraph n n) T)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Reconvergence lenses for the canonical expanded-contour first-stop
forest. -/
abbrev CanonicalLens :=
  (firstStop axis hn2 hT).ReconvergenceLens

/-- Every physical merger occurrence is its corresponding canonical lens. -/
def collisionLensEmbedding :
    (planeChannelForest axis hn2 hT).forest.MergerSlot ↪
      CanonicalLens axis hn2 hT where
  toFun := MarkedCycleFirstStop.ReconvergenceLens.ofSlot
  inj' := by
    intro a b hab
    exact congrArg MarkedCycleFirstStop.ReconvergenceLens.mergerSlot hab

/-- A lens retains the physical tree edge already owned by its concrete merger
occurrence. -/
def lensTreeEdgeEmbedding :
    CanonicalLens axis hn2 hT ↪ ↥T.edgeFinset where
  toFun L := mergerSlotTreeEdgeEmbedding axis hn2 hn3 hT L.mergerSlot
  inj' := by
    intro L K hLK
    apply MarkedCycleFirstStop.ReconvergenceLens.ext
    exact (mergerSlotTreeEdgeEmbedding axis hn2 hn3 hT).injective hLK

/-- The marked expanded slot reached by a lens's shared suffix. -/
def lensMarkedSlot (L : CanonicalLens axis hn2 hT) :
    ↥(markedSlots (T := T)) :=
  ⟨L.reachedStop.1,
    (MarkedCycleFirstStop.mem_reachedStops_iff
      (firstStop axis hn2 hT) L.reachedStop).mp L.reachedStop_mem⟩

/-- The split outer cotree port reached by a canonical lens. -/
def lensOuterPort (L : CanonicalLens axis hn2 hT) : GridCotreeOuterPort T :=
  outerPortOfMarkedSlot (T := T) (lensMarkedSlot axis hn2 hT L)

/-- The actual first-stop exit represented by a lens's reached marked state. -/
def lensExit (L : CanonicalLens axis hn2 hT) :
    ↥(firstStop axis hn2 hT).exits :=
  ⟨Sum.inr L.reachedStop, by
    rw [← (firstStop axis hn2 hT).reachedStops_map_inr_eq_exits]
    exact Finset.mem_map.mpr
      ⟨L.reachedStop, L.reachedStop_mem, rfl⟩⟩

@[simp] theorem exitState_lensExit (L : CanonicalLens axis hn2 hT) :
    exitState axis hn2 hT (lensExit axis hn2 hT L) = L.reachedStop := by
  apply Subtype.ext
  have h := exit_value_eq axis hn2 hT (lensExit axis hn2 hT L)
  change Sum.inr L.reachedStop = Sum.inr
    (exitState axis hn2 hT (lensExit axis hn2 hT L)) at h
  exact congrArg Subtype.val (Sum.inr.inj h).symm

/-- The reserved exit embedding sends a lens's actual first stop to its outer
port. -/
@[simp] theorem exitEmbedding_lensExit (L : CanonicalLens axis hn2 hT) :
    exitEmbedding axis hn2 hT (lensExit axis hn2 hT L) =
      lensOuterPort axis hn2 hT L := by
  unfold exitEmbedding lensOuterPort lensMarkedSlot
  apply congrArg (outerPortOfMarkedSlot (T := T))
  apply Subtype.ext
  change (exitState axis hn2 hT (lensExit axis hn2 hT L)).1 =
    L.reachedStop.1
  rw [exitState_lensExit]

/-- Every actual first-stop port of a canonical lens belongs to the canonical
exit-port reservation range. -/
theorem lensOuterPort_mem_range_exitEmbedding
    (L : CanonicalLens axis hn2 hT) :
    lensOuterPort axis hn2 hT L ∈ Set.range (exitEmbedding axis hn2 hT) := by
  exact ⟨lensExit axis hn2 hT L, exitEmbedding_lensExit axis hn2 hT L⟩

/-- Concrete expanded-contour precursor to a geometric lens region.  The
finite occurrence set remembers distinct first-stop intervals even when their
slot carriers have reconverged; the two slots record their common merger and
terminal. -/
structure CanonicalLensIntervalRegion where
  originSlots : Finset ↥(startSlots axis hn2 hT)
  mergerSlot : GridCompassSlot n n
  terminalSlot : GridCompassSlot n n

/-- Canonical interval-region data represented by one reconvergence lens. -/
def lensIntervalRegion (L : CanonicalLens axis hn2 hT) :
    CanonicalLensIntervalRegion axis hn2 hT where
  originSlots := L.originRegion
  mergerSlot := L.mergerState.1.1
  terminalSlot := L.reachedStop.1

@[simp] theorem lensIntervalRegion_originSlots
    (L : CanonicalLens axis hn2 hT) :
    (lensIntervalRegion axis hn2 hT L).originSlots = L.originRegion := rfl

@[simp] theorem lensIntervalRegion_mergerSlot
    (L : CanonicalLens axis hn2 hT) :
    (lensIntervalRegion axis hn2 hT L).mergerSlot = L.mergerState.1.1 := rfl

/-- Exact interval meaning of the finite occurrence carrier: each listed start
reaches the represented merger by a prefix of its marked contour interval. -/
theorem mem_lensIntervalRegion_originSlots_iff
    (L : CanonicalLens axis hn2 hT) (s : ↥(startSlots axis hn2 hT)) :
    s ∈ (lensIntervalRegion axis hn2 hT L).originSlots ↔
      ∃ k ≤ (firstStop axis hn2 hT).distance s.1,
        (((firstStop axis hn2 hT).f : GridCompassSlot n n →
          GridCompassSlot n n)^[k]) s.1 =
            (lensIntervalRegion axis hn2 hT L).mergerSlot := by
  exact (firstStop axis hn2 hT).mem_origins_iff L.mergerState.1 s

/-- The terminal of the represented interval is exactly the expanded slot of
the canonical outer cotree port reached by the lens. -/
theorem lensIntervalRegion_terminalSlot
    (L : CanonicalLens axis hn2 hT) :
    (lensIntervalRegion axis hn2 hT L).terminalSlot =
      GridExpandedContour.outerPortSlot (lensOuterPort axis hn2 hT L) := by
  symm
  exact outerPortSlot_outerPortOfMarkedSlot (T := T)
    (lensMarkedSlot axis hn2 hT L)

/-- Every represented start interval has the concrete terminal slot stored in
the region. -/
theorem terminalState_eq_lensIntervalRegion_terminalSlot
    (L : CanonicalLens axis hn2 hT) {s : ↥(startSlots axis hn2 hT)}
    (hs : s ∈ (lensIntervalRegion axis hn2 hT L).originSlots) :
    ((firstStop axis hn2 hT).terminalState s).1 =
      (lensIntervalRegion axis hn2 hT L).terminalSlot := by
  exact congrArg Subtype.val
    (MarkedCycleFirstStop.ReconvergenceLens.terminalState_eq_reachedStop_of_mem_originRegion
      L hs)

/-- The exact branch data present at a canonical merger.  The private branch
starts at the merger slot itself; the shared branch is the unique used state
immediately preceding it on the expanded contour.  These are occurrences and
states, not two primal paths or a planar region. -/
structure CanonicalLensMergerBranches where
  directStart : ↥(startSlots axis hn2 hT)
  sharedPredecessor : (firstStop axis hn2 hT).State
  mergerState : (firstStop axis hn2 hT).MergerState

/-- Binary branch data selected by a canonical reconvergence lens. -/
def lensMergerBranches (L : CanonicalLens axis hn2 hT) :
    CanonicalLensMergerBranches axis hn2 hT where
  directStart := ⟨L.mergerState.1.1, L.mergerState.2.1⟩
  sharedPredecessor :=
    (firstStop axis hn2 hT).mergerPredecessor L.mergerState
  mergerState := L.mergerState

/-- The private branch is introduced at the merger's expanded slot. -/
@[simp] theorem lensMergerBranches_directStart_value
    (L : CanonicalLens axis hn2 hT) :
    (lensMergerBranches axis hn2 hT L).directStart.1 =
      (lensMergerBranches axis hn2 hT L).mergerState.1.1 := rfl

/-- The shared predecessor makes exactly one expanded-contour step into the
merger slot. -/
theorem lensMergerBranches_sharedPredecessor_succ
    (L : CanonicalLens axis hn2 hT) :
    GridExpandedContour.equiv (T := T)
        (lensMergerBranches axis hn2 hT L).sharedPredecessor.1 =
      (lensMergerBranches axis hn2 hT L).mergerState.1.1 := by
  exact (firstStop axis hn2 hT).f_eq_of_stateParent
    ((firstStop axis hn2 hT).stateParent_mergerPredecessor L.mergerState)

/-- Equivalently, the shared branch is the explicit expanded-contour
predecessor of the merger slot. -/
theorem lensMergerBranches_sharedPredecessor_eq_pred
    (L : CanonicalLens axis hn2 hT) :
    (lensMergerBranches axis hn2 hT L).sharedPredecessor.1 =
      GridExpandedContour.pred (T := T)
        (lensMergerBranches axis hn2 hT L).mergerState.1.1 := by
  have hs := lensMergerBranches_sharedPredecessor_succ axis hn2 hT L
  have hp := congrArg
    (fun s => (GridExpandedContour.equiv (T := T)).symm s) hs
  simpa [GridExpandedContour.equiv] using hp

/-- The incoming shared slot is genuinely different from the newly introduced
private start slot. -/
theorem lensMergerBranches_sharedPredecessor_ne_directStart
    (L : CanonicalLens axis hn2 hT) :
    (lensMergerBranches axis hn2 hT L).sharedPredecessor.1 ≠
      (lensMergerBranches axis hn2 hT L).directStart.1 := by
  intro heq
  let F := firstStop axis hn2 hT
  have hparent := F.stateParent_mergerPredecessor L.mergerState
  have hnot := F.not_mem_stop_of_stateParent hparent
  have hdist := F.distance_succ hnot
  rw [F.f_eq_of_stateParent hparent] at hdist
  change F.distance L.mergerState.1.1 + 1 =
    F.distance (F.mergerPredecessor L.mergerState).1 at hdist
  change (F.mergerPredecessor L.mergerState).1 =
    L.mergerState.1.1 at heq
  rw [heq] at hdist
  omega

/-- The first-stop forest has exactly these two local children at the merger:
the private start occurrence and the unique shared predecessor state. -/
theorem lensMergerBranches_children_eq
    (L : CanonicalLens axis hn2 hT) :
    (firstStop axis hn2 hT).forest.children
        (Sum.inr (lensMergerBranches axis hn2 hT L).mergerState.1) =
      {Sum.inl (lensMergerBranches axis hn2 hT L).directStart,
        Sum.inr (lensMergerBranches axis hn2 hT L).sharedPredecessor} := by
  exact (firstStop axis hn2 hT).children_mergerState_eq L.mergerState

/-- Concrete primal germ represented by the direct occurrence at a merger.
Unsupported starts carry their retained inward tree dart; direct exits carry
their split outer port instead. -/
inductive CanonicalDirectBranchGerm where
  | inward (dart : GridDirectionalDart T)
  | outer (port : GridCotreeOuterPort T)

namespace CanonicalDirectBranchGerm

/-- Expanded slot represented by a direct branch germ. -/
def slot : CanonicalDirectBranchGerm (T := T) → GridCompassSlot n n
  | .inward d => GridExpandedContour.slotOfDart d
  | .outer p => GridExpandedContour.outerPortSlot p

end CanonicalDirectBranchGerm

/-- The direct canonical demand attached at a lens merger. -/
def lensDirectDemand (L : CanonicalLens axis hn2 hT) :
    CanonicalShoreDemand axis n :=
  demandOfStartSlot axis hn2 hT
    (lensMergerBranches axis hn2 hT L).directStart

/-- Recover all honest primal data at the direct merger occurrence. -/
def lensDirectBranchGerm (L : CanonicalLens axis hn2 hT) :
    CanonicalDirectBranchGerm (T := T) :=
  if hq : lensDirectDemand axis hn2 hT L ∈
      CanonicalShoreDemand.directExits axis hn2 T then
    .outer (CanonicalShoreDemand.directExitOuterPort axis hn2 T
      ⟨lensDirectDemand axis hn2 hT L, hq⟩)
  else
    .inward (GridDirectionalDart.retainedCanonicalInwardDart axis hn2 hT
      ⟨lensDirectDemand axis hn2 hT L,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hq⟩⟩)

/-- The recovered direct germ represents exactly the merger start slot. -/
theorem lensDirectBranchGerm_slot
    (L : CanonicalLens axis hn2 hT) :
    (lensDirectBranchGerm axis hn2 hT L).slot =
      (lensMergerBranches axis hn2 hT L).directStart.1 := by
  have hstart :
      startSlot axis hn2 hT (lensDirectDemand axis hn2 hT L) =
        (lensMergerBranches axis hn2 hT L).directStart.1 :=
    startSlot_demandOfStartSlot axis hn2 hT
      (lensMergerBranches axis hn2 hT L).directStart
  unfold lensDirectBranchGerm
  split <;> rename_i hq
  · change GridExpandedContour.outerPortSlot _ = _
    rw [startSlot, dif_pos hq] at hstart
    exact hstart
  · change GridExpandedContour.slotOfDart _ = _
    rw [startSlot, dif_neg hq] at hstart
    exact hstart

/-- Exact endpoint alternative for the direct germ.  An inward germ leaves the
merger vertex in the merger slot direction; an outer germ is based there with
that direction as its outward stub. -/
theorem lensDirectBranchGerm_endpoint_alternative
    (L : CanonicalLens axis hn2 hT) :
    (∃ d : GridDirectionalDart T,
        lensDirectBranchGerm axis hn2 hT L = .inward d ∧
        d.source = (lensMergerBranches axis hn2 hT L).mergerState.1.1.1 ∧
        d.direction = (lensMergerBranches axis hn2 hT L).mergerState.1.1.2) ∨
      (∃ p : GridCotreeOuterPort T,
        lensDirectBranchGerm axis hn2 hT L = .outer p ∧
        p.vertex = (lensMergerBranches axis hn2 hT L).mergerState.1.1.1 ∧
        p.outwardDirection =
          (lensMergerBranches axis hn2 hT L).mergerState.1.1.2) := by
  have hslot := lensDirectBranchGerm_slot axis hn2 hT L
  cases hgerm : lensDirectBranchGerm axis hn2 hT L with
  | inward d =>
      left
      refine ⟨d, rfl, ?_, ?_⟩
      · simpa [hgerm, CanonicalDirectBranchGerm.slot,
          GridExpandedContour.slotOfDart] using congrArg Prod.fst hslot
      · simpa [hgerm, CanonicalDirectBranchGerm.slot,
          GridExpandedContour.slotOfDart] using congrArg Prod.snd hslot
  | outer p =>
      right
      refine ⟨p, rfl, ?_, ?_⟩
      · simpa [hgerm, CanonicalDirectBranchGerm.slot,
          GridExpandedContour.outerPortSlot] using congrArg Prod.fst hslot
      · simpa [hgerm, CanonicalDirectBranchGerm.slot,
          GridExpandedContour.outerPortSlot] using congrArg Prod.snd hslot

/-- Concrete local transition made by the shared predecessor.  Occupied slots
traverse a retained tree edge; unoccupied slots only turn at their vertex. -/
inductive CanonicalSharedBranchGerm where
  | edge (dart : GridDirectionalDart T)
  | turn (slot : GridCompassSlot n n)
      (notOccupied : ¬GridExpandedContour.Occupied (T := T) slot)

/-- Classify the unique shared predecessor transition without pretending that
an in-place turn is a primal edge. -/
def lensSharedBranchGerm (L : CanonicalLens axis hn2 hT) :
    CanonicalSharedBranchGerm (T := T) :=
  let s := (lensMergerBranches axis hn2 hT L).sharedPredecessor.1
  if hs : GridExpandedContour.Occupied (T := T) s then
    .edge (GridDirectionalDart.ofDirectionMem (T := T) s.1 s.2 hs)
  else
    .turn s hs

/-- Exact endpoint alternative for the shared transition: an edge germ enters
the merger vertex, while a turn germ stays at that vertex. -/
theorem lensSharedBranchGerm_endpoint_alternative
    (L : CanonicalLens axis hn2 hT) :
    (∃ d : GridDirectionalDart T,
        lensSharedBranchGerm axis hn2 hT L = .edge d ∧
        d.source =
          (lensMergerBranches axis hn2 hT L).sharedPredecessor.1.1 ∧
        d.target = (lensMergerBranches axis hn2 hT L).mergerState.1.1.1) ∨
      (∃ hs : ¬GridExpandedContour.Occupied (T := T)
          (lensMergerBranches axis hn2 hT L).sharedPredecessor.1,
        lensSharedBranchGerm axis hn2 hT L =
          .turn (lensMergerBranches axis hn2 hT L).sharedPredecessor.1 hs ∧
        (lensMergerBranches axis hn2 hT L).sharedPredecessor.1.1 =
          (lensMergerBranches axis hn2 hT L).mergerState.1.1.1) := by
  let s := (lensMergerBranches axis hn2 hT L).sharedPredecessor.1
  by_cases hs : GridExpandedContour.Occupied (T := T) s
  · left
    let d := GridDirectionalDart.ofDirectionMem (T := T) s.1 s.2 hs
    refine ⟨d, by simp [lensSharedBranchGerm, s, hs, d], rfl, ?_⟩
    have hsucc := lensMergerBranches_sharedPredecessor_succ axis hn2 hT L
    rw [GridExpandedContour.equiv_apply,
      GridExpandedContour.succ_of_occupied hs] at hsucc
    simpa [s] using congrArg Prod.fst hsucc
  · right
    refine ⟨hs, by simp [lensSharedBranchGerm, s, hs], ?_⟩
    have hsucc := lensMergerBranches_sharedPredecessor_succ axis hn2 hT L
    rw [GridExpandedContour.equiv_apply,
      GridExpandedContour.succ_of_not_occupied hs] at hsucc
    simpa [s] using congrArg Prod.fst hsucc

/-- An edge-valued shared germ is based at exactly the shared predecessor
slot, including its compass direction. -/
theorem lensSharedBranchGerm_edge_slot
    (L : CanonicalLens axis hn2 hT) {e : GridDirectionalDart T}
    (he : lensSharedBranchGerm axis hn2 hT L = .edge e) :
    GridExpandedContour.slotOfDart e =
      (lensMergerBranches axis hn2 hT L).sharedPredecessor.1 := by
  unfold lensSharedBranchGerm at he
  dsimp only at he
  split at he
  · rename_i hs
    have hdart : GridDirectionalDart.ofDirectionMem (T := T)
        (lensMergerBranches axis hn2 hT L).sharedPredecessor.1.1
        (lensMergerBranches axis hn2 hT L).sharedPredecessor.1.2 hs = e :=
      CanonicalSharedBranchGerm.edge.inj he
    rw [← hdart]
    rfl
  · contradiction

/-- The direct germ and incoming shared predecessor represent distinct
expanded slots, independently of whether either germ traverses a primal edge. -/
theorem lensBranchGerm_slots_ne
    (L : CanonicalLens axis hn2 hT) :
    (lensMergerBranches axis hn2 hT L).sharedPredecessor.1 ≠
      (lensDirectBranchGerm axis hn2 hT L).slot := by
  rw [lensDirectBranchGerm_slot axis hn2 hT L]
  exact lensMergerBranches_sharedPredecessor_ne_directStart axis hn2 hT L

/-- When both local germs traverse retained edges, their oriented darts are
distinct: the direct dart leaves the merger vertex while the shared dart enters
it.  This does not assert that their longer contour branches are disjoint. -/
theorem lensBranchGerm_darts_ne
    (L : CanonicalLens axis hn2 hT) {d e : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d)
    (he : lensSharedBranchGerm axis hn2 hT L = .edge e) : d ≠ e := by
  have hdslot := lensDirectBranchGerm_slot axis hn2 hT L
  rw [hd] at hdslot
  have hdsource : d.source =
      (lensMergerBranches axis hn2 hT L).mergerState.1.1.1 := by
    simpa [CanonicalDirectBranchGerm.slot,
      GridExpandedContour.slotOfDart] using congrArg Prod.fst hdslot
  rcases lensSharedBranchGerm_endpoint_alternative axis hn2 hT L with
    ⟨e', he', -, hetarget⟩ | ⟨hs, hturn, -⟩
  · have heq : e' = e := by
      exact CanonicalSharedBranchGerm.edge.inj (he'.symm.trans he)
    subst e'
    intro hde
    subst e
    exact (T.ne_of_adj d.adj) (hdsource.trans hetarget.symm)
  · rw [he] at hturn
    contradiction

/-- Stutter-erased retained-tree walk along the complete shared contour suffix
from a lens merger to its outer-port terminal. -/
def lensSharedSuffixWalk (L : CanonicalLens axis hn2 hT) :
    T.Walk (lensMergerBranches axis hn2 hT L).mergerState.1.1.1
      (lensIntervalRegion axis hn2 hT L).terminalSlot.1 := by
  let s := (lensMergerBranches axis hn2 hT L).mergerState.1.1
  let p := GridExpandedContour.iterateWalk (T := T) s L.rank
  have hend : (((GridExpandedContour.equiv (T := T)^[L.rank]) s).1) =
      (lensIntervalRegion axis hn2 hT L).terminalSlot.1 := by
    exact congrArg Prod.fst
      (MarkedCycleFirstStop.ReconvergenceLens.iterate_rank_mergerState_eq_reachedStop L)
  exact p.copy rfl hend

/-- The shared suffix walk uses exactly the retained darts encountered on the
expanded merger-to-terminal interval. -/
theorem edges_lensSharedSuffixWalk (L : CanonicalLens axis hn2 hT) :
    (lensSharedSuffixWalk axis hn2 hT L).edges =
      (GridExpandedContour.occupiedDarts (T := T)
        (lensMergerBranches axis hn2 hT L).mergerState.1.1 L.rank).map
          GridDirectionalDart.edgeSym2 := by
  simp [lensSharedSuffixWalk, GridExpandedContour.edges_iterateWalk]

theorem darts_lensSharedSuffixWalk (L : CanonicalLens axis hn2 hT) :
    (lensSharedSuffixWalk axis hn2 hT L).darts =
      (GridExpandedContour.occupiedDarts (T := T)
        (lensMergerBranches axis hn2 hT L).mergerState.1.1 L.rank).map
          GridExpandedContour.graphDart := by
  simp [lensSharedSuffixWalk, GridExpandedContour.darts_iterateWalk]

/-- Stutter-erased one-step walk from the shared predecessor into the merger.
It is nil precisely in the local-turn case and one edge in the occupied case. -/
def lensSharedPredecessorWalk (L : CanonicalLens axis hn2 hT) :
    T.Walk (lensMergerBranches axis hn2 hT L).sharedPredecessor.1.1
      (lensMergerBranches axis hn2 hT L).mergerState.1.1.1 := by
  let s := (lensMergerBranches axis hn2 hT L).sharedPredecessor.1
  let p := GridExpandedContour.iterateWalk (T := T) s 1
  have hend : (((GridExpandedContour.equiv (T := T)^[1]) s).1) =
      (lensMergerBranches axis hn2 hT L).mergerState.1.1.1 := by
    simpa using congrArg Prod.fst
      (lensMergerBranches_sharedPredecessor_succ axis hn2 hT L)
  exact p.copy rfl hend

/-- Exact occupied-dart trace of the incoming shared predecessor step. -/
theorem edges_lensSharedPredecessorWalk (L : CanonicalLens axis hn2 hT) :
    (lensSharedPredecessorWalk axis hn2 hT L).edges =
      (GridExpandedContour.occupiedDarts (T := T)
        (lensMergerBranches axis hn2 hT L).sharedPredecessor.1 1).map
          GridDirectionalDart.edgeSym2 := by
  simp only [lensSharedPredecessorWalk, Walk.edges_copy,
    GridExpandedContour.edges_iterateWalk]

theorem darts_lensSharedPredecessorWalk (L : CanonicalLens axis hn2 hT) :
    (lensSharedPredecessorWalk axis hn2 hT L).darts =
      (GridExpandedContour.occupiedDarts (T := T)
        (lensMergerBranches axis hn2 hT L).sharedPredecessor.1 1).map
          GridExpandedContour.graphDart := by
  simp only [lensSharedPredecessorWalk, Walk.darts_copy,
    GridExpandedContour.darts_iterateWalk]

/-- A direct inward germ gives one honest retained-tree edge leaving the
merger.  Outer-port direct germs intentionally have no such grid walk. -/
def lensDirectInwardWalk (L : CanonicalLens axis hn2 hT)
    {d : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    T.Walk (lensMergerBranches axis hn2 hT L).mergerState.1.1.1 d.target := by
  have hslot := lensDirectBranchGerm_slot axis hn2 hT L
  rw [hd] at hslot
  have hsource : d.source =
      (lensMergerBranches axis hn2 hT L).mergerState.1.1.1 := by
    simpa [CanonicalDirectBranchGerm.slot,
      GridExpandedContour.slotOfDart] using congrArg Prod.fst hslot
  exact (Walk.cons d.adj Walk.nil).copy hsource rfl

@[simp] theorem edges_lensDirectInwardWalk
    (L : CanonicalLens axis hn2 hT) {d : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    (lensDirectInwardWalk axis hn2 hT L hd).edges = [d.edgeSym2] := by
  dsimp only [lensDirectInwardWalk]
  exact Walk.edges_copy _ _ _

/-- Offset-collar realization of the complete shared suffix.  Unlike the
retained-tree projection, this keeps the two sides of every tree edge apart. -/
def lensSharedSuffixCollarTrace (L : CanonicalLens axis hn2 hT) :
    (gridGraph (GridExpandedContour.collarSize n)
      (GridExpandedContour.collarSize n)).Walk
      (GridExpandedContour.slotPoint
        (lensMergerBranches axis hn2 hT L).mergerState.1.1)
      (GridExpandedContour.slotPoint
        (lensIntervalRegion axis hn2 hT L).terminalSlot) := by
  let s := (lensMergerBranches axis hn2 hT L).mergerState.1.1
  let p := GridExpandedContour.iterateCollarTrace (T := T) s L.rank
  have hend : GridExpandedContour.slotPoint
      ((GridExpandedContour.equiv (T := T)^[L.rank]) s) =
      GridExpandedContour.slotPoint
        (lensIntervalRegion axis hn2 hT L).terminalSlot := by
    exact congrArg GridExpandedContour.slotPoint
      (MarkedCycleFirstStop.ReconvergenceLens.iterate_rank_mergerState_eq_reachedStop L)
  exact p.copy rfl hend

@[simp] theorem length_lensSharedSuffixCollarTrace
    (L : CanonicalLens axis hn2 hT) :
    (lensSharedSuffixCollarTrace axis hn2 hT L).length = 2 * L.rank := by
  simp [lensSharedSuffixCollarTrace]

theorem edges_lensSharedSuffixCollarTrace
    (L : CanonicalLens axis hn2 hT) :
    (lensSharedSuffixCollarTrace axis hn2 hT L).edges =
      GridExpandedContour.collarEdgeList (T := T)
        (lensMergerBranches axis hn2 hT L).mergerState.1.1 L.rank := by
  simp [lensSharedSuffixCollarTrace,
    GridExpandedContour.edges_iterateCollarTrace]

theorem support_lensSharedSuffixCollarTrace
    (L : CanonicalLens axis hn2 hT) :
    (lensSharedSuffixCollarTrace axis hn2 hT L).support =
      GridExpandedContour.collarVertexList (T := T)
        (lensMergerBranches axis hn2 hT L).mergerState.1.1 L.rank := by
  simp [lensSharedSuffixCollarTrace, GridExpandedContour.iterateCollarTrace,
    GridExpandedContour.support_collarTrace]

/-- A first-stop lens rank is strictly shorter than the full expanded-contour
period. -/
theorem lensRank_lt_orderOf (L : CanonicalLens axis hn2 hT) :
    L.rank < orderOf (GridExpandedContour.equiv (T := T)) := by
  let f := GridExpandedContour.equiv (T := T)
  let F := firstStop axis hn2 hT
  change L.rank < orderOf f
  have hcycle := GridExpandedContour.equiv_isCycle_of_spanningSquareTree hn2 hT
  have ho : 0 < orderOf f := by
    rw [hcycle.orderOf]
    exact lt_of_lt_of_le Nat.zero_lt_two hcycle.two_le_card_support
  have hterminalMod :
      ((f : GridCompassSlot n n → GridCompassSlot n n)^[L.rank % orderOf f])
          L.mergerState.1.1 = L.reachedStop.1 := by
    change (f ^ (L.rank % orderOf f)) L.mergerState.1.1 = L.reachedStop.1
    rw [pow_mod_orderOf]
    exact MarkedCycleFirstStop.ReconvergenceLens.iterate_rank_mergerState_eq_reachedStop L
  have hmarked :
      ((f : GridCompassSlot n n → GridCompassSlot n n)^[L.rank % orderOf f])
          L.mergerState.1.1 ∈ F.stop := by
    rw [hterminalMod]
    exact F.terminalState_mem_stop L.ownerStart
  have hminimal := F.distance_minimal L.mergerState.1.1 hmarked
  have hrank : L.rank = F.distance L.mergerState.1.1 := L.rank_eq
  by_contra hnot
  have hmod := Nat.mod_lt L.rank ho
  omega

/-- Complementary global-contour arc from the reached terminal sector back to
the merger sector.  This is the complement in the full contour orbit, not a
smaller lens side. -/
def lensComplementCollarTrace (L : CanonicalLens axis hn2 hT) :
    (gridGraph (GridExpandedContour.collarSize n)
      (GridExpandedContour.collarSize n)).Walk
      (GridExpandedContour.slotPoint
        (lensIntervalRegion axis hn2 hT L).terminalSlot)
      (GridExpandedContour.slotPoint
        (lensMergerBranches axis hn2 hT L).mergerState.1.1) := by
  let f := GridExpandedContour.equiv (T := T)
  let s := (lensMergerBranches axis hn2 hT L).mergerState.1.1
  let t := (lensIntervalRegion axis hn2 hT L).terminalSlot
  let r := orderOf f - L.rank
  let p := GridExpandedContour.collarTrace (T := T) t r
  have ht : t = GridExpandedContour.advance (T := T) s L.rank := by
    rw [GridExpandedContour.advance_eq_iterate]
    exact (MarkedCycleFirstStop.ReconvergenceLens.iterate_rank_mergerState_eq_reachedStop L).symm
  have hperiod : GridExpandedContour.advance (T := T) s (orderOf f) = s := by
    rw [GridExpandedContour.advance_eq_iterate]
    change (f ^ orderOf f) s = s
    rw [pow_orderOf_eq_one]
    rfl
  have hend : GridExpandedContour.advance (T := T) t r = s := by
    rw [ht, GridExpandedContour.advance_add]
    have hrank : L.rank ≤ orderOf f := by
      exact (lensRank_lt_orderOf axis hn2 hT L).le
    rw [show L.rank + r = orderOf f by
      dsimp [r]
      omega]
    exact hperiod
  exact p.copy rfl (congrArg GridExpandedContour.slotPoint hend)

theorem edges_lensComplementCollarTrace
    (L : CanonicalLens axis hn2 hT) :
    (lensComplementCollarTrace axis hn2 hT L).edges =
      GridExpandedContour.collarEdgeList (T := T)
        (lensIntervalRegion axis hn2 hT L).terminalSlot
        (orderOf (GridExpandedContour.equiv (T := T)) - L.rank) := by
  simp [lensComplementCollarTrace, GridExpandedContour.edges_collarTrace]

theorem support_lensComplementCollarTrace
    (L : CanonicalLens axis hn2 hT) :
    (lensComplementCollarTrace axis hn2 hT L).support =
      GridExpandedContour.collarVertexList (T := T)
        (lensIntervalRegion axis hn2 hT L).terminalSlot
        (orderOf (GridExpandedContour.equiv (T := T)) - L.rank) := by
  simp [lensComplementCollarTrace, GridExpandedContour.support_collarTrace]

/-- The shared suffix followed by its complement is a closed walk around the
entire expanded contour. -/
def lensGlobalContourCycle (L : CanonicalLens axis hn2 hT) :
    (gridGraph (GridExpandedContour.collarSize n)
      (GridExpandedContour.collarSize n)).Walk
      (GridExpandedContour.slotPoint
        (lensMergerBranches axis hn2 hT L).mergerState.1.1)
      (GridExpandedContour.slotPoint
        (lensMergerBranches axis hn2 hT L).mergerState.1.1) :=
  (lensSharedSuffixCollarTrace axis hn2 hT L).append
    (lensComplementCollarTrace axis hn2 hT L)

theorem edges_lensGlobalContourCycle
    (L : CanonicalLens axis hn2 hT) :
    (lensGlobalContourCycle axis hn2 hT L).edges =
      GridExpandedContour.collarEdgeList (T := T)
        (lensMergerBranches axis hn2 hT L).mergerState.1.1
        (orderOf (GridExpandedContour.equiv (T := T))) := by
  let f := GridExpandedContour.equiv (T := T)
  let s := (lensMergerBranches axis hn2 hT L).mergerState.1.1
  have ht : (lensIntervalRegion axis hn2 hT L).terminalSlot =
      GridExpandedContour.advance (T := T) s L.rank := by
    rw [GridExpandedContour.advance_eq_iterate]
    exact (MarkedCycleFirstStop.ReconvergenceLens.iterate_rank_mergerState_eq_reachedStop L).symm
  rw [lensGlobalContourCycle, Walk.edges_append,
    edges_lensSharedSuffixCollarTrace, edges_lensComplementCollarTrace, ht]
  rw [← GridExpandedContour.collarEdgeList_add]
  congr 2
  have hrank := lensRank_lt_orderOf axis hn2 hT L
  omega

/-- The two complementary global-orbit arcs have disjoint edge sets. -/
theorem lensGlobalContourArc_edges_disjoint
    (L : CanonicalLens axis hn2 hT) :
    List.Disjoint
      (GridExpandedContour.collarEdgeList (T := T)
        (lensMergerBranches axis hn2 hT L).mergerState.1.1 L.rank)
      (GridExpandedContour.collarEdgeList (T := T)
        (lensIntervalRegion axis hn2 hT L).terminalSlot
        (orderOf (GridExpandedContour.equiv (T := T)) - L.rank)) := by
  let f := GridExpandedContour.equiv (T := T)
  let s := (lensMergerBranches axis hn2 hT L).mergerState.1.1
  let o := orderOf f
  have hcycle := GridExpandedContour.equiv_isCycle_of_spanningSquareTree hn2 hT
  have hs : f s ≠ s := by
    simpa only [f, GridExpandedContour.equiv_apply] using
      GridExpandedContour.succ_ne (T := T) s
  have hrank : L.rank < o := by
    simpa [f, o] using lensRank_lt_orderOf axis hn2 hT L
  have ho : 0 < o := lt_of_le_of_lt (Nat.zero_le _) hrank
  have hperiod : GridExpandedContour.advance (T := T) s o = s := by
    rw [GridExpandedContour.advance_eq_iterate]
    change (f ^ o) s = s
    rw [show o = orderOf f by rfl, pow_orderOf_eq_one]
    rfl
  have ht : (lensIntervalRegion axis hn2 hT L).terminalSlot =
      GridExpandedContour.advance (T := T) s L.rank := by
    rw [GridExpandedContour.advance_eq_iterate]
    exact (MarkedCycleFirstStop.ReconvergenceLens.iterate_rank_mergerState_eq_reachedStop L).symm
  rw [List.disjoint_left]
  intro e he₁ he₂
  rcases (GridExpandedContour.mem_collarEdgeList_iff (T := T)
      s L.rank e).1 he₁ with ⟨i, hi, b, hib⟩
  rcases (GridExpandedContour.mem_collarEdgeList_iff (T := T)
      (lensIntervalRegion axis hn2 hT L).terminalSlot (o - L.rank) e).1 he₂ with
    ⟨j, hj, c, hjc⟩
  have hpairs := GridExpandedContour.localEdge_injective (T := T)
    (a₁ := (GridExpandedContour.advance (T := T) s i, b))
    (a₂ := (GridExpandedContour.advance (T := T)
      (lensIntervalRegion axis hn2 hT L).terminalSlot j, c))
    (hib.symm.trans hjc)
  have hslot := congrArg Prod.fst hpairs
  rw [ht, GridExpandedContour.advance_add] at hslot
  have happ : (f ^ i) s = (f ^ (L.rank + j)) s := by
    simpa only [GridExpandedContour.advance_eq_iterate, f, Equiv.Perm.coe_pow] using hslot
  have hpowers : f ^ i = f ^ (L.rank + j) :=
    hcycle.pow_eq_pow_iff.mpr ⟨s, hs, happ⟩
  have hiO : i < o := lt_trans hi hrank
  have hjO : L.rank + j < o := by omega
  have hij := pow_injOn_Iio_orderOf hiO hjO hpowers
  omega

/-- The two global-orbit arcs share no collar vertex except their merger and
terminal endpoints. -/
theorem lensGlobalContourArc_support_intersection
    (L : CanonicalLens axis hn2 hT) {x}
    (hx₁ : x ∈ (lensSharedSuffixCollarTrace axis hn2 hT L).support)
    (hx₂ : x ∈ (lensComplementCollarTrace axis hn2 hT L).support) :
    x = GridExpandedContour.slotPoint
        (lensMergerBranches axis hn2 hT L).mergerState.1.1 ∨
      x = GridExpandedContour.slotPoint
        (lensIntervalRegion axis hn2 hT L).terminalSlot := by
  let f := GridExpandedContour.equiv (T := T)
  let s := (lensMergerBranches axis hn2 hT L).mergerState.1.1
  let o := orderOf f
  have hcycle := GridExpandedContour.equiv_isCycle_of_spanningSquareTree hn2 hT
  have hs : f s ≠ s := by
    simpa only [f, GridExpandedContour.equiv_apply] using
      GridExpandedContour.succ_ne (T := T) s
  have hrank : L.rank < o := by
    simpa [f, o] using lensRank_lt_orderOf axis hn2 hT L
  have ho : 0 < o := lt_of_le_of_lt (Nat.zero_le _) hrank
  have hperiod : GridExpandedContour.advance (T := T) s o = s := by
    rw [GridExpandedContour.advance_eq_iterate]
    change (f ^ o) s = s
    rw [show o = orderOf f by rfl, pow_orderOf_eq_one]
    rfl
  have ht : (lensIntervalRegion axis hn2 hT L).terminalSlot =
      GridExpandedContour.advance (T := T) s L.rank := by
    rw [GridExpandedContour.advance_eq_iterate]
    exact (MarkedCycleFirstStop.ReconvergenceLens.iterate_rank_mergerState_eq_reachedStop L).symm
  rw [support_lensSharedSuffixCollarTrace] at hx₁
  rw [support_lensComplementCollarTrace] at hx₂
  rcases (GridExpandedContour.mem_collarVertexList_iff (T := T)
      s L.rank x).1 hx₁ with ⟨i, hi, hxi⟩ | ⟨i, hi, hxi⟩
  · rcases (GridExpandedContour.mem_collarVertexList_iff (T := T)
        (lensIntervalRegion axis hn2 hT L).terminalSlot (o - L.rank) x).1 hx₂ with
      ⟨j, hj, hxj⟩ | ⟨j, hj, hxj⟩
    · have hslot := GridExpandedContour.slotPoint_injective (hxi.symm.trans hxj)
      rw [ht, GridExpandedContour.advance_add] at hslot
      by_cases hjEnd : L.rank + j = o
      · left
        rw [hxi]
        congr 1
        have his : GridExpandedContour.advance (T := T) s i = s := by
          rw [hslot, hjEnd]
          exact hperiod
        have happ : (f ^ i) s = (f ^ 0) s := by
          simpa [GridExpandedContour.advance_eq_iterate, f, Equiv.Perm.coe_pow] using his
        have hpowers := hcycle.pow_eq_pow_iff.mpr ⟨s, hs, happ⟩
        have hi0 := pow_injOn_Iio_orderOf (lt_of_le_of_lt hi hrank) ho hpowers
        rw [hi0]
        rfl
      · right
        rw [hxi, ht]
        congr 1
        have hsumle : L.rank + j ≤ o := by omega
        have hjLt : L.rank + j < o := lt_of_le_of_ne hsumle hjEnd
        have happ : (f ^ i) s = (f ^ (L.rank + j)) s := by
          simpa only [GridExpandedContour.advance_eq_iterate, f, Equiv.Perm.coe_pow] using hslot
        have hpowers := hcycle.pow_eq_pow_iff.mpr ⟨s, hs, happ⟩
        have hij := pow_injOn_Iio_orderOf (lt_of_le_of_lt hi hrank) hjLt hpowers
        have hirank : i = L.rank := by omega
        rw [hirank]
    · exact (GridExpandedContour.segmentMidpoint_ne_slotPoint (T := T)
        (GridExpandedContour.advance (T := T)
          (lensIntervalRegion axis hn2 hT L).terminalSlot j)
        (GridExpandedContour.advance (T := T) s i) (hxi.symm.trans hxj).symm).elim
  · rcases (GridExpandedContour.mem_collarVertexList_iff (T := T)
        (lensIntervalRegion axis hn2 hT L).terminalSlot (o - L.rank) x).1 hx₂ with
      ⟨j, hj, hxj⟩ | ⟨j, hj, hxj⟩
    · exact (GridExpandedContour.segmentMidpoint_ne_slotPoint (T := T)
        (GridExpandedContour.advance (T := T) s i)
        (GridExpandedContour.advance (T := T)
          (lensIntervalRegion axis hn2 hT L).terminalSlot j)
        (hxi.symm.trans hxj)).elim
    · have hslot := GridExpandedContour.segmentMidpoint_injective (T := T)
          (hxi.symm.trans hxj)
      rw [ht, GridExpandedContour.advance_add] at hslot
      have hjLt : L.rank + j < o := by omega
      have happ : (f ^ i) s = (f ^ (L.rank + j)) s := by
        simpa only [GridExpandedContour.advance_eq_iterate, f, Equiv.Perm.coe_pow] using hslot
      have hpowers := hcycle.pow_eq_pow_iff.mpr ⟨s, hs, happ⟩
      have hij := pow_injOn_Iio_orderOf (lt_trans hi hrank) hjLt hpowers
      omega

/-- The appended lens suffix and complement are exactly the full global collar
cycle based at the merger. -/
theorem lensGlobalContourCycle_eq_orderCollarWalk
    (L : CanonicalLens axis hn2 hT) :
    lensGlobalContourCycle axis hn2 hT L =
      GridExpandedContour.spanningTreeCollarCycle hn2 hT
        (lensMergerBranches axis hn2 hT L).mergerState.1.1 := by
  apply Walk.edges_injective
  rw [edges_lensGlobalContourCycle]
  simp [GridExpandedContour.orderCollarWalk,
    GridExpandedContour.spanningTreeCollarCycle,
    GridExpandedContour.orbitCollarWalk,
    GridExpandedContour.edges_collarTrace]

theorem lensGlobalContourCycle_isCycle
    (L : CanonicalLens axis hn2 hT) :
    (lensGlobalContourCycle axis hn2 hT L).IsCycle := by
  rw [lensGlobalContourCycle_eq_orderCollarWalk]
  exact GridExpandedContour.spanningTreeCollarCycle_isCycle hn2 hT _

/-- Face carrier of the global contour partition based at a lens merger.  This
is not a smaller lens region. -/
def lensGlobalContourInteriorFaces (L : CanonicalLens axis hn2 hT) :
    Finset (GridFace (GridExpandedContour.collarSize n)
      (GridExpandedContour.collarSize n)) :=
  cycleInteriorFaces (lensGlobalContourCycle axis hn2 hT L)

@[simp] theorem out_not_mem_lensGlobalContourInteriorFaces
    (L : CanonicalLens axis hn2 hT) :
    GridFace.out ∉ lensGlobalContourInteriorFaces axis hn2 hT L :=
  out_not_mem_cycleInteriorFaces _

/-- The incoming shared predecessor has one continuous two-edge collar segment
ending at the merger sector. -/
def lensSharedPredecessorCollarSegment (L : CanonicalLens axis hn2 hT) :
    (gridGraph (GridExpandedContour.collarSize n)
      (GridExpandedContour.collarSize n)).Walk
      (GridExpandedContour.slotPoint
        (lensMergerBranches axis hn2 hT L).sharedPredecessor.1)
      (GridExpandedContour.slotPoint
        (lensMergerBranches axis hn2 hT L).mergerState.1.1) := by
  let s := (lensMergerBranches axis hn2 hT L).sharedPredecessor.1
  let p := GridExpandedContour.successorSegment (T := T) s
  exact p.copy rfl (congrArg GridExpandedContour.slotPoint
    (lensMergerBranches_sharedPredecessor_succ axis hn2 hT L))

@[simp] theorem length_lensSharedPredecessorCollarSegment
    (L : CanonicalLens axis hn2 hT) :
    (lensSharedPredecessorCollarSegment axis hn2 hT L).length = 2 := by
  simp [lensSharedPredecessorCollarSegment]

/-- Both direct-germ cases begin at exactly the merger sector in the offset
collar. -/
theorem lensDirectBranchGerm_slotPoint_eq_merger
    (L : CanonicalLens axis hn2 hT) :
    GridExpandedContour.slotPoint
        (lensDirectBranchGerm axis hn2 hT L).slot =
      GridExpandedContour.slotPoint
        (lensMergerBranches axis hn2 hT L).mergerState.1.1 := by
  apply congrArg GridExpandedContour.slotPoint
  rw [lensDirectBranchGerm_slot,
    lensMergerBranches_directStart_value]

/-- Honest case split for a prospective direct closing germ.  Inward and outer
germs both identify the merger sector; neither supplies a distinct second
collar endpoint. -/
theorem lensDirectBranchGerm_collar_case
    (L : CanonicalLens axis hn2 hT) :
    (∃ d : GridDirectionalDart T,
        lensDirectBranchGerm axis hn2 hT L = .inward d ∧
        GridExpandedContour.slotPoint
            (GridExpandedContour.slotOfDart d) =
          GridExpandedContour.slotPoint
            (lensMergerBranches axis hn2 hT L).mergerState.1.1) ∨
      (∃ p : GridCotreeOuterPort T,
        lensDirectBranchGerm axis hn2 hT L = .outer p ∧
        GridExpandedContour.slotPoint
            (GridExpandedContour.outerPortSlot p) =
          GridExpandedContour.slotPoint
            (lensMergerBranches axis hn2 hT L).mergerState.1.1) := by
  cases h : lensDirectBranchGerm axis hn2 hT L with
  | inward d =>
      left
      exact ⟨d, rfl, by simpa [h, CanonicalDirectBranchGerm.slot] using
        lensDirectBranchGerm_slotPoint_eq_merger axis hn2 hT L⟩
  | outer p =>
      right
      exact ⟨p, rfl, by simpa [h, CanonicalDirectBranchGerm.slot] using
        lensDirectBranchGerm_slotPoint_eq_merger axis hn2 hT L⟩

/-- The direct germ's first collar segment is the first segment of the shared
merger suffix, not an alternative closing arc. -/
theorem support_lensDirectBranchGerm_successorSegment
    (L : CanonicalLens axis hn2 hT) :
    (GridExpandedContour.successorSegment (T := T)
      (lensDirectBranchGerm axis hn2 hT L).slot).support =
      [GridExpandedContour.slotPoint
          (lensMergerBranches axis hn2 hT L).mergerState.1.1,
        GridExpandedContour.segmentMidpoint (T := T)
          (lensMergerBranches axis hn2 hT L).mergerState.1.1,
        GridExpandedContour.slotPoint (GridExpandedContour.succ (T := T)
          (lensMergerBranches axis hn2 hT L).mergerState.1.1)] := by
  rw [GridExpandedContour.support_successorSegment]
  rw [lensDirectBranchGerm_slot axis hn2 hT L,
    lensMergerBranches_directStart_value axis hn2 hT L]

/-- Minimal additional occurrence history needed for a genuine smaller lens
arc.  Existing direct germs provide only the merger endpoint, so a future
geometric construction must supply a distinct pre-start collar occurrence and
an alternate terminal-to-merger path carrying it. -/
structure CanonicalLensPreStartHistory (L : CanonicalLens axis hn2 hT) where
  preStartPoint : GridVertex (GridExpandedContour.collarSize n)
    (GridExpandedContour.collarSize n)
  preStart_ne_merger : preStartPoint ≠ GridExpandedContour.slotPoint
    (lensMergerBranches axis hn2 hT L).mergerState.1.1
  closingWalk : (gridGraph (GridExpandedContour.collarSize n)
    (GridExpandedContour.collarSize n)).Walk
      (GridExpandedContour.slotPoint
        (lensIntervalRegion axis hn2 hT L).terminalSlot)
      (GridExpandedContour.slotPoint
        (lensMergerBranches axis hn2 hT L).mergerState.1.1)
  closing_isPath : closingWalk.IsPath
  preStart_mem : preStartPoint ∈ closingWalk.support
  edges_disjoint : List.Disjoint
    (lensSharedSuffixCollarTrace axis hn2 hT L).edges closingWalk.edges
  support_intersection : ∀ {x},
    x ∈ (lensSharedSuffixCollarTrace axis hn2 hT L).support →
    x ∈ closingWalk.support →
    x = GridExpandedContour.slotPoint
        (lensMergerBranches axis hn2 hT L).mergerState.1.1 ∨
      x = GridExpandedContour.slotPoint
        (lensIntervalRegion axis hn2 hT L).terminalSlot

/-- An inward direct germ forces an unmarked merger and hence positive suffix
rank. -/
theorem lensRank_pos_of_direct_inward
    (L : CanonicalLens axis hn2 hT) {d : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d) : 0 < L.rank := by
  have hslot := lensDirectBranchGerm_slot axis hn2 hT L
  rw [hd, lensMergerBranches_directStart_value] at hslot
  have hoccupied : GridExpandedContour.Occupied (T := T) L.mergerState.1.1 := by
    change GridExpandedContour.slotOfDart d = L.mergerState.1.1 at hslot
    rw [← hslot]
    exact GridExpandedContour.occupied_slotOfDart d
  have hnotMarked : L.mergerState.1.1 ∉ markedSlots (T := T) := by
    intro hm
    rcases Finset.mem_image.mp hm with ⟨p, -, hp⟩
    apply GridExpandedContour.outerPortSlot_not_occupied p
    rw [hp]
    exact hoccupied
  have hnotStop : L.mergerState.1.1 ∉
      (firstStop axis hn2 hT).stop := by
    exact hnotMarked
  rw [L.rank_eq]
  exact Nat.pos_of_ne_zero fun hz =>
    hnotStop (((firstStop axis hn2 hT).distance_eq_zero_iff _).mp hz)

/-- Orbit injectivity on the closed terminal-to-merger complementary interval,
provided the shared suffix is nonempty. -/
theorem lensComplement_advance_injective
    (L : CanonicalLens axis hn2 hT) (hrank : 0 < L.rank) :
    ∀ i j,
      i ≤ orderOf (GridExpandedContour.equiv (T := T)) - L.rank →
      j ≤ orderOf (GridExpandedContour.equiv (T := T)) - L.rank →
      GridExpandedContour.advance (T := T)
          (lensIntervalRegion axis hn2 hT L).terminalSlot i =
        GridExpandedContour.advance (T := T)
          (lensIntervalRegion axis hn2 hT L).terminalSlot j →
      i = j := by
  let f := GridExpandedContour.equiv (T := T)
  let s := (lensMergerBranches axis hn2 hT L).mergerState.1.1
  let o := orderOf f
  have hcycle := GridExpandedContour.equiv_isCycle_of_spanningSquareTree hn2 hT
  have hs : f s ≠ s := by
    simpa only [f, GridExpandedContour.equiv_apply] using
      GridExpandedContour.succ_ne (T := T) s
  have hrankO : L.rank < o := by
    simpa [f, o] using lensRank_lt_orderOf axis hn2 hT L
  have ht : (lensIntervalRegion axis hn2 hT L).terminalSlot =
      GridExpandedContour.advance (T := T) s L.rank := by
    rw [GridExpandedContour.advance_eq_iterate]
    exact (MarkedCycleFirstStop.ReconvergenceLens.iterate_rank_mergerState_eq_reachedStop L).symm
  intro i j hi hj hij
  change i ≤ o - L.rank at hi
  change j ≤ o - L.rank at hj
  rw [ht, GridExpandedContour.advance_add,
    GridExpandedContour.advance_add] at hij
  have hiO : L.rank + i ≤ o := by omega
  have hjO : L.rank + j ≤ o := by omega
  by_cases hiEnd : L.rank + i = o
  · by_cases hjEnd : L.rank + j = o
    · omega
    · have hjLt : L.rank + j < o := lt_of_le_of_ne hjO hjEnd
      have hperiod : GridExpandedContour.advance (T := T) s o = s := by
        rw [GridExpandedContour.advance_eq_iterate]
        change (f ^ o) s = s
        rw [show o = orderOf f by rfl, pow_orderOf_eq_one]
        rfl
      have hj0 : GridExpandedContour.advance (T := T) s (L.rank + j) =
          GridExpandedContour.advance (T := T) s 0 := by
        change GridExpandedContour.advance (T := T) s (L.rank + j) = s
        simpa only [hiEnd, hperiod] using hij.symm
      have happ : (f ^ (L.rank + j)) s = (f ^ 0) s := by
        simpa [GridExpandedContour.advance_eq_iterate, f, Equiv.Perm.coe_pow] using hj0
      have hpowers := hcycle.pow_eq_pow_iff.mpr ⟨s, hs, happ⟩
      have := pow_injOn_Iio_orderOf hjLt
        (lt_of_le_of_lt (Nat.zero_le _) hrankO) hpowers
      omega
  · by_cases hjEnd : L.rank + j = o
    · have hiLt : L.rank + i < o := lt_of_le_of_ne hiO hiEnd
      have hperiod : GridExpandedContour.advance (T := T) s o = s := by
        rw [GridExpandedContour.advance_eq_iterate]
        change (f ^ o) s = s
        rw [show o = orderOf f by rfl, pow_orderOf_eq_one]
        rfl
      have hi0 : GridExpandedContour.advance (T := T) s (L.rank + i) =
          GridExpandedContour.advance (T := T) s 0 := by
        change GridExpandedContour.advance (T := T) s (L.rank + i) = s
        simpa only [hjEnd, hperiod] using hij
      have happ : (f ^ (L.rank + i)) s = (f ^ 0) s := by
        simpa [GridExpandedContour.advance_eq_iterate, f, Equiv.Perm.coe_pow] using hi0
      have hpowers := hcycle.pow_eq_pow_iff.mpr ⟨s, hs, happ⟩
      have := pow_injOn_Iio_orderOf hiLt
        (lt_of_le_of_lt (Nat.zero_le _) hrankO) hpowers
      omega
    · have hiLt : L.rank + i < o := lt_of_le_of_ne hiO hiEnd
      have hjLt : L.rank + j < o := lt_of_le_of_ne hjO hjEnd
      have happ : (f ^ (L.rank + i)) s = (f ^ (L.rank + j)) s := by
        simpa only [GridExpandedContour.advance_eq_iterate, f, Equiv.Perm.coe_pow] using hij
      have hpowers := hcycle.pow_eq_pow_iff.mpr ⟨s, hs, happ⟩
      have := pow_injOn_Iio_orderOf hiLt hjLt hpowers
      omega

theorem lensComplementCollarTrace_isPath
    (L : CanonicalLens axis hn2 hT) (hrank : 0 < L.rank) :
    (lensComplementCollarTrace axis hn2 hT L).IsPath := by
  unfold lensComplementCollarTrace
  simp only [Walk.isPath_copy]
  apply GridExpandedContour.collarTrace_isPath_of_advance_injective
  exact lensComplement_advance_injective axis hn2 hT L hrank

/-- Exact condition under which the reverse inward-dart occurrence lies
strictly inside the global complement and can serve as nontrivial pre-start
history. -/
structure InwardReverseHistoryData
    (L : CanonicalLens axis hn2 hT) where
  dart : GridDirectionalDart T
  direct_eq : lensDirectBranchGerm axis hn2 hT L = .inward dart
  index : Nat
  index_lt : index < orderOf (GridExpandedContour.equiv (T := T)) - L.rank
  advance_eq_reverse : GridExpandedContour.advance (T := T)
    (lensIntervalRegion axis hn2 hT L).terminalSlot index =
      GridExpandedContour.slotOfDart dart.reverse

/-- Residual ordering in which the reverse inward-dart occurrence is reached
before the first outer mark, on the shared suffix itself. -/
structure InwardReverseOnSharedData
    (L : CanonicalLens axis hn2 hT) where
  dart : GridDirectionalDart T
  direct_eq : lensDirectBranchGerm axis hn2 hT L = .inward dart
  index : Nat
  index_pos : 0 < index
  index_lt_rank : index < L.rank
  advance_eq_reverse : GridExpandedContour.advance (T := T)
    (lensMergerBranches axis hn2 hT L).mergerState.1.1 index =
      GridExpandedContour.slotOfDart dart.reverse

/-- Exact universal ordering dichotomy for the reverse inward dart.  Existing
shore facts do not eliminate the shared-suffix alternative. -/
def inwardReverseOrdering
    (L : CanonicalLens axis hn2 hT) {d : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    InwardReverseOnSharedData axis hn2 hT L ⊕
      InwardReverseHistoryData axis hn2 hT L := by
  classical
  let f := GridExpandedContour.equiv (T := T)
  let s := (lensMergerBranches axis hn2 hT L).mergerState.1.1
  let z := GridExpandedContour.slotOfDart d.reverse
  let o := orderOf f
  have hsame := GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
    hn2 hT s z
  let k := Nat.find hsame.exists_pow_eq'
  have hkO := (Nat.find_spec hsame.exists_pow_eq').1
  have hk := (Nat.find_spec hsame.exists_pow_eq').2
  have hkAdvance : GridExpandedContour.advance (T := T) s k = z := by
    rw [GridExpandedContour.advance_eq_iterate]
    exact hk
  have hdslot := lensDirectBranchGerm_slot axis hn2 hT L
  rw [hd, lensMergerBranches_directStart_value] at hdslot
  change GridExpandedContour.slotOfDart d = L.mergerState.1.1 at hdslot
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkzero
    have hz : GridExpandedContour.slotOfDart d.reverse =
        GridExpandedContour.slotOfDart d := by
      change z = GridExpandedContour.slotOfDart d
      calc
        z = s := by rw [← hkAdvance, hkzero]; rfl
        _ = GridExpandedContour.slotOfDart d := by
          simpa only [s, lensMergerBranches] using hdslot.symm
    have hdarts := GridExpandedContour.slotOfDart_injective hz
    have hv : d.target = d.source := by
      simpa [GridDirectionalDart.reverse] using
        congrArg GridDirectionalDart.source hdarts
    exact T.loopless.irrefl d.source (hv ▸ d.adj)
  have hkNeRank : k ≠ L.rank := by
    intro hkr
    have hzterminal : z = (lensIntervalRegion axis hn2 hT L).terminalSlot := by
      rw [← hkAdvance, hkr, GridExpandedContour.advance_eq_iterate]
      exact MarkedCycleFirstStop.ReconvergenceLens.iterate_rank_mergerState_eq_reachedStop L
    have hzOccupied : GridExpandedContour.Occupied (T := T) z := by
      exact GridExpandedContour.occupied_slotOfDart d.reverse
    have hterminalNot : ¬GridExpandedContour.Occupied (T := T)
        (lensIntervalRegion axis hn2 hT L).terminalSlot := by
      rw [lensIntervalRegion_terminalSlot axis hn2 hT L]
      exact GridExpandedContour.outerPortSlot_not_occupied _
    exact hterminalNot (hzterminal ▸ hzOccupied)
  if hbefore : k < L.rank then
    exact Sum.inl
      { dart := d
        direct_eq := hd
        index := k
        index_pos := hkpos
        index_lt_rank := hbefore
        advance_eq_reverse := hkAdvance }
  else
    have hafter : L.rank < k := (lt_or_gt_of_ne hkNeRank).resolve_left hbefore
    let j := k - L.rank
    have ht : (lensIntervalRegion axis hn2 hT L).terminalSlot =
        GridExpandedContour.advance (T := T) s L.rank := by
      rw [GridExpandedContour.advance_eq_iterate]
      exact (MarkedCycleFirstStop.ReconvergenceLens.iterate_rank_mergerState_eq_reachedStop L).symm
    exact Sum.inr
      { dart := d
        direct_eq := hd
        index := j
        index_lt := by
          dsimp [j, o] at *
          omega
        advance_eq_reverse := by
          rw [ht, GridExpandedContour.advance_add]
          rw [show L.rank + j = k by dsimp [j]; omega]
          exact hkAdvance }

/-- Eligible inward lenses obtain a genuine pre-start occurrence from the
reverse side of their retained inward edge. -/
def inwardReversePreStartHistory
    (L : CanonicalLens axis hn2 hT)
    (data : InwardReverseHistoryData axis hn2 hT L) :
    CanonicalLensPreStartHistory axis hn2 hT L := by
  let d := data.dart
  let j := data.index
  have hd := data.direct_eq
  have hj := data.index_lt
  have hjslot := data.advance_eq_reverse
  let r := orderOf (GridExpandedContour.equiv (T := T)) - L.rank
  let pre := GridExpandedContour.slotPoint
    (GridExpandedContour.slotOfDart d.reverse)
  have hrank := lensRank_pos_of_direct_inward axis hn2 hT L hd
  refine
    { preStartPoint := pre
      preStart_ne_merger := ?_
      closingWalk := lensComplementCollarTrace axis hn2 hT L
      closing_isPath := lensComplementCollarTrace_isPath axis hn2 hT L hrank
      preStart_mem := ?_
      edges_disjoint := by
        rw [edges_lensSharedSuffixCollarTrace,
          edges_lensComplementCollarTrace]
        exact lensGlobalContourArc_edges_disjoint axis hn2 hT L
      support_intersection := fun hx₁ hx₂ =>
        lensGlobalContourArc_support_intersection axis hn2 hT L hx₁ hx₂ }
  · intro heq
    change GridExpandedContour.slotPoint
        (GridExpandedContour.slotOfDart d.reverse) =
      GridExpandedContour.slotPoint
        (lensMergerBranches axis hn2 hT L).mergerState.1.1 at heq
    have hrev := GridExpandedContour.slotPoint_injective heq
    have hdslot := lensDirectBranchGerm_slot axis hn2 hT L
    rw [hd, lensMergerBranches_directStart_value] at hdslot
    change GridExpandedContour.slotOfDart d = L.mergerState.1.1 at hdslot
    have hslots : GridExpandedContour.slotOfDart d.reverse =
        GridExpandedContour.slotOfDart d := hrev.trans hdslot.symm
    have hdarts := GridExpandedContour.slotOfDart_injective hslots
    have hv : d.target = d.source := by
      simpa [GridDirectionalDart.reverse] using
        congrArg GridDirectionalDart.source hdarts
    exact T.loopless.irrefl d.source (hv ▸ d.adj)
  · rw [support_lensComplementCollarTrace]
    apply (GridExpandedContour.mem_collarVertexList_iff (T := T) _ r pre).2
    exact Or.inl ⟨j, by omega, by rw [hjslot]⟩

/-- Universal constructive result for inward germs: either the reverse dart is
on the shared suffix, or it yields the complement pre-start certificate. -/
def inwardPreStartHistoryOrShared
    (L : CanonicalLens axis hn2 hT) {d : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    InwardReverseOnSharedData axis hn2 hT L ⊕
      CanonicalLensPreStartHistory axis hn2 hT L :=
  match inwardReverseOrdering axis hn2 hT L hd with
  | .inl data => .inl data
  | .inr data => .inr (inwardReversePreStartHistory axis hn2 hT L data)

theorem reversePoint_mem_sharedSuffix_of_data
    (L : CanonicalLens axis hn2 hT)
    (data : InwardReverseOnSharedData axis hn2 hT L) :
    GridExpandedContour.slotPoint
        (GridExpandedContour.slotOfDart data.dart.reverse) ∈
      (lensSharedSuffixCollarTrace axis hn2 hT L).support := by
  rw [support_lensSharedSuffixCollarTrace]
  apply (GridExpandedContour.mem_collarVertexList_iff (T := T) _ L.rank _).2
  exact Or.inl ⟨data.index, data.index_lt_rank.le, by
    rw [data.advance_eq_reverse]⟩

/-! ## Genuine local fundamental-shore closures -/

/-- First forward expanded-contour occurrence of the reverse orientation of a
retained dart. -/
noncomputable def inwardShoreContourRank (d : GridDirectionalDart T) : Nat :=
  Nat.find
    (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT
      (GridExpandedContour.slotOfDart d)
      (GridExpandedContour.slotOfDart d.reverse)).exists_pow_eq'

theorem inwardShoreContourRank_lt_orderOf (d : GridDirectionalDart T) :
    inwardShoreContourRank hn2 hT d <
      orderOf (GridExpandedContour.equiv (T := T)) :=
  (Nat.find_spec
    (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT
      (GridExpandedContour.slotOfDart d)
      (GridExpandedContour.slotOfDart d.reverse)).exists_pow_eq').1

theorem advance_inwardShoreContourRank (d : GridDirectionalDart T) :
    GridExpandedContour.advance (T := T) (GridExpandedContour.slotOfDart d)
        (inwardShoreContourRank hn2 hT d) =
      GridExpandedContour.slotOfDart d.reverse := by
  rw [GridExpandedContour.advance_eq_iterate]
  exact (Nat.find_spec
    (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT
      (GridExpandedContour.slotOfDart d)
      (GridExpandedContour.slotOfDart d.reverse)).exists_pow_eq').2

theorem inwardShoreContourRank_pos (d : GridDirectionalDart T) :
    0 < inwardShoreContourRank hn2 hT d := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hslots := advance_inwardShoreContourRank hn2 hT d
  rw [hz] at hslots
  exact GridExpandedContour.slotPoint_dart_ne_reverse (T := T) d
    (congrArg GridExpandedContour.slotPoint hslots)

/-- Forward collar arc entered through `d` and ending at the unique reverse
orientation.  This is independent of every first-stop terminal. -/
def inwardShoreContourArc (d : GridDirectionalDart T) :
    (gridGraph (GridExpandedContour.collarSize n)
      (GridExpandedContour.collarSize n)).Walk
      (GridExpandedContour.slotPoint (GridExpandedContour.slotOfDart d))
      (GridExpandedContour.slotPoint
        (GridExpandedContour.slotOfDart d.reverse)) :=
  (GridExpandedContour.collarTrace (T := T)
      (GridExpandedContour.slotOfDart d)
      (inwardShoreContourRank hn2 hT d)).copy rfl
    (congrArg GridExpandedContour.slotPoint
      (advance_inwardShoreContourRank hn2 hT d))

theorem support_inwardShoreContourArc (d : GridDirectionalDart T) :
    (inwardShoreContourArc hn2 hT d).support =
      GridExpandedContour.collarVertexList (T := T)
        (GridExpandedContour.slotOfDart d)
        (inwardShoreContourRank hn2 hT d) := by
  simp [inwardShoreContourArc, GridExpandedContour.support_collarTrace]

theorem edges_inwardShoreContourArc (d : GridDirectionalDart T) :
    (inwardShoreContourArc hn2 hT d).edges =
      GridExpandedContour.collarEdgeList (T := T)
        (GridExpandedContour.slotOfDart d)
        (inwardShoreContourRank hn2 hT d) := by
  simp [inwardShoreContourArc, GridExpandedContour.edges_collarTrace]

theorem inwardShoreContourArc_isPath (d : GridDirectionalDart T) :
    (inwardShoreContourArc hn2 hT d).IsPath := by
  unfold inwardShoreContourArc
  simp only [Walk.isPath_copy]
  apply GridExpandedContour.collarTrace_isPath_of_advance_injective
  intro i j hi hj hij
  let f := GridExpandedContour.equiv (T := T)
  let k := inwardShoreContourRank hn2 hT d
  have hcycle := GridExpandedContour.equiv_isCycle_of_spanningSquareTree hn2 hT
  have hs : f (GridExpandedContour.slotOfDart d) ≠
      GridExpandedContour.slotOfDart d := by
    simpa only [f, GridExpandedContour.equiv_apply] using
      GridExpandedContour.succ_ne (T := T) (GridExpandedContour.slotOfDart d)
  have hik : i < orderOf f :=
    lt_of_le_of_lt hi (inwardShoreContourRank_lt_orderOf hn2 hT d)
  have hjk : j < orderOf f :=
    lt_of_le_of_lt hj (inwardShoreContourRank_lt_orderOf hn2 hT d)
  have happ : (f ^ i) (GridExpandedContour.slotOfDart d) =
      (f ^ j) (GridExpandedContour.slotOfDart d) := by
    simpa only [GridExpandedContour.advance_eq_iterate, f, Equiv.Perm.coe_pow] using hij
  have hpowers := hcycle.pow_eq_pow_iff.mpr ⟨_, hs, happ⟩
  exact pow_injOn_Iio_orderOf hik hjk hpowers

/-- The edge-corridor chord interior misses the complete target-shore contour
arc, not merely one terminal-dependent suffix. -/
theorem inwardShoreChord_support_intersection (d : GridDirectionalDart T) {x}
    (hx : x ∈ (GridExpandedContour.edgeCorridorChord d).support)
    (hy : x ∈ (inwardShoreContourArc hn2 hT d).support) :
    x = GridExpandedContour.slotPoint (GridExpandedContour.slotOfDart d) ∨
      x = GridExpandedContour.slotPoint
        (GridExpandedContour.slotOfDart d.reverse) := by
  by_cases hs : x = GridExpandedContour.slotPoint
      (GridExpandedContour.slotOfDart d)
  · exact Or.inl hs
  by_cases hr : x = GridExpandedContour.slotPoint
      (GridExpandedContour.slotOfDart d.reverse)
  · exact Or.inr hr
  exfalso
  apply GridExpandedContour.edgeCorridorChord_interior_not_mem_collarTrace
    d hx hs hr (GridExpandedContour.slotOfDart d)
      (inwardShoreContourRank hn2 hT d)
  simpa [inwardShoreContourArc] using hy

theorem inwardShoreChord_edges_disjoint (d : GridDirectionalDart T) :
    List.Disjoint (GridExpandedContour.edgeCorridorChord d).edges
      (inwardShoreContourArc hn2 hT d).edges := by
  rw [List.disjoint_left]
  intro e heChord heArc
  rw [GridExpandedContour.edges_edgeCorridorChord] at heChord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at heChord
  have hturnSource : GridExpandedContour.turnCorner d.source d.direction ∉
      (inwardShoreContourArc hn2 hT d).support := by
    intro hy
    apply GridExpandedContour.edgeCorridorChord_interior_not_mem_collarTrace d
      (x := GridExpandedContour.turnCorner d.source d.direction)
      (by rw [GridExpandedContour.support_edgeCorridorChord]; simp)
      (GridExpandedContour.turnCorner_ne_slotPoint _ _ _)
      (GridExpandedContour.turnCorner_ne_slotPoint _ _ _)
      (GridExpandedContour.slotOfDart d)
      (inwardShoreContourRank hn2 hT d)
    simpa [inwardShoreContourArc] using hy
  have hcenter : GridExpandedContour.edgeCorridorCenter d ∉
      (inwardShoreContourArc hn2 hT d).support := by
    intro hy
    apply GridExpandedContour.edgeCorridorChord_interior_not_mem_collarTrace d
      (x := GridExpandedContour.edgeCorridorCenter d)
      (by rw [GridExpandedContour.support_edgeCorridorChord]; simp)
      (GridExpandedContour.edgeCorridorCenter_ne_slotPoint (T := T) _ _)
      (GridExpandedContour.edgeCorridorCenter_ne_slotPoint (T := T) _ _)
      (GridExpandedContour.slotOfDart d)
      (inwardShoreContourRank hn2 hT d)
    simpa [inwardShoreContourArc] using hy
  have hturnTarget :
      GridExpandedContour.turnCorner d.target d.direction.opposite ∉
        (inwardShoreContourArc hn2 hT d).support := by
    intro hy
    apply GridExpandedContour.edgeCorridorChord_interior_not_mem_collarTrace d
      (x := GridExpandedContour.turnCorner d.target d.direction.opposite)
      (by rw [GridExpandedContour.support_edgeCorridorChord]; simp)
      (GridExpandedContour.turnCorner_ne_slotPoint _ _ _)
      (GridExpandedContour.turnCorner_ne_slotPoint _ _ _)
      (GridExpandedContour.slotOfDart d)
      (inwardShoreContourRank hn2 hT d)
    simpa [inwardShoreContourArc] using hy
  rcases heChord with rfl | rfl | rfl | rfl
  · exact hturnSource
      ((inwardShoreContourArc hn2 hT d).snd_mem_support_of_mem_edges heArc)
  · exact hcenter
      ((inwardShoreContourArc hn2 hT d).snd_mem_support_of_mem_edges heArc)
  · exact hcenter
      ((inwardShoreContourArc hn2 hT d).fst_mem_support_of_mem_edges heArc)
  · exact hturnTarget
      ((inwardShoreContourArc hn2 hT d).fst_mem_support_of_mem_edges heArc)

/-- Genuine local collar cycle around the fundamental target shore of `d`. -/
def inwardShoreCollarCycle (d : GridDirectionalDart T) :
    (gridGraph (GridExpandedContour.collarSize n)
      (GridExpandedContour.collarSize n)).Walk
      (GridExpandedContour.slotPoint
        (GridExpandedContour.slotOfDart d.reverse))
      (GridExpandedContour.slotPoint
        (GridExpandedContour.slotOfDart d.reverse)) :=
  (GridExpandedContour.edgeCorridorChord d).reverse.append
    (inwardShoreContourArc hn2 hT d)

theorem inwardShoreCollarCycle_isCycle (d : GridDirectionalDart T) :
    (inwardShoreCollarCycle hn2 hT d).IsCycle := by
  apply GridExpandedContour.reverse_append_isCycle_of_paths
  · exact GridExpandedContour.slotPoint_dart_ne_reverse (T := T) d
  · exact GridExpandedContour.edgeCorridorChord_isPath (T := T) d
  · exact inwardShoreContourArc_isPath hn2 hT d
  · exact inwardShoreChord_edges_disjoint hn2 hT d
  · intro x hx hy
    exact inwardShoreChord_support_intersection hn2 hT d hx hy

/-- Bounded face carrier of the genuine local fundamental-shore cycle. -/
def inwardShoreInteriorFaces (d : GridDirectionalDart T) :
    Finset (GridFace (GridExpandedContour.collarSize n)
      (GridExpandedContour.collarSize n)) :=
  cycleInteriorFaces (inwardShoreCollarCycle hn2 hT d)

@[simp] theorem out_not_mem_inwardShoreInteriorFaces
    (d : GridDirectionalDart T) :
    GridFace.out ∉ inwardShoreInteriorFaces hn2 hT d :=
  out_not_mem_cycleInteriorFaces _

theorem inwardShoreInteriorFaces_nonempty (d : GridDirectionalDart T) :
    (inwardShoreInteriorFaces hn2 hT d).Nonempty := by
  let G := gridGraph (GridExpandedContour.collarSize n)
    (GridExpandedContour.collarSize n)
  have hG : forcedEdgeGraph G
      ((↑(∅ : Finset (GridVertex (GridExpandedContour.collarSize n)
        (GridExpandedContour.collarSize n))) : Set _)ᶜ) = G := by
    ext u v
    simp [forcedEdgeGraph]
  have henclose : ∀ {v}
      (c : (forcedEdgeGraph G
        ((↑(∅ : Finset (GridVertex (GridExpandedContour.collarSize n)
          (GridExpandedContour.collarSize n))) : Set _)ᶜ)).Walk v v),
      c.IsCycle → (cycleInteriorFaces c).Nonempty :=
    (gridCycleEnclosesBoundedFace_of_rowRayParity gridCycleRowRayParity)
      (∅ : Finset (GridVertex (GridExpandedContour.collarSize n)
        (GridExpandedContour.collarSize n)))
  rw [hG] at henclose
  exact henclose (inwardShoreCollarCycle hn2 hT d)
    (inwardShoreCollarCycle_isCycle hn2 hT d)

/-- Per-inward-lens local region, independent of the lens terminal and of the
position of the reverse occurrence relative to it. -/
def inwardLensInteriorFaces (L : CanonicalLens axis hn2 hT)
    {d : GridDirectionalDart T}
    (_hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    Finset (GridFace (GridExpandedContour.collarSize n)
      (GridExpandedContour.collarSize n)) :=
  inwardShoreInteriorFaces hn2 hT d

theorem inwardLensInteriorFaces_nonempty
    (L : CanonicalLens axis hn2 hT) {d : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    (inwardLensInteriorFaces axis hn2 hT L hd).Nonempty :=
  inwardShoreInteriorFaces_nonempty hn2 hT d

/-- An inward lens dart is exactly the retained inward dart of its canonical
demand, rather than merely an occupied slot with matching coordinates. -/
theorem inwardLens_dart_eq_retainedCanonicalInwardDart
    (L : CanonicalLens axis hn2 hT) {d : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    ∃ hq : lensDirectDemand axis hn2 hT L ∉
        CanonicalShoreDemand.directExits axis hn2 T,
      d = GridDirectionalDart.retainedCanonicalInwardDart axis hn2 hT
        ⟨lensDirectDemand axis hn2 hT L,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hq⟩⟩ := by
  unfold lensDirectBranchGerm at hd
  split at hd <;> rename_i hq
  · cases hd
  · exact ⟨hq, CanonicalDirectBranchGerm.inward.inj hd |>.symm⟩

/-- The chosen forward arc has the graph-theoretic target shore orientation:
`d` is its unique contour entry and `d.reverse` its unique exit. -/
theorem inwardLens_targetShore_entry_exit
    (L : CanonicalLens axis hn2 hT) {d : GridDirectionalDart T}
    (_hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    (∀ x, x ∉ d.targetShoreDarts →
        (x.contourSucc ∈ d.targetShoreDarts ↔ x = d)) ∧
      (∀ x, x ∈ d.targetShoreDarts →
        (x.contourSucc ∉ d.targetShoreDarts ↔ x = d.reverse)) := by
  constructor
  · intro x hx
    exact GridDirectionalDart.contourSucc_mem_targetShore_iff_of_notMem
      hT.isTree.isAcyclic d x hx
  · intro x hx
    exact GridDirectionalDart.contourSucc_notMem_targetShore_iff_of_mem
      hT.isTree.isAcyclic d x hx

/-- Existing rooted-shore APIs yield laminarity after the lens darts are
oriented away from one common root.  Raw boundary-inward orientations need not
share this hypothesis. -/
theorem inwardLens_targetShores_laminar
    (root : GridVertex n n)
    (L K : CanonicalLens axis hn2 hT)
    {d e : GridDirectionalDart T}
    (_hd : lensDirectBranchGerm axis hn2 hT L = .inward d)
    (_he : lensDirectBranchGerm axis hn2 hT K = .inward e)
    (hdr : GridDirectionalDart.AwayFromRoot root d)
    (her : GridDirectionalDart.AwayFromRoot root e) :
    d.targetShoreVertices ⊆ e.targetShoreVertices ∨
      e.targetShoreVertices ⊆ d.targetShoreVertices ∨
      Disjoint d.targetShoreVertices e.targetShoreVertices :=
  GridDirectionalDart.targetShoreVertices_laminar hT.isTree root hdr her

/-- The exact dual-path transport needed to turn target-shore inclusion into
inclusion of the corresponding collar face carriers.  The two cycles exchange
different attachment chords, so this does not follow from edge-set monotonicity. -/
def InwardShoreDualNesting (d e : GridDirectionalDart T) : Prop :=
  ∀ f,
    (cycleComplementDualGraph (inwardShoreCollarCycle hn2 hT e)).Reachable
        GridFace.out f →
      (cycleComplementDualGraph (inwardShoreCollarCycle hn2 hT d)).Reachable
        GridFace.out f

theorem inwardShoreInteriorFaces_subset_iff_dualNesting
    (d e : GridDirectionalDart T) :
    inwardShoreInteriorFaces hn2 hT d ⊆
        inwardShoreInteriorFaces hn2 hT e ↔
      InwardShoreDualNesting hn2 hT d e := by
  exact cycleInteriorFaces_subset_iff_reachable_transport
    (inwardShoreCollarCycle hn2 hT d)
    (inwardShoreCollarCycle hn2 hT e)

/-- Strongest currently justified shore-to-face inclusion theorem: once the
explicit dual transport across the two attachment chords is supplied, target
shore inclusion yields face inclusion. -/
theorem inwardShoreInteriorFaces_subset_of_targetShore_subset
    (d e : GridDirectionalDart T)
    (_hshore : d.targetShoreVertices ⊆ e.targetShoreVertices)
    (hdual : InwardShoreDualNesting hn2 hT d e) :
    inwardShoreInteriorFaces hn2 hT d ⊆
      inwardShoreInteriorFaces hn2 hT e :=
  (inwardShoreInteriorFaces_subset_iff_dualNesting hn2 hT d e).2 hdual

/-- Exact dual condition for disjoint local shore regions. -/
def InwardShoreDualExterior (d e : GridDirectionalDart T) : Prop :=
  ∀ f,
    ¬(cycleComplementDualGraph (inwardShoreCollarCycle hn2 hT d)).Reachable
        GridFace.out f →
      (cycleComplementDualGraph (inwardShoreCollarCycle hn2 hT e)).Reachable
        GridFace.out f

theorem inwardShoreInteriorFaces_disjoint_iff_dualExterior
    (d e : GridDirectionalDart T) :
    Disjoint (inwardShoreInteriorFaces hn2 hT d)
        (inwardShoreInteriorFaces hn2 hT e) ↔
      InwardShoreDualExterior hn2 hT d e := by
  exact cycleInteriorFaces_disjoint_iff_reachable_exterior
    (inwardShoreCollarCycle hn2 hT d)
    (inwardShoreCollarCycle hn2 hT e)

theorem inwardShoreInteriorFaces_disjoint_of_targetShores_disjoint
    (d e : GridDirectionalDart T)
    (_hshore : Disjoint d.targetShoreVertices e.targetShoreVertices)
    (hdual : InwardShoreDualExterior hn2 hT d e) :
    Disjoint (inwardShoreInteriorFaces hn2 hT d)
      (inwardShoreInteriorFaces hn2 hT e) :=
  (inwardShoreInteriorFaces_disjoint_iff_dualExterior hn2 hT d e).2 hdual

/-- Strict face containment from the exact dual nesting condition plus one
face in the parent annulus. -/
theorem inwardShoreInteriorFaces_ssubset_of_dualNesting
    (d e : GridDirectionalDart T)
    (hdual : InwardShoreDualNesting hn2 hT d e)
    (hannulus : ∃ f, f ∈ inwardShoreInteriorFaces hn2 hT e ∧
      f ∉ inwardShoreInteriorFaces hn2 hT d) :
    inwardShoreInteriorFaces hn2 hT d ⊂
      inwardShoreInteriorFaces hn2 hT e := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨
    (inwardShoreInteriorFaces_subset_iff_dualNesting hn2 hT d e).2 hdual, ?_⟩
  rintro heq
  rcases hannulus with ⟨f, hfe, hfd⟩
  exact hfd (heq ▸ hfe)

/-- Residual geometric gate for all fundamental-shore collar regions.  Its two
clauses are precisely the dual reachability transports not supplied by abstract
tree-shore laminarity. -/
def InwardShoreFaceCutGate : Prop :=
  (∀ d e : GridDirectionalDart T,
      d.targetShoreVertices ⊆ e.targetShoreVertices →
        InwardShoreDualNesting hn2 hT d e) ∧
    (∀ d e : GridDirectionalDart T,
      Disjoint d.targetShoreVertices e.targetShoreVertices →
        InwardShoreDualExterior hn2 hT d e)

theorem inwardLensInteriorFaces_laminar_of_faceCutGate
    (hgate : InwardShoreFaceCutGate hn2 hT)
    (root : GridVertex n n)
    (L K : CanonicalLens axis hn2 hT)
    {d e : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d)
    (he : lensDirectBranchGerm axis hn2 hT K = .inward e)
    (hdr : GridDirectionalDart.AwayFromRoot root d)
    (her : GridDirectionalDart.AwayFromRoot root e) :
    inwardLensInteriorFaces axis hn2 hT L hd ⊆
        inwardLensInteriorFaces axis hn2 hT K he ∨
      inwardLensInteriorFaces axis hn2 hT K he ⊆
        inwardLensInteriorFaces axis hn2 hT L hd ∨
      Disjoint (inwardLensInteriorFaces axis hn2 hT L hd)
        (inwardLensInteriorFaces axis hn2 hT K he) := by
  rcases inwardLens_targetShores_laminar axis hn2 hT root L K hd he hdr her with
    hde | hed | hdis
  · exact Or.inl
      (inwardShoreInteriorFaces_subset_of_targetShore_subset hn2 hT d e hde
        (hgate.1 d e hde))
  · exact Or.inr (Or.inl
      (inwardShoreInteriorFaces_subset_of_targetShore_subset hn2 hT e d hed
        (hgate.1 e d hed)))
  · exact Or.inr (Or.inr
      (inwardShoreInteriorFaces_disjoint_of_targetShores_disjoint hn2 hT d e hdis
        (hgate.2 d e hdis)))

/-- Corrected orientation for planar shore regions: orient every attachment
edge away from one common root before selecting its target-side collar cycle. -/
noncomputable def rootedInwardRegionDart
    (root : GridVertex n n) (d : GridDirectionalDart T) :
    GridDirectionalDart T :=
  (GridDirectionalDart.rootedOrientation hT.isTree root d).1

theorem rootedInwardRegionDart_awayFromRoot
    (root : GridVertex n n) (d : GridDirectionalDart T) :
    GridDirectionalDart.AwayFromRoot root
      (rootedInwardRegionDart hT root d) :=
  (GridDirectionalDart.rootedOrientation hT.isTree root d).2

def rootedInwardLensInteriorFaces
    (root : GridVertex n n) (L : CanonicalLens axis hn2 hT)
    {d : GridDirectionalDart T}
    (_hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    Finset (GridFace (GridExpandedContour.collarSize n)
      (GridExpandedContour.collarSize n)) :=
  inwardShoreInteriorFaces hn2 hT (rootedInwardRegionDart hT root d)

/-- Canonical common root supplied by the outer port reached by a lens. -/
def lensRegionRoot (L : CanonicalLens axis hn2 hT) : GridVertex n n :=
  (lensOuterPort axis hn2 hT L).vertex

def canonicalRootedInwardLensInteriorFaces
    (L : CanonicalLens axis hn2 hT) {d : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    Finset (GridFace (GridExpandedContour.collarSize n)
      (GridExpandedContour.collarSize n)) :=
  rootedInwardLensInteriorFaces axis hn2 hT (lensRegionRoot axis hn2 hT L) L hd

theorem inwardLens_eq_of_dart_edgeSym2_eq
    (hn3 : 3 ≤ n)
    (L K : CanonicalLens axis hn2 hT) {d e : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d)
    (he : lensDirectBranchGerm axis hn2 hT K = .inward e)
    (hedge : d.edgeSym2 = e.edgeSym2) : L = K := by
  obtain ⟨hLd, hdret⟩ :=
    inwardLens_dart_eq_retainedCanonicalInwardDart axis hn2 hT L hd
  obtain ⟨hKe, heret⟩ :=
    inwardLens_dart_eq_retainedCanonicalInwardDart axis hn2 hT K he
  have hdem : lensDirectDemand axis hn2 hT L =
      lensDirectDemand axis hn2 hT K := by
    apply CanonicalShoreDemand.inwardEdgeSym2_injective axis hn2 hn3
    rw [← GridDirectionalDart.retainedCanonicalInwardDart_edgeSym2
        axis hn2 hT ⟨lensDirectDemand axis hn2 hT L,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hLd⟩⟩,
      ← GridDirectionalDart.retainedCanonicalInwardDart_edgeSym2
        axis hn2 hT ⟨lensDirectDemand axis hn2 hT K,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hKe⟩⟩,
      ← hdret, ← heret]
    exact hedge
  apply MarkedCycleFirstStop.ReconvergenceLens.ext
  apply (firstStop axis hn2 hT).mergerSlotMergerStateEquiv.injective
  rw [← L.mergerState_eq, ← K.mergerState_eq]
  apply Subtype.ext
  apply Subtype.ext
  calc
    L.mergerState.1.1 = startSlot axis hn2 hT
        (lensDirectDemand axis hn2 hT L) := by
      exact (startSlot_demandOfStartSlot axis hn2 hT
        (lensMergerBranches axis hn2 hT L).directStart).symm
    _ = startSlot axis hn2 hT (lensDirectDemand axis hn2 hT K) := by rw [hdem]
    _ = K.mergerState.1.1 := by
      exact startSlot_demandOfStartSlot axis hn2 hT
        (lensMergerBranches axis hn2 hT K).directStart

/-- Inward reconvergence-lens occurrences, now viewed only as labels attached
to rooted geometric shores.  Their planar parent below is unrelated to
`ReconvergenceLens.parent`. -/
structure PlanarInwardLensOccurrence (root : GridVertex n n) where
  lens : CanonicalLens axis hn2 hT
  dart : GridDirectionalDart T
  direct_eq : lensDirectBranchGerm axis hn2 hT lens = .inward dart

/-- The canonical lens determines an inward occurrence: equality of lenses
forces equality of their direct inward darts. -/
theorem PlanarInwardLensOccurrence.lens_injective
    (root : GridVertex n n) :
    Function.Injective
      (PlanarInwardLensOccurrence.lens (axis := axis) (hn2 := hn2)
        (hT := hT) (root := root)) := by
  rintro ⟨L, d, hd⟩ ⟨K, e, he⟩ hLK
  dsimp only at hLK
  subst K
  have hde : d = e := by
    have h := hd.symm.trans he
    exact CanonicalDirectBranchGerm.inward.inj h
  subst e
  rfl

/-- Forgetting the inward dart embeds planar occurrences into their canonical
lenses. -/
def planarInwardLensOccurrenceLensEmbedding
    (root : GridVertex n n) :
    PlanarInwardLensOccurrence axis hn2 hT root ↪ CanonicalLens axis hn2 hT where
  toFun := PlanarInwardLensOccurrence.lens
  inj' := PlanarInwardLensOccurrence.lens_injective axis hn2 hT root

def planarInwardLensOccurrence
    (root : GridVertex n n) (L : CanonicalLens axis hn2 hT)
    {d : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    PlanarInwardLensOccurrence axis hn2 hT root where
  lens := L
  dart := d
  direct_eq := hd

noncomputable instance planarInwardLensOccurrenceFintype
    (root : GridVertex n n) :
    Fintype (PlanarInwardLensOccurrence axis hn2 hT root) :=
  Fintype.ofInjective
    (fun a => (a.lens, a.dart)) (by
      intro a b hab
      cases a
      cases b
      simp only [Prod.mk.injEq] at hab
      rcases hab with ⟨rfl, rfl⟩
      rfl)

noncomputable instance planarInwardLensOccurrenceDecidableEq
    (root : GridVertex n n) :
    DecidableEq (PlanarInwardLensOccurrence axis hn2 hT root) :=
  Classical.decEq _

noncomputable def PlanarInwardLensOccurrence.rootedShore
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    GridDirectionalDart.RootedTreeDart (T := T) root :=
  GridDirectionalDart.rootedOrientation hT.isTree root a.dart

theorem PlanarInwardLensOccurrence.rootedShore_injective
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    Function.Injective
      (PlanarInwardLensOccurrence.rootedShore axis hn2 hT
        (root := root)) := by
  intro a b hab
  have hedgeRoot := congrArg
    (fun d : GridDirectionalDart.RootedTreeDart (T := T) root => d.1.edgeSym2) hab
  have hedge : a.dart.edgeSym2 = b.dart.edgeSym2 := by
    simpa [PlanarInwardLensOccurrence.rootedShore,
      GridDirectionalDart.rootedOrientation_edgeSym2] using hedgeRoot
  have hlens : a.lens = b.lens :=
    inwardLens_eq_of_dart_edgeSym2_eq axis hn2 hT hn3 a.lens b.lens
      a.direct_eq b.direct_eq hedge
  have hdart : a.dart = b.dart := by
    apply CanonicalDirectBranchGerm.inward.inj
    rw [← a.direct_eq, ← b.direct_eq, hlens]
  cases a
  cases b
  simp_all

def PlanarInwardLensOccurrence.HasStrictSupershore
    {root : GridVertex n n}
    (a b : PlanarInwardLensOccurrence axis hn2 hT root) : Prop :=
  (a.rootedShore axis hn2 hT).1.targetShoreVertices ⊂
    (b.rootedShore axis hn2 hT).1.targetShoreVertices

def PlanarInwardLensOccurrence.IsImmediateSupershore
    {root : GridVertex n n}
    (a b : PlanarInwardLensOccurrence axis hn2 hT root) : Prop :=
  a.HasStrictSupershore axis hn2 hT b ∧
    ∀ c, a.HasStrictSupershore axis hn2 hT c →
      (b.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
        (c.rootedShore axis hn2 hT).1.targetShoreVertices

theorem PlanarInwardLensOccurrence.exists_unique_immediateSupershore
    (hn3 : 3 ≤ n)
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (h : ∃ b, a.HasStrictSupershore axis hn2 hT b) :
    ∃! b, a.IsImmediateSupershore axis hn2 hT b := by
  classical
  let shores : Set (Finset (GridVertex n n)) :=
    {S | ∃ b : PlanarInwardLensOccurrence axis hn2 hT root,
      a.HasStrictSupershore axis hn2 hT b ∧
        (b.rootedShore axis hn2 hT).1.targetShoreVertices = S}
  obtain ⟨b₀, hb₀⟩ := h
  have hb₀mem : (b₀.rootedShore axis hn2 hT).1.targetShoreVertices ∈ shores :=
    ⟨b₀, hb₀, rfl⟩
  have hfinite : shores.Finite := Set.toFinite shores
  obtain ⟨D, _hDsub, hDmin⟩ := hfinite.exists_le_minimal hb₀mem
  obtain ⟨b, hb, hD⟩ := hDmin.prop
  have himmediate : a.IsImmediateSupershore axis hn2 hT b := by
    refine ⟨hb, ?_⟩
    intro c hc
    rcases GridDirectionalDart.targetShoreVertices_laminar hT.isTree root
        (b.rootedShore axis hn2 hT).2 (c.rootedShore axis hn2 hT).2 with
      hbc | hcb | hdis
    · exact hbc
    · have hcmem : (c.rootedShore axis hn2 hT).1.targetShoreVertices ∈ shores :=
        ⟨c, hc, rfl⟩
      have hcD : (c.rootedShore axis hn2 hT).1.targetShoreVertices ≤ D := by
        simpa [← hD] using hcb
      have hDc := hDmin.2 hcmem hcD
      simpa [← hD] using hDc
    · have hatarget := GridDirectionalDart.target_mem_targetShoreVertices
        (a.rootedShore axis hn2 hT).1
      exact (Finset.disjoint_left.mp hdis
        (hb.1 hatarget) (hc.1 hatarget)).elim
  refine ⟨b, himmediate, ?_⟩
  intro c hc
  apply PlanarInwardLensOccurrence.rootedShore_injective axis hn2 hT hn3 root
  apply GridDirectionalDart.RootedTreeDart.eq_of_targetShoreVertices_eq
    hT.isTree root
  apply Finset.Subset.antisymm
  · exact hc.2 b himmediate.1
  · exact himmediate.2 c hc.1

noncomputable def planarInwardLensParent
    (hn3 : 3 ≤ n)
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    Option (PlanarInwardLensOccurrence axis hn2 hT root) := by
  classical
  exact if h : ∃ b, a.HasStrictSupershore axis hn2 hT b then
    some (Classical.choose (a.exists_unique_immediateSupershore
      axis hn2 hT hn3 h))
  else none

theorem planarInwardLensParent_eq_some_iff
    (hn3 : 3 ≤ n)
    {root : GridVertex n n}
    (a b : PlanarInwardLensOccurrence axis hn2 hT root) :
    planarInwardLensParent axis hn2 hT hn3 a = some b ↔
      a.IsImmediateSupershore axis hn2 hT b := by
  classical
  unfold planarInwardLensParent
  split <;> rename_i h
  · constructor
    · intro hab
      have heq := Option.some.inj hab
      simpa [← heq] using
        (Classical.choose_spec
          (a.exists_unique_immediateSupershore axis hn2 hT hn3 h)).1
    · intro hb
      congr 1
      exact ((Classical.choose_spec
        (a.exists_unique_immediateSupershore axis hn2 hT hn3 h)).2 b hb).symm
  · constructor
    · simp
    · intro hb
      exact (h ⟨b, hb.1⟩).elim

theorem planarInwardLensParent_eq_none_iff
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    planarInwardLensParent axis hn2 hT hn3 a = none ↔
      ¬∃ b, a.HasStrictSupershore axis hn2 hT b := by
  classical
  unfold planarInwardLensParent
  simp

noncomputable def planarInwardLensParentForest
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    ParentForest (PlanarInwardLensOccurrence axis hn2 hT root) where
  parent := planarInwardLensParent axis hn2 hT hn3
  rank := fun a => Fintype.card (GridVertex n n) -
    (a.rootedShore axis hn2 hT).1.targetShoreVertices.card
  rank_parent := by
    intro a b hab
    have hstrict :=
      (planarInwardLensParent_eq_some_iff axis hn2 hT hn3 a b).1 hab |>.1
    have hcard := Finset.card_lt_card hstrict
    have hbcard :
        (b.rootedShore axis hn2 hT).1.targetShoreVertices.card ≤
          Fintype.card (GridVertex n n) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    exact Nat.sub_lt_sub_left (hcard.trans_le hbcard) hcard

/-- Corrected geometric obligation with an explicit planar parent map.  Unlike
`ReconvergenceLens.GeometricLensObligation`, it does not hardcode the unrelated
first-stop occurrence parent. -/
def CorrectedGeometricLensObligation
    (Occurrence Node Region : Type*)
    (belongs : Occurrence → Node → Prop)
    (region : Node → Region)
    (planarParent : Node → Option Node)
    (Disjoint StrictlyContains : Region → Region → Prop)
    (isBoundaryRoot : Node → Prop) : Prop :=
  (∀ o, ∃ L, belongs o L ∧
      ∀ K, belongs o K → L = K ∨ StrictlyContains (region K) (region L)) ∧
  (∀ L K, L = K ∨ Disjoint (region L) (region K) ∨
      StrictlyContains (region L) (region K) ∨
      StrictlyContains (region K) (region L)) ∧
  (∀ L K, planarParent L = some K →
      StrictlyContains (region K) (region L)) ∧
  (∀ L, planarParent L = none ↔ isBoundaryRoot L)

def planarInwardLensShoreRegion
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    Finset (GridVertex n n) :=
  (a.rootedShore axis hn2 hT).1.targetShoreVertices

/-- Kernel-level completion of the corrected obligation for the actual rooted
shore carriers.  Face carriers satisfy the same statement once the explicit
regular-neighborhood cut gate is discharged. -/
theorem planarInwardLensShore_geometricObligation
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    CorrectedGeometricLensObligation
      (PlanarInwardLensOccurrence axis hn2 hT root)
      (PlanarInwardLensOccurrence axis hn2 hT root)
      (Finset (GridVertex n n))
      (fun o L => o = L)
      (planarInwardLensShoreRegion axis hn2 hT)
      (planarInwardLensParent axis hn2 hT hn3)
      Disjoint
      (fun parent child => child ⊂ parent)
      (fun L => planarInwardLensParent axis hn2 hT hn3 L = none) := by
  refine ⟨?_, ?_, ?_, fun L => Iff.rfl⟩
  · intro o
    exact ⟨o, rfl, by intro K h; exact Or.inl h⟩
  · intro L K
    by_cases hLK : L = K
    · exact Or.inl hLK
    rcases GridDirectionalDart.targetShoreVertices_laminar hT.isTree root
        (L.rootedShore axis hn2 hT).2 (K.rootedShore axis hn2 hT).2 with
      hsub | hsup | hdis
    · right; right; right
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq =>
        hLK (PlanarInwardLensOccurrence.rootedShore_injective
          axis hn2 hT hn3 root
          (GridDirectionalDart.RootedTreeDart.eq_of_targetShoreVertices_eq
            hT.isTree root heq))⟩
    · right; right; left
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hsup, fun heq =>
        hLK (PlanarInwardLensOccurrence.rootedShore_injective
          axis hn2 hT hn3 root
          (GridDirectionalDart.RootedTreeDart.eq_of_targetShoreVertices_eq
            hT.isTree root heq.symm))⟩
    · exact Or.inr (Or.inl hdis)
  · intro L K hparent
    exact (planarInwardLensParent_eq_some_iff axis hn2 hT hn3 L K).1 hparent |>.1

/-! ## Unconditional U1 package using concrete planar vertex shores -/

structure PlanarOuterLensOccurrence (root : GridVertex n n) where
  lens : CanonicalLens axis hn2 hT
  port : GridCotreeOuterPort T
  direct_eq : lensDirectBranchGerm axis hn2 hT lens = .outer port

abbrev PlanarLensOccurrence (root : GridVertex n n) :=
  PlanarInwardLensOccurrence axis hn2 hT root ⊕
    PlanarOuterLensOccurrence axis hn2 hT root

inductive CanonicalPlanarRegion where
  | shore (vertices : Finset (GridVertex n n))
  | boundary

namespace CanonicalPlanarRegion

def Disjoint : CanonicalPlanarRegion (n := n) →
    CanonicalPlanarRegion (n := n) → Prop
  | .shore A, .shore B => _root_.Disjoint A B
  | .boundary, .boundary => True
  | .boundary, .shore _ | .shore _, .boundary => True

def StrictlyContains : CanonicalPlanarRegion (n := n) →
    CanonicalPlanarRegion (n := n) → Prop
  | .shore parent, .shore child => child ⊂ parent
  | _, _ => False

end CanonicalPlanarRegion

noncomputable def canonicalPlanarLensOccurrence
    (root : GridVertex n n) (L : CanonicalLens axis hn2 hT) :
    PlanarLensOccurrence axis hn2 hT root :=
  match h : lensDirectBranchGerm axis hn2 hT L with
  | .inward _ => .inl (planarInwardLensOccurrence axis hn2 hT root L h)
  | .outer p => .inr { lens := L, port := p, direct_eq := h }

theorem canonicalPlanarLensOccurrence_injective
    (root : GridVertex n n) :
    Function.Injective (canonicalPlanarLensOccurrence axis hn2 hT root) := by
  intro L K hLK
  let lensOf : PlanarLensOccurrence axis hn2 hT root →
      CanonicalLens axis hn2 hT
    | .inl a => a.lens
    | .inr a => a.lens
  have hproj (M : CanonicalLens axis hn2 hT) :
      lensOf (canonicalPlanarLensOccurrence axis hn2 hT root M) = M := by
    unfold canonicalPlanarLensOccurrence
    split <;> rfl
  calc
    L = lensOf (canonicalPlanarLensOccurrence axis hn2 hT root L) := (hproj L).symm
    _ = lensOf (canonicalPlanarLensOccurrence axis hn2 hT root K) :=
      congrArg lensOf hLK
    _ = K := hproj K

noncomputable def canonicalPlanarLensOccurrenceEmbedding
    (root : GridVertex n n) :
    CanonicalLens axis hn2 hT ↪ PlanarLensOccurrence axis hn2 hT root where
  toFun := canonicalPlanarLensOccurrence axis hn2 hT root
  inj' := canonicalPlanarLensOccurrence_injective axis hn2 hT root

def planarLensOccurrenceRegion
    {root : GridVertex n n} :
    PlanarLensOccurrence axis hn2 hT root → CanonicalPlanarRegion (n := n)
  | .inl a => .shore (planarInwardLensShoreRegion axis hn2 hT a)
  | .inr _ => .boundary

noncomputable def planarLensOccurrenceParent
    (hn3 : 3 ≤ n) {root : GridVertex n n} :
    PlanarLensOccurrence axis hn2 hT root →
      Option (PlanarLensOccurrence axis hn2 hT root)
  | .inl a => (planarInwardLensParent axis hn2 hT hn3 a).map Sum.inl
  | .inr _ => none

noncomputable def planarLensOccurrenceParentForest
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    ParentForest (PlanarLensOccurrence axis hn2 hT root) where
  parent := planarLensOccurrenceParent axis hn2 hT hn3
  rank
    | .inl a => (planarInwardLensParentForest axis hn2 hT hn3 root).rank a + 1
    | .inr _ => 0
  rank_parent := by
    intro a b hab
    rcases a with a | a
    · simp only [planarLensOccurrenceParent] at hab
      cases hp : planarInwardLensParent axis hn2 hT hn3 a with
      | none => simp [hp] at hab
      | some p =>
          simp [hp] at hab
          subst b
          exact Nat.add_lt_add_right
            ((planarInwardLensParentForest axis hn2 hT hn3 root).rank_parent hp) 1
    · simp [planarLensOccurrenceParent] at hab

theorem planarLensOccurrence_regions_laminar
    (hn3 : 3 ≤ n) (root : GridVertex n n)
    (a b : PlanarLensOccurrence axis hn2 hT root) :
    a = b ∨
      CanonicalPlanarRegion.Disjoint
        (planarLensOccurrenceRegion axis hn2 hT a)
        (planarLensOccurrenceRegion axis hn2 hT b) ∨
      CanonicalPlanarRegion.StrictlyContains
        (planarLensOccurrenceRegion axis hn2 hT a)
        (planarLensOccurrenceRegion axis hn2 hT b) ∨
      CanonicalPlanarRegion.StrictlyContains
        (planarLensOccurrenceRegion axis hn2 hT b)
        (planarLensOccurrenceRegion axis hn2 hT a) := by
  rcases a with a | a <;> rcases b with b | b
  · by_cases hab : a = b
    · exact Or.inl (congrArg Sum.inl hab)
    rcases GridDirectionalDart.targetShoreVertices_laminar hT.isTree root
        (a.rootedShore axis hn2 hT).2 (b.rootedShore axis hn2 hT).2 with
      hsub | hsup | hdis
    · right; right; right
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq =>
        hab (PlanarInwardLensOccurrence.rootedShore_injective
          axis hn2 hT hn3 root
          (GridDirectionalDart.RootedTreeDart.eq_of_targetShoreVertices_eq
            hT.isTree root heq))⟩
    · right; right; left
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hsup, fun heq =>
        hab (PlanarInwardLensOccurrence.rootedShore_injective
          axis hn2 hT hn3 root
          (GridDirectionalDart.RootedTreeDart.eq_of_targetShoreVertices_eq
            hT.isTree root heq.symm))⟩
    · exact Or.inr (Or.inl hdis)
  · exact Or.inr (Or.inl trivial)
  · exact Or.inr (Or.inl trivial)
  · by_cases hab : a = b
    · exact Or.inl (congrArg Sum.inr hab)
    · exact Or.inr (Or.inl trivial)

theorem planarLensOccurrence_parent_strictlyContains
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    {a b : PlanarLensOccurrence axis hn2 hT root}
    (hab : planarLensOccurrenceParent axis hn2 hT hn3 a = some b) :
    CanonicalPlanarRegion.StrictlyContains
      (planarLensOccurrenceRegion axis hn2 hT b)
      (planarLensOccurrenceRegion axis hn2 hT a) := by
  rcases a with a | a
  · simp only [planarLensOccurrenceParent] at hab
    cases hp : planarInwardLensParent axis hn2 hT hn3 a with
    | none => simp [hp] at hab
    | some p =>
        simp [hp] at hab
        subst b
        exact (planarInwardLensParent_eq_some_iff axis hn2 hT hn3 a p).1 hp |>.1
  · simp [planarLensOccurrenceParent] at hab

theorem planarOuterLensOccurrence_is_boundary_root
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (a : PlanarOuterLensOccurrence axis hn2 hT root) :
    planarLensOccurrenceParent axis hn2 hT hn3 (Sum.inr a) = none ∧
      planarLensOccurrenceRegion axis hn2 hT (Sum.inr a) = .boundary := by
  exact ⟨rfl, rfl⟩

/-- Unconditional U1 certificate.  Its regions are concrete common-root target
shore vertex sets; collar face carriers are an optional refinement. -/
structure CanonicalUpperU1Certificate (hn3 : 3 ≤ n) (root : GridVertex n n) where
  assignment : CanonicalLens axis hn2 hT ↪
    PlanarLensOccurrence axis hn2 hT root
  assignment_eq : assignment =
    canonicalPlanarLensOccurrenceEmbedding axis hn2 hT root
  regions_laminar : ∀
    (a b : PlanarLensOccurrence axis hn2 hT root),
    a = b ∨ CanonicalPlanarRegion.Disjoint
      (planarLensOccurrenceRegion axis hn2 hT a)
      (planarLensOccurrenceRegion axis hn2 hT b) ∨
      CanonicalPlanarRegion.StrictlyContains
        (planarLensOccurrenceRegion axis hn2 hT a)
        (planarLensOccurrenceRegion axis hn2 hT b) ∨
      CanonicalPlanarRegion.StrictlyContains
        (planarLensOccurrenceRegion axis hn2 hT b)
        (planarLensOccurrenceRegion axis hn2 hT a)
  parentForest : ParentForest (PlanarLensOccurrence axis hn2 hT root)
  parentForest_eq : parentForest =
    planarLensOccurrenceParentForest axis hn2 hT hn3 root
  parent_strict : ∀ {a b}, parentForest.parent a = some b →
    CanonicalPlanarRegion.StrictlyContains
      (planarLensOccurrenceRegion axis hn2 hT b)
      (planarLensOccurrenceRegion axis hn2 hT a)
  inward_parent_minimal : ∀
    (a b : PlanarInwardLensOccurrence axis hn2 hT root),
    planarInwardLensParent axis hn2 hT hn3 a = some b →
      a.IsImmediateSupershore axis hn2 hT b
  root_iff : ∀ a, parentForest.parent a = none ↔
    (match a with
      | .inl x => ¬∃ b, x.HasStrictSupershore axis hn2 hT b
      | .inr _ => True)

noncomputable def canonicalUpperU1
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    CanonicalUpperU1Certificate axis hn2 hT hn3 root where
  assignment := canonicalPlanarLensOccurrenceEmbedding axis hn2 hT root
  assignment_eq := rfl
  regions_laminar := planarLensOccurrence_regions_laminar axis hn2 hT hn3 root
  parentForest := planarLensOccurrenceParentForest axis hn2 hT hn3 root
  parentForest_eq := rfl
  parent_strict := planarLensOccurrence_parent_strictlyContains axis hn2 hT hn3
  inward_parent_minimal := fun a b h =>
    (planarInwardLensParent_eq_some_iff axis hn2 hT hn3 a b).1 h
  root_iff := by
    intro a
    rcases a with a | a
    · simp only [planarLensOccurrenceParentForest]
      simp only [planarLensOccurrenceParent]
      simpa only [Option.map_eq_none_iff] using
        planarInwardLensParent_eq_none_iff axis hn2 hT hn3 a
    · simp only [planarLensOccurrenceParentForest]
      simp [planarLensOccurrenceParent]

def canonicalUpperU1Root : GridVertex n n :=
  (⟨0, lt_of_lt_of_le Nat.zero_lt_two hn2⟩,
    ⟨0, lt_of_lt_of_le Nat.zero_lt_two hn2⟩)

/-- Root-argument-free canonical U1 certificate. -/
noncomputable def canonicalUpperU1Default (hn3 : 3 ≤ n) :
    CanonicalUpperU1Certificate axis hn2 hT hn3
      (canonicalUpperU1Root hn2) :=
  canonicalUpperU1 axis hn2 hT hn3 (canonicalUpperU1Root hn2)

/-! ## U2 ownership primitives, without adequacy claims -/

/-- An oriented incidence of a coordinate grid edge.  The Boolean chooses
which canonical endpoint is the exposed target. -/
structure OrientedShoreResource where
  edge : GridEdge n n
  reverse : Bool
  deriving DecidableEq, Fintype

namespace OrientedShoreResource

def source (r : OrientedShoreResource (n := n)) : GridVertex n n :=
  if r.reverse then r.edge.primalEndpoints.2 else r.edge.primalEndpoints.1

def target (r : OrientedShoreResource (n := n)) : GridVertex n n :=
  if r.reverse then r.edge.primalEndpoints.1 else r.edge.primalEndpoints.2

end OrientedShoreResource

/-- Candidate membership is exactly exposure through the rooted shore cut,
with the resource orientation pointing into the shore. -/
def PlanarInwardLensOccurrence.CandidateResource
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (r : OrientedShoreResource (n := n)) : Prop :=
  r.source ∉ (a.rootedShore axis hn2 hT).1.targetShoreVertices ∧
    r.target ∈ (a.rootedShore axis hn2 hT).1.targetShoreVertices

theorem PlanarInwardLensOccurrence.candidateResource_crosses
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (r : OrientedShoreResource (n := n))
    (hr : a.CandidateResource axis hn2 hT r) :
    r.edge.Crosses (a.rootedShore axis hn2 hT).1.targetShoreVertices := by
  cases hrev : r.reverse <;>
    simp only [PlanarInwardLensOccurrence.CandidateResource,
      OrientedShoreResource.source, OrientedShoreResource.target, hrev,
      Bool.false_eq_true, if_false, if_true] at hr
  · exact Or.inr ⟨hr.2, hr.1⟩
  · exact Or.inl ⟨hr.2, hr.1⟩

/-- A first owner is the smallest occurrence shore exposing the oriented
resource.  This predicate makes no assertion that any candidate exists. -/
def PlanarInwardLensOccurrence.FirstOwns
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (r : OrientedShoreResource (n := n)) : Prop :=
  a.CandidateResource axis hn2 hT r ∧
    ∀ b : PlanarInwardLensOccurrence axis hn2 hT root,
      b.CandidateResource axis hn2 hT r →
      (a.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
        (b.rootedShore axis hn2 hT).1.targetShoreVertices

abbrev PlanarInwardLensOccurrence.FirstOwnedResources
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  {r : OrientedShoreResource (n := n) // a.FirstOwns axis hn2 hT r}

def PlanarInwardLensOccurrence.firstOwnedResourceForget
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    a.FirstOwnedResources axis hn2 hT ↪ OrientedShoreResource (n := n) :=
  Function.Embedding.subtype _

theorem PlanarInwardLensOccurrence.firstOwner_unique
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    {a b : PlanarInwardLensOccurrence axis hn2 hT root}
    {r : OrientedShoreResource (n := n)}
    (ha : a.FirstOwns axis hn2 hT r)
    (hb : b.FirstOwns axis hn2 hT r) : a = b := by
  apply PlanarInwardLensOccurrence.rootedShore_injective axis hn2 hT hn3 root
  apply GridDirectionalDart.RootedTreeDart.eq_of_targetShoreVertices_eq
    hT.isTree root
  exact Finset.Subset.antisymm (ha.2 b hb.1) (hb.2 a ha.1)

/-- Globally labelled first-owned resources. -/
structure PlanarFirstOwnedResource
    (hn3 : 3 ≤ n) (root : GridVertex n n) where
  owner : PlanarInwardLensOccurrence axis hn2 hT root
  resource : OrientedShoreResource (n := n)
  first_owned : owner.FirstOwns axis hn2 hT resource

/-- Forgetting the owner remains injective because minimal exposed owners are
unique. -/
noncomputable def planarFirstOwnedResourceEmbedding
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    PlanarFirstOwnedResource axis hn2 hT hn3 root ↪
      OrientedShoreResource (n := n) where
  toFun x := x.resource
  inj' := by
    intro x y hxy
    change x.resource = y.resource at hxy
    have hy : y.owner.FirstOwns axis hn2 hT x.resource := by
      rw [hxy]
      exact y.first_owned
    have howner : x.owner = y.owner :=
      PlanarInwardLensOccurrence.firstOwner_unique axis hn2 hT hn3
        x.first_owned hy
    cases x
    cases y
    simp_all

theorem planarFirstOwnedResource_owner_disjoint
    (hn3 : 3 ≤ n) (root : GridVertex n n)
    {x y : PlanarFirstOwnedResource axis hn2 hT hn3 root}
    (howner : x.owner ≠ y.owner) : x.resource ≠ y.resource := by
  intro hresource
  have hy : y.owner.FirstOwns axis hn2 hT x.resource := by
    rw [hresource]
    exact y.first_owned
  exact howner (PlanarInwardLensOccurrence.firstOwner_unique axis hn2 hT hn3
    x.first_owned hy)

/-! ### The three physical primal resource kinds -/

abbrev SupportedSplitOuterPortResource := GridCotreeOuterPort T

abbrev RetainedInternalSupportEdgeResource :=
  ↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T)))

abbrev FreeFullVertexComponentResource :=
  ((gridGraph n n).induce
    (↑((Finset.univ : Finset (GridVertex n n)) \
      supportFinset (gridGraph n n \ T)) : Set (GridVertex n n))).ConnectedComponent

theorem outerLens_eq_of_port_eq
    (L K : CanonicalLens axis hn2 hT)
    {p q : GridCotreeOuterPort T}
    (hp : lensDirectBranchGerm axis hn2 hT L = .outer p)
    (hq : lensDirectBranchGerm axis hn2 hT K = .outer q)
    (hpq : p = q) : L = K := by
  apply MarkedCycleFirstStop.ReconvergenceLens.ext
  apply (firstStop axis hn2 hT).mergerSlotMergerStateEquiv.injective
  rw [← L.mergerState_eq, ← K.mergerState_eq]
  apply Subtype.ext
  apply Subtype.ext
  have hL := lensDirectBranchGerm_slot axis hn2 hT L
  have hK := lensDirectBranchGerm_slot axis hn2 hT K
  rw [hp, lensMergerBranches_directStart_value] at hL
  rw [hq, lensMergerBranches_directStart_value] at hK
  subst q
  exact hL.symm.trans hK

/-- Direct outer occurrences reserve actual split ports injectively. -/
noncomputable def planarOuterOwnedPortEmbedding
    (root : GridVertex n n) :
    PlanarOuterLensOccurrence axis hn2 hT root ↪ GridCotreeOuterPort T where
  toFun a := a.port
  inj' := by
    intro a b hab
    have hlens := outerLens_eq_of_port_eq axis hn2 hT a.lens b.lens
      a.direct_eq b.direct_eq hab
    cases a
    cases b
    simp_all

def PlanarInwardLensOccurrence.ExposesSplitOuterPort
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (p : SupportedSplitOuterPortResource (T := T)) : Prop :=
  p.vertex ∈ (a.rootedShore axis hn2 hT).1.targetShoreVertices

def PlanarInwardLensOccurrence.ExposesInternalSupportEdge
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (e : RetainedInternalSupportEdgeResource (T := T)) : Prop :=
  ∀ v ∈ e.1, v ∈ (a.rootedShore axis hn2 hT).1.targetShoreVertices

def PlanarInwardLensOccurrence.ExposesFreeComponent
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (C : FreeFullVertexComponentResource (T := T)) : Prop :=
  ∃ v ∈ C.supp,
    v.1 ∈ (a.rootedShore axis hn2 hT).1.targetShoreVertices

def PlanarInwardLensOccurrence.FirstOwnsPhysical
    {R : Type*} {root : GridVertex n n}
  (exposes : PlanarInwardLensOccurrence axis hn2 hT root → R → Prop)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) (r : R) : Prop :=
  exposes a r ∧ ∀ b : PlanarInwardLensOccurrence axis hn2 hT root, exposes b r →
    (a.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
      (b.rootedShore axis hn2 hT).1.targetShoreVertices

theorem PlanarInwardLensOccurrence.exists_unique_firstOwner_of_chain
    (hn3 : 3 ≤ n) {R : Type*} {root : GridVertex n n}
    (exposes : PlanarInwardLensOccurrence axis hn2 hT root → R → Prop)
    (r : R) (hnonempty : ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      exposes a r)
    (hchain : ∀ a b : PlanarInwardLensOccurrence axis hn2 hT root,
      exposes a r → exposes b r →
      (a.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
          (b.rootedShore axis hn2 hT).1.targetShoreVertices ∨
        (b.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
          (a.rootedShore axis hn2 hT).1.targetShoreVertices) :
    ∃! a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.FirstOwnsPhysical axis hn2 hT exposes r := by
  classical
  let shores : Set (Finset (GridVertex n n)) :=
    {S | ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      exposes a r ∧ (a.rootedShore axis hn2 hT).1.targetShoreVertices = S}
  obtain ⟨a₀, ha₀⟩ := hnonempty
  have ha₀mem : (a₀.rootedShore axis hn2 hT).1.targetShoreVertices ∈ shores :=
    ⟨a₀, ha₀, rfl⟩
  obtain ⟨D, _, hDmin⟩ := (Set.toFinite shores).exists_le_minimal ha₀mem
  obtain ⟨a, ha, hDa⟩ := hDmin.prop
  have hminimal : ∀ b, exposes b r →
      (a.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
        (b.rootedShore axis hn2 hT).1.targetShoreVertices := by
    intro b hb
    rcases hchain a b ha hb with hab | hba
    · exact hab
    · have hbmem : (b.rootedShore axis hn2 hT).1.targetShoreVertices ∈ shores :=
        ⟨b, hb, rfl⟩
      have hbD : (b.rootedShore axis hn2 hT).1.targetShoreVertices ≤ D := by
        simpa [← hDa] using hba
      have hDb := hDmin.2 hbmem hbD
      simpa [← hDa] using hDb
  refine ⟨a, ⟨ha, hminimal⟩, ?_⟩
  intro b hb
  apply PlanarInwardLensOccurrence.rootedShore_injective axis hn2 hT hn3 root
  apply GridDirectionalDart.RootedTreeDart.eq_of_targetShoreVertices_eq
    hT.isTree root
  exact Finset.Subset.antisymm (hb.2 a ha) (hminimal b hb.1)

theorem splitOuterPort_exposing_shores_chain
    {root : GridVertex n n} (p : SupportedSplitOuterPortResource (T := T))
    (a b : PlanarInwardLensOccurrence axis hn2 hT root)
    (ha : a.ExposesSplitOuterPort axis hn2 hT p)
    (hb : b.ExposesSplitOuterPort axis hn2 hT p) :
    (a.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
        (b.rootedShore axis hn2 hT).1.targetShoreVertices ∨
      (b.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
        (a.rootedShore axis hn2 hT).1.targetShoreVertices := by
  rcases GridDirectionalDart.targetShoreVertices_laminar hT.isTree root
      (a.rootedShore axis hn2 hT).2 (b.rootedShore axis hn2 hT).2 with
    hab | hba | hdis
  · exact Or.inl hab
  · exact Or.inr hba
  · exact (Finset.disjoint_left.mp hdis ha hb).elim

theorem internalSupportEdge_exposing_shores_chain
    {root : GridVertex n n} (e : RetainedInternalSupportEdgeResource (T := T))
    (a b : PlanarInwardLensOccurrence axis hn2 hT root)
    (ha : a.ExposesInternalSupportEdge axis hn2 hT e)
    (hb : b.ExposesInternalSupportEdge axis hn2 hT e) :
    (a.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
        (b.rootedShore axis hn2 hT).1.targetShoreVertices ∨
      (b.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
        (a.rootedShore axis hn2 hT).1.targetShoreVertices := by
  rcases GridDirectionalDart.targetShoreVertices_laminar hT.isTree root
      (a.rootedShore axis hn2 hT).2 (b.rootedShore axis hn2 hT).2 with
    hab | hba | hdis
  · exact Or.inl hab
  · exact Or.inr hba
  · have hexists : ∃ u : GridVertex n n, u ∈ e.1 := by
      induction e.1 using Sym2.inductionOn with
      | _ u v => exact ⟨u, by simp [Sym2.mem_iff]⟩
    obtain ⟨u, hu⟩ := hexists
    exact (Finset.disjoint_left.mp hdis (ha u hu) (hb u hu)).elim

theorem exists_unique_firstOwner_splitOuterPort
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (p : SupportedSplitOuterPortResource (T := T))
    (h : ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.ExposesSplitOuterPort axis hn2 hT p) :
    ∃! a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.FirstOwnsPhysical axis hn2 hT
      (PlanarInwardLensOccurrence.ExposesSplitOuterPort axis hn2 hT) p :=
  PlanarInwardLensOccurrence.exists_unique_firstOwner_of_chain
    axis hn2 hT hn3 _ p h (splitOuterPort_exposing_shores_chain axis hn2 hT p)

theorem exists_unique_firstOwner_internalSupportEdge
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (e : RetainedInternalSupportEdgeResource (T := T))
    (h : ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.ExposesInternalSupportEdge axis hn2 hT e) :
    ∃! a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.FirstOwnsPhysical axis hn2 hT
      (PlanarInwardLensOccurrence.ExposesInternalSupportEdge axis hn2 hT) e :=
  PlanarInwardLensOccurrence.exists_unique_firstOwner_of_chain
    axis hn2 hT hn3 _ e h (internalSupportEdge_exposing_shores_chain axis hn2 hT e)

structure PlanarFirstOwnedPhysical
    {R : Type*} (root : GridVertex n n)
    (exposes : PlanarInwardLensOccurrence axis hn2 hT root → R → Prop) where
  owner : PlanarInwardLensOccurrence axis hn2 hT root
  resource : R
  first_owned : owner.FirstOwnsPhysical axis hn2 hT exposes resource

noncomputable instance planarFirstOwnedPhysicalFintype
    {R : Type*} [Fintype R] (root : GridVertex n n)
    (exposes : PlanarInwardLensOccurrence axis hn2 hT root → R → Prop) :
    Fintype (PlanarFirstOwnedPhysical axis hn2 hT root exposes) :=
  Fintype.ofInjective (fun x => (x.owner, x.resource)) (by
    intro x y hxy
    cases x
    cases y
    simp_all)

noncomputable def planarFirstOwnedPhysicalEmbedding
    (hn3 : 3 ≤ n) {R : Type*} (root : GridVertex n n)
    (exposes : PlanarInwardLensOccurrence axis hn2 hT root → R → Prop) :
    PlanarFirstOwnedPhysical axis hn2 hT root exposes ↪ R where
  toFun x := x.resource
  inj' := by
    intro x y hxy
    change x.resource = y.resource at hxy
    have hy : y.owner.FirstOwnsPhysical axis hn2 hT exposes x.resource := by
      rw [hxy]
      exact y.first_owned
    have howner : x.owner = y.owner := by
      apply PlanarInwardLensOccurrence.rootedShore_injective axis hn2 hT hn3 root
      apply GridDirectionalDart.RootedTreeDart.eq_of_targetShoreVertices_eq
        hT.isTree root
      exact Finset.Subset.antisymm
        (x.first_owned.2 y.owner hy.1) (hy.2 x.owner x.first_owned.1)
    cases x
    cases y
    simp_all

theorem planarFirstOwnedPhysical_owner_disjoint
    (hn3 : 3 ≤ n) {R : Type*} (root : GridVertex n n)
    (exposes : PlanarInwardLensOccurrence axis hn2 hT root → R → Prop)
    {x y : PlanarFirstOwnedPhysical axis hn2 hT root exposes}
    (howner : x.owner ≠ y.owner) : x.resource ≠ y.resource := by
  intro hresource
  have hy : exposes y.owner x.resource := by
    rw [hresource]
    exact y.first_owned.1
  have hx : exposes x.owner y.resource := by
    rw [← hresource]
    exact x.first_owned.1
  exact howner (by
    apply PlanarInwardLensOccurrence.rootedShore_injective axis hn2 hT hn3 root
    apply GridDirectionalDart.RootedTreeDart.eq_of_targetShoreVertices_eq
      hT.isTree root
    exact Finset.Subset.antisymm
      (x.first_owned.2 y.owner hy)
      (y.first_owned.2 x.owner hx))

abbrev FirstOwnedSplitOuterPorts (root : GridVertex n n) :=
  PlanarFirstOwnedPhysical axis hn2 hT root
    (PlanarInwardLensOccurrence.ExposesSplitOuterPort axis hn2 hT)

abbrev FirstOwnedInternalSupportEdges (root : GridVertex n n) :=
  PlanarFirstOwnedPhysical axis hn2 hT root
    (PlanarInwardLensOccurrence.ExposesInternalSupportEdge axis hn2 hT)

abbrev FirstOwnedFreeComponents (root : GridVertex n n) :=
  PlanarFirstOwnedPhysical axis hn2 hT root
    (PlanarInwardLensOccurrence.ExposesFreeComponent axis hn2 hT)

noncomputable def firstOwnedSplitOuterPortEmbedding
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    FirstOwnedSplitOuterPorts axis hn2 hT root ↪
      SupportedSplitOuterPortResource (T := T) :=
  planarFirstOwnedPhysicalEmbedding axis hn2 hT hn3 root _

noncomputable def firstOwnedInternalSupportEdgeEmbedding
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    FirstOwnedInternalSupportEdges axis hn2 hT root ↪
      RetainedInternalSupportEdgeResource (T := T) :=
  planarFirstOwnedPhysicalEmbedding axis hn2 hT hn3 root _

/-- This is exactly the missing geometric statement for raw free components:
one component must not first contact two disjoint occurrence shores. -/
def FreeComponentExposureLaminar (root : GridVertex n n) : Prop :=
  ∀ (C : FreeFullVertexComponentResource (T := T))
    (a b : PlanarInwardLensOccurrence axis hn2 hT root),
    a.ExposesFreeComponent axis hn2 hT C →
    b.ExposesFreeComponent axis hn2 hT C →
    (a.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
        (b.rootedShore axis hn2 hT).1.targetShoreVertices ∨
      (b.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
        (a.rootedShore axis hn2 hT).1.targetShoreVertices

noncomputable def firstOwnedFreeComponentEmbedding
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    FirstOwnedFreeComponents axis hn2 hT root ↪
      FreeFullVertexComponentResource (T := T) :=
  planarFirstOwnedPhysicalEmbedding axis hn2 hT hn3 root _

theorem exists_unique_firstOwner_freeComponent
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (hlaminar : FreeComponentExposureLaminar axis hn2 hT root)
    (C : FreeFullVertexComponentResource (T := T))
    (h : ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.ExposesFreeComponent axis hn2 hT C) :
    ∃! a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.FirstOwnsPhysical axis hn2 hT
        (PlanarInwardLensOccurrence.ExposesFreeComponent axis hn2 hT) C :=
  PlanarInwardLensOccurrence.exists_unique_firstOwner_of_chain
    axis hn2 hT hn3 _ C h (hlaminar C)

theorem exists_exposedFreeComponent_of_target_not_mem_support
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (hfree : (a.rootedShore axis hn2 hT).1.target ∉
      supportFinset (gridGraph n n \ T)) :
    ∃ C : FreeFullVertexComponentResource (T := T),
      a.ExposesFreeComponent axis hn2 hT C := by
  let v : ↥((Finset.univ : Finset (GridVertex n n)) \
      supportFinset (gridGraph n n \ T)) :=
    ⟨(a.rootedShore axis hn2 hT).1.target,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hfree⟩⟩
  let G := (gridGraph n n).induce
    (↑((Finset.univ : Finset (GridVertex n n)) \
      supportFinset (gridGraph n n \ T)) : Set (GridVertex n n))
  let C := G.connectedComponentMk v
  refine ⟨C, v, ?_, ?_⟩
  · rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  · exact GridDirectionalDart.target_mem_targetShoreVertices _

/-- Exact remaining exposure coverage statements.  Ownership uniqueness is
already proved independently of these propositions. -/
def SplitOuterPortExposureComplete (root : GridVertex n n) : Prop :=
  ∀ p : SupportedSplitOuterPortResource (T := T),
    ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.ExposesSplitOuterPort axis hn2 hT p

def InternalSupportEdgeExposureComplete (root : GridVertex n n) : Prop :=
  ∀ e : RetainedInternalSupportEdgeResource (T := T),
    ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.ExposesInternalSupportEdge axis hn2 hT e

def FreeComponentExposureComplete (root : GridVertex n n) : Prop :=
  ∀ C : FreeFullVertexComponentResource (T := T),
    ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.ExposesFreeComponent axis hn2 hT C

abbrev ExposedSplitOuterPortResource (root : GridVertex n n) :=
  {p : SupportedSplitOuterPortResource (T := T) //
    ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.ExposesSplitOuterPort axis hn2 hT p}

abbrev ExposedInternalSupportEdgeResource (root : GridVertex n n) :=
  {e : RetainedInternalSupportEdgeResource (T := T) //
    ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.ExposesInternalSupportEdge axis hn2 hT e}

abbrev ExposedFreeComponentResource (root : GridVertex n n) :=
  {C : FreeFullVertexComponentResource (T := T) //
    ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.ExposesFreeComponent axis hn2 hT C}

noncomputable def firstOwnedSplitOuterPortOfExposed
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (p : ExposedSplitOuterPortResource axis hn2 hT root) :
    FirstOwnedSplitOuterPorts axis hn2 hT root := by
  let h := exists_unique_firstOwner_splitOuterPort axis hn2 hT hn3 p.1 p.2
  exact ⟨Classical.choose h.exists, p.1, Classical.choose_spec h.exists⟩

noncomputable def firstOwnedInternalSupportEdgeOfExposed
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (e : ExposedInternalSupportEdgeResource axis hn2 hT root) :
    FirstOwnedInternalSupportEdges axis hn2 hT root := by
  let h := exists_unique_firstOwner_internalSupportEdge axis hn2 hT hn3 e.1 e.2
  exact ⟨Classical.choose h.exists, e.1, Classical.choose_spec h.exists⟩

noncomputable def firstOwnedFreeComponentOfExposed
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (hlaminar : FreeComponentExposureLaminar axis hn2 hT root)
    (C : ExposedFreeComponentResource axis hn2 hT root) :
    FirstOwnedFreeComponents axis hn2 hT root := by
  let h := exists_unique_firstOwner_freeComponent axis hn2 hT hn3
    hlaminar C.1 C.2
  exact ⟨Classical.choose h.exists, C.1, Classical.choose_spec h.exists⟩

theorem firstOwnedSplitOuterPortOfExposed_resource
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (p : ExposedSplitOuterPortResource axis hn2 hT root) :
    (firstOwnedSplitOuterPortOfExposed axis hn2 hT hn3 p).resource = p.1 := by
  simp [firstOwnedSplitOuterPortOfExposed]

theorem firstOwnedInternalSupportEdgeOfExposed_resource
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (e : ExposedInternalSupportEdgeResource axis hn2 hT root) :
    (firstOwnedInternalSupportEdgeOfExposed axis hn2 hT hn3 e).resource = e.1 := by
  simp [firstOwnedInternalSupportEdgeOfExposed]

theorem firstOwnedFreeComponentOfExposed_resource
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (hlaminar : FreeComponentExposureLaminar axis hn2 hT root)
    (C : ExposedFreeComponentResource axis hn2 hT root) :
    (firstOwnedFreeComponentOfExposed axis hn2 hT hn3 hlaminar C).resource = C.1 := by
  simp [firstOwnedFreeComponentOfExposed]

/-- Constructed U2 layer: explicit owned subtypes and injective forgetful maps.
It deliberately contains no exposure-completeness or cardinality field. -/
structure CanonicalUpperU2OwnershipPrimitives
    (hn3 : 3 ≤ n) (root : GridVertex n n) where
  reservedOuterPorts : PlanarOuterLensOccurrence axis hn2 hT root ↪
    SupportedSplitOuterPortResource (T := T)
  firstOwnedPorts : FirstOwnedSplitOuterPorts axis hn2 hT root ↪
    SupportedSplitOuterPortResource (T := T)
  firstOwnedInternalEdges : FirstOwnedInternalSupportEdges axis hn2 hT root ↪
    RetainedInternalSupportEdgeResource (T := T)
  firstOwnedFreeComponents : FirstOwnedFreeComponents axis hn2 hT root ↪
    FreeFullVertexComponentResource (T := T)

noncomputable def canonicalUpperU2OwnershipPrimitives
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    CanonicalUpperU2OwnershipPrimitives axis hn2 hT hn3 root where
  reservedOuterPorts := planarOuterOwnedPortEmbedding axis hn2 hT root
  firstOwnedPorts := firstOwnedSplitOuterPortEmbedding axis hn2 hT hn3 root
  firstOwnedInternalEdges :=
    firstOwnedInternalSupportEdgeEmbedding axis hn2 hT hn3 root
  firstOwnedFreeComponents := firstOwnedFreeComponentEmbedding axis hn2 hT hn3 root

/-- Corrected local granularity for a free component: retain the concrete first
contact vertex.  Distinct contacts are not counted as distinct raw components. -/
structure FreeComponentContactResource where
  component : FreeFullVertexComponentResource (T := T)
  contact : ↥((Finset.univ : Finset (GridVertex n n)) \
    supportFinset (gridGraph n n \ T))
  contact_mem : contact ∈ component.supp

noncomputable instance freeComponentContactResourceFintype :
    Fintype (FreeComponentContactResource (T := T)) :=
  Fintype.ofInjective (fun r => (r.component, r.contact)) (by
    intro r s hrs
    cases r
    cases s
    simp_all)

def PlanarInwardLensOccurrence.ExposesFreeComponentContact
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (r : FreeComponentContactResource (T := T)) : Prop :=
  r.contact.1 ∈ (a.rootedShore axis hn2 hT).1.targetShoreVertices

theorem exists_exposedFreeComponentContact_of_exposesFreeComponent
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (C : FreeFullVertexComponentResource (T := T))
    (hC : a.ExposesFreeComponent axis hn2 hT C) :
    ∃ r : FreeComponentContactResource (T := T),
      r.component = C ∧ a.ExposesFreeComponentContact axis hn2 hT r := by
  rcases hC with ⟨v, hvC, hva⟩
  exact ⟨{ component := C, contact := v, contact_mem := hvC }, rfl, hva⟩

theorem freeComponentContact_exposing_shores_chain
    {root : GridVertex n n} (r : FreeComponentContactResource (T := T))
    (a b : PlanarInwardLensOccurrence axis hn2 hT root)
    (ha : a.ExposesFreeComponentContact axis hn2 hT r)
    (hb : b.ExposesFreeComponentContact axis hn2 hT r) :
    (a.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
        (b.rootedShore axis hn2 hT).1.targetShoreVertices ∨
      (b.rootedShore axis hn2 hT).1.targetShoreVertices ⊆
        (a.rootedShore axis hn2 hT).1.targetShoreVertices := by
  rcases GridDirectionalDart.targetShoreVertices_laminar hT.isTree root
      (a.rootedShore axis hn2 hT).2 (b.rootedShore axis hn2 hT).2 with
    hab | hba | hdis
  · exact Or.inl hab
  · exact Or.inr hba
  · exact (Finset.disjoint_left.mp hdis ha hb).elim

abbrev FirstOwnedFreeComponentContacts (root : GridVertex n n) :=
  PlanarFirstOwnedPhysical axis hn2 hT root
    (PlanarInwardLensOccurrence.ExposesFreeComponentContact axis hn2 hT)

noncomputable def firstOwnedFreeComponentContactEmbedding
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    FirstOwnedFreeComponentContacts axis hn2 hT root ↪
      FreeComponentContactResource (T := T) :=
  planarFirstOwnedPhysicalEmbedding axis hn2 hT hn3 root _

theorem exists_unique_firstOwner_freeComponentContact
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (r : FreeComponentContactResource (T := T))
    (h : ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.ExposesFreeComponentContact axis hn2 hT r) :
    ∃! a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.FirstOwnsPhysical axis hn2 hT
        (PlanarInwardLensOccurrence.ExposesFreeComponentContact axis hn2 hT) r :=
    PlanarInwardLensOccurrence.exists_unique_firstOwner_of_chain
    axis hn2 hT hn3 _ r h
      (freeComponentContact_exposing_shores_chain axis hn2 hT r)

/-- Contact-labelled resources which are exposed by at least one occurrence. -/
abbrev ExposedFreeComponentContactResource (root : GridVertex n n) :=
  {r : FreeComponentContactResource (T := T) //
    ∃ a : PlanarInwardLensOccurrence axis hn2 hT root,
      a.ExposesFreeComponentContact axis hn2 hT r}

noncomputable def firstOwnedFreeComponentContactOfExposed
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (r : ExposedFreeComponentContactResource axis hn2 hT root) :
    FirstOwnedFreeComponentContacts axis hn2 hT root := by
  let h := exists_unique_firstOwner_freeComponentContact axis hn2 hT hn3 r.1 r.2
  exact ⟨Classical.choose h.exists, r.1, Classical.choose_spec h.exists⟩

@[simp] theorem firstOwnedFreeComponentContactOfExposed_resource
    (hn3 : 3 ≤ n) {root : GridVertex n n}
    (r : ExposedFreeComponentContactResource axis hn2 hT root) :
    (firstOwnedFreeComponentContactOfExposed axis hn2 hT hn3 r).resource = r.1 := by
  simp [firstOwnedFreeComponentContactOfExposed]

/-- Choose one geometrically exposed contact for an exposed raw component.
Other contacts of the same component are deliberately not separate resources. -/
noncomputable def exposedFreeComponentContactOfExposedComponent
    {root : GridVertex n n}
    (C : ExposedFreeComponentResource axis hn2 hT root) :
    ExposedFreeComponentContactResource axis hn2 hT root := by
  let a := Classical.choose C.2
  let ha := Classical.choose_spec C.2
  let hcontact := exists_exposedFreeComponentContact_of_exposesFreeComponent
    axis hn2 hT a C.1 ha
  let r := Classical.choose hcontact
  exact ⟨r, a, (Classical.choose_spec hcontact).2⟩

@[simp] theorem exposedFreeComponentContactOfExposedComponent_component
    {root : GridVertex n n}
    (C : ExposedFreeComponentResource axis hn2 hT root) :
    (exposedFreeComponentContactOfExposedComponent axis hn2 hT C).1.component = C.1 := by
  simp only [exposedFreeComponentContactOfExposedComponent]
  exact (Classical.choose_spec
    (exists_exposedFreeComponentContact_of_exposesFreeComponent axis hn2 hT
      (Classical.choose C.2) C.1 (Classical.choose_spec C.2))).1

/-- Every exposed raw free component receives one first-owned contact.  This is
injective by the retained component label and needs no no-double-contact gate. -/
noncomputable def exposedFreeComponentFirstOwnerEmbedding
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    ExposedFreeComponentResource axis hn2 hT root ↪
      FirstOwnedFreeComponentContacts axis hn2 hT root where
  toFun C := firstOwnedFreeComponentContactOfExposed axis hn2 hT hn3
    (exposedFreeComponentContactOfExposedComponent axis hn2 hT C)
  inj' := by
    intro C D hCD
    apply Subtype.ext
    have hcomponent := congrArg
      (fun x : FirstOwnedFreeComponentContacts axis hn2 hT root =>
        x.resource.component) hCD
    simpa using hcomponent

/-- The analogous canonical assignments for the other exposed physical
resource kinds. -/
noncomputable def exposedSplitOuterPortFirstOwnerEmbedding
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    ExposedSplitOuterPortResource axis hn2 hT root ↪
      FirstOwnedSplitOuterPorts axis hn2 hT root where
  toFun := firstOwnedSplitOuterPortOfExposed axis hn2 hT hn3
  inj' := by
    intro p q hpq
    apply Subtype.ext
    have hresource := congrArg
      (fun x : FirstOwnedSplitOuterPorts axis hn2 hT root => x.resource) hpq
    simpa only [firstOwnedSplitOuterPortOfExposed] using hresource

noncomputable def exposedInternalSupportEdgeFirstOwnerEmbedding
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    ExposedInternalSupportEdgeResource axis hn2 hT root ↪
      FirstOwnedInternalSupportEdges axis hn2 hT root where
  toFun := firstOwnedInternalSupportEdgeOfExposed axis hn2 hT hn3
  inj' := by
    intro e f hef
    apply Subtype.ext
    have hresource := congrArg
      (fun x : FirstOwnedInternalSupportEdges axis hn2 hT root => x.resource) hef
    simpa only [firstOwnedInternalSupportEdgeOfExposed] using hresource

/-- Canonical U2 assignment for exactly the geometrically exposed physical
resources.  It contains no ledger-wide exposure or resource-adequacy claim. -/
structure CanonicalUpperU2ExposedOwnership
    (hn3 : 3 ≤ n) (root : GridVertex n n) where
  splitOuterPorts : ExposedSplitOuterPortResource axis hn2 hT root ↪
    FirstOwnedSplitOuterPorts axis hn2 hT root
  internalSupportEdges : ExposedInternalSupportEdgeResource axis hn2 hT root ↪
    FirstOwnedInternalSupportEdges axis hn2 hT root
  freeComponents : ExposedFreeComponentResource axis hn2 hT root ↪
    FirstOwnedFreeComponentContacts axis hn2 hT root

noncomputable def canonicalUpperU2ExposedOwnership
    (hn3 : 3 ≤ n) (root : GridVertex n n) :
    CanonicalUpperU2ExposedOwnership axis hn2 hT hn3 root where
  splitOuterPorts := exposedSplitOuterPortFirstOwnerEmbedding axis hn2 hT hn3 root
  internalSupportEdges :=
    exposedInternalSupportEdgeFirstOwnerEmbedding axis hn2 hT hn3 root
  freeComponents := exposedFreeComponentFirstOwnerEmbedding axis hn2 hT hn3 root

/-- This stronger optional condition is needed only when every exposed contact,
rather than one selected contact per component, is retained in the ledger. -/
def FreeComponentFirstContactPruned
    (root : GridVertex n n) : Prop :=
  Function.Injective fun
    x : FirstOwnedFreeComponentContacts axis hn2 hT root => x.resource.component

/-! ## U3 regional bookkeeping -/

abbrev PlanarInwardLensForest (root : GridVertex n n) :=
  planarInwardLensParentForest axis hn2 hT hn3 root

/-- Merger-excess occurrences whose planar region is `a`.  The occurrence
label is the first coordinate of the parent-forest merger slot. -/
abbrev PlanarLensLocalDebt (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  {s : (PlanarInwardLensForest axis hn2 hn3 hT root).MergerSlot // s.1 = a}

/-- The global merger-excess ledger is the disjoint sigma of its regional
fibers. -/
def planarLensLocalDebtDecomposition (root : GridVertex n n) :
    (PlanarInwardLensForest axis hn2 hn3 hT root).MergerSlot ≃
      Σ a, PlanarLensLocalDebt axis hn2 hn3 hT root a where
  toFun s := ⟨s.1, s, rfl⟩
  invFun s := s.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨a, s, hs⟩
    cases s with
    | mk b i =>
      simp only at hs
      subst b
      rfl

theorem card_planarLensLocalDebtDecomposition (root : GridVertex n n) :
    Fintype.card (PlanarInwardLensForest axis hn2 hn3 hT root).MergerSlot =
      ∑ a, Fintype.card (PlanarLensLocalDebt axis hn2 hn3 hT root a) := by
  rw [Fintype.card_congr (planarLensLocalDebtDecomposition axis hn2 hn3 hT root),
    Fintype.card_sigma]

noncomputable instance planarLensLocalDebtFintype
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    Fintype (PlanarLensLocalDebt axis hn2 hn3 hT root a) := Fintype.ofFinite _

/-- A regional merger slot contains no information beyond its local excess
index. -/
def planarLensLocalDebtEquivFin
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    PlanarLensLocalDebt axis hn2 hn3 hT root a ≃
      Fin ((PlanarInwardLensForest axis hn2 hn3 hT root).mergerExcessAt a) where
  toFun x := Fin.cast
    (congrArg (PlanarInwardLensForest axis hn2 hn3 hT root).mergerExcessAt x.2)
    x.1.2
  invFun i := ⟨⟨a, i⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨b, i⟩, hb⟩
    cases hb
    rfl
  right_inv _ := rfl

/-- Distinct local excess indices select distinct immediate children.  No
physical or gap-resource existence is asserted. -/
noncomputable def planarLensLocalDebtImmediateChildEmbedding
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    PlanarLensLocalDebt axis hn2 hn3 hT root a ↪
      ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a) := by
  let F := PlanarInwardLensForest axis hn2 hn3 hT root
  let childEmbedding := F.localMergerSlotPhysicalChildEmbedding
    (fun _ => True) (by
      intro v
      simp [ParentForest.nonphysicalChildren]) a
  exact (planarLensLocalDebtEquivFin axis hn2 hn3 hT root a).toEmbedding.trans
    { toFun := fun i =>
        let child := childEmbedding i
        ⟨child.1, (Finset.mem_filter.mp child.2).1⟩
      inj' := by
        intro i j hij
        apply childEmbedding.injective
        apply Subtype.ext
        exact congrArg
          (fun x : ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a) => x.1)
          hij }

/-- Immediate-child attachment slot with its parent equation exposed. -/
abbrev PlanarLensChildAttachment
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  {c : PlanarInwardLensOccurrence axis hn2 hT root //
    (PlanarInwardLensForest axis hn2 hn3 hT root).parent c = some a}

noncomputable def planarLensLocalDebtAttachmentEmbedding
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    PlanarLensLocalDebt axis hn2 hn3 hT root a ↪
      PlanarLensChildAttachment axis hn2 hn3 hT root a where
  toFun q :=
    let c := planarLensLocalDebtImmediateChildEmbedding axis hn2 hn3 hT root a q
    ⟨c.1, by
      exact (Finset.mem_filter.mp c.2).2⟩
  inj' := by
    intro q r hqr
    apply (planarLensLocalDebtImmediateChildEmbedding axis hn2 hn3 hT root a).injective
    apply Subtype.ext
    exact congrArg
      (fun x : PlanarLensChildAttachment axis hn2 hn3 hT root a => x.1) hqr

/-- A coordinate-labelled cotree edge genuinely passes from a child shore into
the shell of its planar parent. -/
def PlanarInwardLensOccurrence.CotreeTransitionCrossesToParent
    {root : GridVertex n n}
    (a parent : PlanarInwardLensOccurrence axis hn2 hT root)
    (e : LabelledCotreeTransition T) : Prop :=
  let endpoints := e.1.primalEndpoints
  let childRegion := planarInwardLensShoreRegion axis hn2 hT a
  let parentRegion := planarInwardLensShoreRegion axis hn2 hT parent
  (endpoints.1 ∈ childRegion ∧ endpoints.2 ∈ parentRegion ∧
      endpoints.2 ∉ childRegion) ∨
    (endpoints.2 ∈ childRegion ∧ endpoints.1 ∈ parentRegion ∧
      endpoints.1 ∉ childRegion)

/-- The corrected region with all immediate child regions removed.  This is
the vertex-level shell in which a local cell or comb witness must lie. -/
def planarInwardLensShoreShell
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    Finset (GridVertex n n) :=
  planarInwardLensShoreRegion axis hn2 hT a \
    ((PlanarInwardLensForest axis hn2 hn3 hT root).children a).biUnion
      (planarInwardLensShoreRegion axis hn2 hT)

/-- A coordinate cell lies wholly in one corrected planar shore shell. -/
def PlanarLensCellInShoreShell
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (r : Fin (n - 1)) (c : Fin (n - 1)) : Prop :=
  cell00 r c ∈ planarInwardLensShoreShell axis hn2 hn3 hT a ∧
    cell01 r c ∈ planarInwardLensShoreShell axis hn2 hn3 hT a ∧
    cell11 r c ∈ planarInwardLensShoreShell axis hn2 hn3 hT a ∧
    cell10 r c ∈ planarInwardLensShoreShell axis hn2 hn3 hT a

/-- Expanded slots based at vertices which first appear in the parent shore. -/
def planarShoreDifferenceSlots
    {root : GridVertex n n}
    (child parent : PlanarInwardLensOccurrence axis hn2 hT root) :
    Finset (GridCompassSlot n n) :=
  Finset.univ.filter fun s => s.1 ∈
    planarInwardLensShoreRegion axis hn2 hT parent \
      planarInwardLensShoreRegion axis hn2 hT child

theorem planarShoreDifferenceSlots_nonempty
    {root : GridVertex n n}
    {child parent : PlanarInwardLensOccurrence axis hn2 hT root}
    (hparent : (PlanarInwardLensForest axis hn2 hn3 hT root).parent child =
      some parent) :
    (planarShoreDifferenceSlots axis hn2 hT child parent).Nonempty := by
  have hstrict :=
    (planarInwardLensParent_eq_some_iff axis hn2 hT hn3 child parent).1 hparent |>.1
  have hdiff : (planarInwardLensShoreRegion axis hn2 hT parent \
      planarInwardLensShoreRegion axis hn2 hT child).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    intro hreverse
    exact hstrict.ne (Finset.Subset.antisymm hstrict.1 hreverse)
  obtain ⟨v, hv⟩ := hdiff
  refine ⟨(v, .north), ?_⟩
  simp only [planarShoreDifferenceSlots, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact hv

/-- Forward expanded-contour rank from the same canonical anchor used for
ordered merger tokens. -/
def planarExpandedSlotForwardRank (s : GridCompassSlot n n) : Nat :=
  forwardCycleRank (GridExpandedContour.equiv (T := T))
    (canonicalContourRankAnchor axis hn2 hT)
    (fun x => GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT
      (canonicalContourRankAnchor axis hn2 hT) x) s

/-- Canonical first slot, in expanded-contour order, whose base vertex lies in
the difference between a child shore and its planar parent. -/
noncomputable def planarFirstDifferenceSlot
    {root : GridVertex n n}
    (child parent : PlanarInwardLensOccurrence axis hn2 hT root)
    (hparent : (PlanarInwardLensForest axis hn2 hn3 hT root).parent child =
      some parent) : GridCompassSlot n n :=
  Classical.choose (Finset.exists_min_image
    (planarShoreDifferenceSlots axis hn2 hT child parent)
    (planarExpandedSlotForwardRank axis hn2 hT)
    (planarShoreDifferenceSlots_nonempty axis hn2 hn3 hT hparent))

theorem planarFirstDifferenceSlot_mem
    {root : GridVertex n n}
    (child parent : PlanarInwardLensOccurrence axis hn2 hT root)
    (hparent : (PlanarInwardLensForest axis hn2 hn3 hT root).parent child =
      some parent) :
    planarFirstDifferenceSlot axis hn2 hn3 hT child parent hparent ∈
      planarShoreDifferenceSlots axis hn2 hT child parent :=
  (Classical.choose_spec (Finset.exists_min_image
    (planarShoreDifferenceSlots axis hn2 hT child parent)
    (planarExpandedSlotForwardRank axis hn2 hT)
    (planarShoreDifferenceSlots_nonempty axis hn2 hn3 hT hparent))).1

theorem planarFirstDifferenceSlot_rank_le
    {root : GridVertex n n}
    (child parent : PlanarInwardLensOccurrence axis hn2 hT root)
    (hparent : (PlanarInwardLensForest axis hn2 hn3 hT root).parent child =
      some parent)
    {s : GridCompassSlot n n}
    (hs : s ∈ planarShoreDifferenceSlots axis hn2 hT child parent) :
    planarExpandedSlotForwardRank axis hn2 hT
        (planarFirstDifferenceSlot axis hn2 hn3 hT child parent hparent) ≤
      planarExpandedSlotForwardRank axis hn2 hT s :=
  (Classical.choose_spec (Finset.exists_min_image
    (planarShoreDifferenceSlots axis hn2 hT child parent)
    (planarExpandedSlotForwardRank axis hn2 hT)
    (planarShoreDifferenceSlots_nonempty axis hn2 hn3 hT hparent))).2 s hs

theorem planarFirstDifferenceSlot_base_mem_parent_not_child
    {root : GridVertex n n}
    (child parent : PlanarInwardLensOccurrence axis hn2 hT root)
    (hparent : (PlanarInwardLensForest axis hn2 hn3 hT root).parent child =
      some parent) :
    (planarFirstDifferenceSlot axis hn2 hn3 hT child parent hparent).1 ∈
        planarInwardLensShoreRegion axis hn2 hT parent ∧
      (planarFirstDifferenceSlot axis hn2 hn3 hT child parent hparent).1 ∉
        planarInwardLensShoreRegion axis hn2 hT child := by
  simpa [planarShoreDifferenceSlots] using
    planarFirstDifferenceSlot_mem axis hn2 hn3 hT child parent hparent

/-- Exact local classification of an expanded slot.  An unoccupied direction
is either a valid omitted grid step or an incidence leaving the rectangle. -/
inductive ExpandedSlotLocalCase (s : GridCompassSlot n n) : Type where
  | occupied (h : GridExpandedContour.Occupied (T := T) s)
  | cotreeStep (target : GridVertex n n)
      (step : gridNeighbor? s.1 s.2 = some target)
      (not_adj : ¬T.Adj s.1 target)
  | boundary (outside : gridNeighbor? s.1 s.2 = none)

noncomputable def expandedSlotLocalCase (s : GridCompassSlot n n) :
    ExpandedSlotLocalCase (T := T) s := by
  by_cases hoccupied : GridExpandedContour.Occupied (T := T) s
  · exact .occupied hoccupied
  · cases hstep : gridNeighbor? s.1 s.2 with
    | none => exact .boundary hstep
    | some target =>
        exact .cotreeStep target hstep (by
          intro hadj
          apply hoccupied
          rw [GridExpandedContour.Occupied, GridDirectionalDart.mem_directionsAt]
          exact ⟨target, hstep, hadj⟩)

/-- A missing outward direction at a supported vertex is exactly one of the
existing split outer-port resources, including both copies at a corner. -/
def supportedOuterPortOfMissingDirection
    (v : GridVertex n n) (direction : GridDirection)
    (hsupport : v ∈ supportFinset (gridGraph n n \ T))
    (hmissing : gridNeighbor? v direction = none) :
    SupportedSplitOuterPortResource (T := T) := by
  cases direction with
  | north =>
      have hrow : v.1.val = 0 := by
        simp [gridNeighbor?] at hmissing
        omega
      exact .inl ⟨v, by simp [hsupport, hrow]⟩
  | east =>
      have hcol : v.2.val + 1 = n := by
        simp [gridNeighbor?] at hmissing
        omega
      exact .inr (.inr (.inr ⟨v, by simp [hsupport, hcol]⟩))
  | south =>
      have hrow : v.1.val + 1 = n := by
        simp [gridNeighbor?] at hmissing
        omega
      exact .inr (.inl ⟨v, by simp [hsupport, hrow]⟩)
  | west =>
      have hcol : v.2.val = 0 := by
        simp [gridNeighbor?] at hmissing
        omega
      exact .inr (.inr (.inl ⟨v, by simp [hsupport, hcol]⟩))

theorem supportedOuterPortOfMissingDirection_vertex
    (v : GridVertex n n) (direction : GridDirection)
    (hsupport : v ∈ supportFinset (gridGraph n n \ T))
    (hmissing : gridNeighbor? v direction = none) :
    (supportedOuterPortOfMissingDirection (T := T) v direction hsupport hmissing).vertex = v := by
  cases direction <;>
    simp [supportedOuterPortOfMissingDirection, OuterBoundaryPort.vertex]

/-- One step in the ranked shell traversal, labelled by its canonical first
difference slot. -/
noncomputable def planarShellTransitionSlot
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    Option (GridCompassSlot n n) := by
  if h : ∃ parent,
      (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = some parent then
    exact some (planarFirstDifferenceSlot axis hn2 hn3 hT a
      (Classical.choose h) (Classical.choose_spec h))
  else
    exact none

@[simp] theorem planarShellTransitionSlot_eq_none_iff
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    planarShellTransitionSlot axis hn2 hn3 hT a = none ↔
      (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = none := by
  unfold planarShellTransitionSlot
  split <;> rename_i h
  · constructor
    · intro hsome
      cases hsome
    · intro hnone
      obtain ⟨parent, hparent⟩ := h
      rw [hnone] at hparent
      cases hparent
  · simp only
    constructor
    · intro _
      cases hp : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a with
      | none => rfl
      | some parent => exact (h ⟨parent, hp⟩).elim
    · intro _
      trivial

/-- Ranked traversal state: the first coordinate preserves debt provenance and
the second moves through successive planar parents. -/
abbrev PlanarShellRankedState (root : GridVertex n n) :=
  PlanarInwardLensOccurrence axis hn2 hT root ×
    PlanarInwardLensOccurrence axis hn2 hT root

noncomputable def planarShellRankedTransitionSystem
    (root : GridVertex n n) :
    RankedTransitionSystem
      (PlanarInwardLensOccurrence axis hn2 hT root)
      (PlanarShellRankedState axis hn2 hT root)
      (GridCompassSlot n n)
      (PlanarInwardLensOccurrence axis hn2 hT root) where
  next x := Option.map (fun parent => (x.1, parent))
    ((PlanarInwardLensForest axis hn2 hn3 hT root).parent x.2)
  rank x := (PlanarInwardLensForest axis hn2 hn3 hT root).rank x.2
  rank_next := by
    intro x y hxy
    cases hp : (PlanarInwardLensForest axis hn2 hn3 hT root).parent x.2 with
    | none => simp [hp] at hxy
    | some parent =>
        simp [hp] at hxy
        subst y
        exact (PlanarInwardLensForest axis hn2 hn3 hT root).rank_parent hp
  origin x := x.1
  origin_next := by
    intro x y hxy
    cases hp : (PlanarInwardLensForest axis hn2 hn3 hT root).parent x.2 with
    | none => simp [hp] at hxy
    | some parent =>
        simp [hp] at hxy
        subst y
        rfl
  transition x := planarShellTransitionSlot axis hn2 hn3 hT x.2
  transition_some_iff_next_some := by
    intro x
    rw [ne_eq, ne_eq, not_congr
      (planarShellTransitionSlot_eq_none_iff axis hn2 hn3 hT x.2)]
    simp
  terminal x :=
    if (PlanarInwardLensForest axis hn2 hn3 hT root).parent x.2 = none then
      some x.2 else none
  terminal_some_iff_next_none := by
    intro x
    cases hp : (PlanarInwardLensForest axis hn2 hn3 hT root).parent x.2 with
    | none => simp
    | some parent => simp

theorem exists_planarShellRanked_terminal
    (root : GridVertex n n)
    (origin current : PlanarInwardLensOccurrence axis hn2 hT root) :
    ∃ y terminal,
      Relation.ReflTransGen
          (planarShellRankedTransitionSystem axis hn2 hn3 hT root).Step
          (origin, current) y ∧
        (planarShellRankedTransitionSystem axis hn2 hn3 hT root).terminal y =
          some terminal ∧ y.1 = origin :=
  (planarShellRankedTransitionSystem axis hn2 hn3 hT root).exists_terminal_same_origin
    (origin, current)

/-- REJECTED AUDIT API.  This product census retains every possible originating
merger debt/cotree-edge pair rather than one selected transition per active
debt.  Corrected theorems use `PlanarLensDebtRouting`.

Passed resources retain their originating merger debt, cotree-edge label,
and child occurrence.  Equal geometric labels therefore remain distinct when
they propagate different debt occurrences.  The parent coordinate is
proof-checked. -/
abbrev PlanarLensPassedTransition (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  {x : (((PlanarInwardLensForest axis hn2 hn3 hT root).MergerSlot ×
      LabelledCotreeTransition T) ×
        PlanarInwardLensOccurrence axis hn2 hT root) //
    (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = some x.2 ∧
      a.CotreeTransitionCrossesToParent axis hn2 hT x.2 x.1.2}

noncomputable instance labelledCotreeTransitionFintype :
    Fintype (LabelledCotreeTransition T) :=
  Fintype.ofInjective (fun e : LabelledCotreeTransition T => e.1)
    Subtype.val_injective

noncomputable instance planarLensPassedTransitionFintype
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    Fintype (PlanarLensPassedTransition axis hn2 hn3 hT root a) := Fintype.ofFinite _

theorem PlanarLensPassedTransition.parent_typed
    {root : GridVertex n n}
    {a : PlanarInwardLensOccurrence axis hn2 hT root}
    (x : PlanarLensPassedTransition axis hn2 hn3 hT root a) :
    (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = some x.1.2 :=
  x.2.1

theorem PlanarLensPassedTransition.parent_strictly_contains
    {root : GridVertex n n}
    {a : PlanarInwardLensOccurrence axis hn2 hT root}
    (x : PlanarLensPassedTransition axis hn2 hn3 hT root a) :
    planarInwardLensShoreRegion axis hn2 hT a ⊂
      planarInwardLensShoreRegion axis hn2 hT x.1.2 :=
  (planarInwardLensParent_eq_some_iff axis hn2 hT hn3 a x.1.2).1 x.2.1 |>.1

theorem PlanarLensPassedTransition.crosses_parent_shell
    {root : GridVertex n n}
    {a : PlanarInwardLensOccurrence axis hn2 hT root}
    (x : PlanarLensPassedTransition axis hn2 hn3 hT root a) :
    a.CotreeTransitionCrossesToParent axis hn2 hT x.1.2 x.1.1.2 :=
  x.2.2

def PlanarLensPassedTransition.origin
    {root : GridVertex n n}
    {a : PlanarInwardLensOccurrence axis hn2 hT root}
    (x : PlanarLensPassedTransition axis hn2 hn3 hT root a) :
    (PlanarInwardLensForest axis hn2 hn3 hT root).MergerSlot :=
  x.1.1.1

theorem planarLensPassedTransition_empty_of_isRoot
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (ha : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = none) :
    IsEmpty (PlanarLensPassedTransition axis hn2 hn3 hT root a) :=
  ⟨fun x => by
    have hx := x.2.1
    have hnone : (none : Option (PlanarInwardLensOccurrence axis hn2 hT root)) =
        some x.1.2 := ha.symm.trans hx
    cases hnone⟩

/-- Global passed transitions are explicitly occurrence-labelled by the child
region from which they leave. -/
abbrev PlanarLensPassedLedger (root : GridVertex n n) :=
  Σ a, PlanarLensPassedTransition axis hn2 hn3 hT root a

theorem planarLensPassedLedger_region_disjoint
    {root : GridVertex n n}
    {a b : PlanarInwardLensOccurrence axis hn2 hT root}
    (hab : a ≠ b)
    (x : PlanarLensPassedTransition axis hn2 hn3 hT root a)
    (y : PlanarLensPassedTransition axis hn2 hn3 hT root b) :
    (⟨a, x⟩ : PlanarLensPassedLedger axis hn2 hn3 hT root) ≠ ⟨b, y⟩ := by
  intro hxy
  exact hab (congrArg (fun z : PlanarLensPassedLedger axis hn2 hn3 hT root => z.1) hxy)

/-- The three physical U2 resource kinds, retaining their first owner. -/
abbrev PlanarLensFirstOwnedResource (root : GridVertex n n) :=
  FirstOwnedSplitOuterPorts axis hn2 hT root ⊕
    FirstOwnedInternalSupportEdges axis hn2 hT root ⊕
      FirstOwnedFreeComponentContacts axis hn2 hT root

def planarLensFirstOwnedResourceOwner
    {root : GridVertex n n} :
    PlanarLensFirstOwnedResource axis hn2 hT root →
      PlanarInwardLensOccurrence axis hn2 hT root
  | .inl p => p.owner
  | .inr (.inl e) => e.owner
  | .inr (.inr C) => C.owner

/-- Physical resources first-owned by one concrete planar region. -/
abbrev PlanarLensRegionalOwned (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  {r : PlanarLensFirstOwnedResource axis hn2 hT root //
    planarLensFirstOwnedResourceOwner axis hn2 hT r = a}

noncomputable instance planarLensRegionalOwnedFintype
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    Fintype (PlanarLensRegionalOwned axis hn2 hT root a) := Fintype.ofFinite _

/-- First-owned resources decompose disjointly by their unique owner. -/
def planarLensRegionalOwnedDecomposition (root : GridVertex n n) :
    PlanarLensFirstOwnedResource axis hn2 hT root ≃
      Σ a, PlanarLensRegionalOwned axis hn2 hT root a where
  toFun r := ⟨planarLensFirstOwnedResourceOwner axis hn2 hT r, r, rfl⟩
  invFun r := r.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨a, r, hr⟩
    subst a
    rfl

theorem card_planarLensRegionalOwnedDecomposition (root : GridVertex n n) :
    Fintype.card (PlanarLensFirstOwnedResource axis hn2 hT root) =
      ∑ a, Fintype.card (PlanarLensRegionalOwned axis hn2 hT root a) := by
  rw [Fintype.card_congr (planarLensRegionalOwnedDecomposition axis hn2 hT root),
    Fintype.card_sigma]

theorem planarLensRegionalOwned_disjoint
    {root : GridVertex n n}
    {a b : PlanarInwardLensOccurrence axis hn2 hT root}
    (hab : a ≠ b)
    (x : PlanarLensRegionalOwned axis hn2 hT root a)
    (y : PlanarLensRegionalOwned axis hn2 hT root b) : x.1 ≠ y.1 := by
  intro hxy
  apply hab
  rw [← x.2, ← y.2, hxy]

/-- Local alternatives produced by a supported cell side or a bare-comb gap.
The retained case has the exact internal-edge type used by U2; the omitted case
retains its coordinate-labelled cotree transition for later parent typing. -/
abbrev PlanarLensBoundaryAlternative :=
  RetainedInternalSupportEdgeResource (T := T) ⊕ LabelledCotreeTransition T

noncomputable def gridCellPlanarLensBoundaryAlternative
    (r : Fin (n - 1)) (c : Fin (n - 1)) :
    PlanarLensBoundaryAlternative (T := T) := by
  apply Classical.choice
  rcases gridTreeCell_internal_or_labelledCotree T hT r c with
    ⟨_side, e, _⟩ | ⟨_side, e, _⟩
  · exact ⟨.inl e⟩
  · exact ⟨.inr e⟩

noncomputable def horizontalSouthBareCombPlanarLensBoundaryAlternative
    (C : HorizontalSouthBareComb T) (i : Fin C.gapCount) :
    PlanarLensBoundaryAlternative (T := T) :=
  C.gapResourceEmbedding i

noncomputable def horizontalNorthBareCombPlanarLensBoundaryAlternative
    (C : HorizontalNorthBareComb T) (i : Fin C.gapCount) :
    PlanarLensBoundaryAlternative (T := T) :=
  C.gapResourceEmbedding i

noncomputable def verticalEastBareCombPlanarLensBoundaryAlternative
    (C : VerticalEastBareComb T) (i : Fin C.gapCount) :
    PlanarLensBoundaryAlternative (T := T) :=
  C.gapResourceEmbedding i

noncomputable def verticalWestBareCombPlanarLensBoundaryAlternative
    (C : VerticalWestBareComb T) (i : Fin C.gapCount) :
    PlanarLensBoundaryAlternative (T := T) :=
  C.gapResourceEmbedding i

/-- A local cell/comb alternative is usable in region `a` when its retained
edge is first-owned there, or its cotree label crosses from `a` to its typed
planar parent. -/
def PlanarLensBoundaryAlternative.AssignedTo
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    PlanarLensBoundaryAlternative (T := T) → Prop
  | .inl e => ∃ x : FirstOwnedInternalSupportEdges axis hn2 hT root,
      x.owner = a ∧ x.resource = e
  | .inr e => ∃ x : PlanarLensPassedTransition axis hn2 hn3 hT root a,
      x.1.1.2 = e

theorem PlanarLensBoundaryAlternative.assignedTo_owned_or_passed
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (z : PlanarLensBoundaryAlternative (T := T))
    (hz : z.AssignedTo axis hn2 hn3 hT a) :
    Nonempty (PlanarLensRegionalOwned axis hn2 hT root a ⊕
      PlanarLensPassedTransition axis hn2 hn3 hT root a) := by
  cases z with
  | inl e =>
      rcases hz with ⟨x, hxowner, _hxresource⟩
      exact ⟨.inl ⟨.inr (.inl x), hxowner⟩⟩
  | inr e =>
      rcases hz with ⟨x, _hxresource⟩
      exact ⟨.inr x⟩

def PlanarLensCellAlternativeAssigned
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (r : Fin (n - 1)) (c : Fin (n - 1)) : Prop :=
  (gridCellPlanarLensBoundaryAlternative hT r c).AssignedTo
    axis hn2 hn3 hT a

def PlanarLensBareCombAlternativeAssigned
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (C : HorizontalSouthBareComb T) (i : Fin C.gapCount) : Prop :=
  (horizontalSouthBareCombPlanarLensBoundaryAlternative C i).AssignedTo
    axis hn2 hn3 hT a

def PlanarLensHorizontalNorthBareCombAlternativeAssigned
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (C : HorizontalNorthBareComb T) (i : Fin C.gapCount) : Prop :=
  (horizontalNorthBareCombPlanarLensBoundaryAlternative C i).AssignedTo
    axis hn2 hn3 hT a

def PlanarLensVerticalEastBareCombAlternativeAssigned
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (C : VerticalEastBareComb T) (i : Fin C.gapCount) : Prop :=
  (verticalEastBareCombPlanarLensBoundaryAlternative C i).AssignedTo
    axis hn2 hn3 hT a

def PlanarLensVerticalWestBareCombAlternativeAssigned
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (C : VerticalWestBareComb T) (i : Fin C.gapCount) : Prop :=
  (verticalWestBareCombPlanarLensBoundaryAlternative C i).AssignedTo
    axis hn2 hn3 hT a

/-- REJECTED AUDIT API.  The demands visible in one region: its own merger-excess occurrences and
the occurrence-labelled transitions arriving from each immediate child. -/
abbrev PlanarLensRegionalDemand (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  PlanarLensLocalDebt axis hn2 hn3 hT root a ⊕
    Σ c : ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a),
      PlanarLensPassedTransition axis hn2 hn3 hT root c.1

/-- REJECTED AUDIT API.  A completed geometric assignment for one region.  Its codomain enforces
`AssignedTo`: each demand is sent either to a resource first-owned by `a` or to
an occurrence-labelled transition passed from `a` to its parent.  Injectivity
preserves equal geometric transition labels carried by distinct occurrences. -/
abbrev PlanarLensRegionalAssignment (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  PlanarLensRegionalDemand axis hn2 hn3 hT root a ↪
    (PlanarLensRegionalOwned axis hn2 hT root a ⊕
      PlanarLensPassedTransition axis hn2 hn3 hT root a)

theorem sum_finset_subtype_eq_sum_filter
    {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (f : V → Nat) :
    (∑ x : ↥s, f x.1) = ∑ x ∈ s, f x := by
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach s f

/-- Child-to-parent passed fibers balance globally: every non-root child occurs
once in its parent's child finset, while root fibers are empty. -/
theorem parentForest_sum_children_eq_sum_of_root_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ParentForest V) (passed : V → Nat)
    (hroot : ∀ v, F.parent v = none → passed v = 0) :
    ∑ a, ∑ c ∈ F.children a, passed c = ∑ c, passed c := by
  classical
  simp only [ParentForest.children, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  cases hp : F.parent c with
  | none => simp [hroot c hp]
  | some p => simp

/-- Pure telescoping: local debt plus transitions arriving from children is
paid by local ownership plus the transition passed to the parent. -/
theorem parentForest_global_le_of_regional_telescope
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ParentForest V) (debt owned passed : V → Nat)
    (hroot : ∀ v, F.parent v = none → passed v = 0)
    (hlocal : ∀ v,
      debt v + ∑ c ∈ F.children v, passed c ≤ owned v + passed v) :
    ∑ v, debt v ≤ ∑ v, owned v := by
  have hsum := Finset.sum_le_sum fun v (_hv : v ∈ (Finset.univ : Finset V)) =>
    hlocal v
  simp only [Finset.sum_add_distrib] at hsum
  rw [parentForest_sum_children_eq_sum_of_root_zero F passed hroot] at hsum
  omega

/-- REJECTED AUDIT API: product-census one-region numerical statement. -/
def CanonicalUpperU3RegionInequality
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) : Prop :=
  Fintype.card (PlanarLensLocalDebt axis hn2 hn3 hT root a) +
      ∑ c : ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a),
        Fintype.card (PlanarLensPassedTransition axis hn2 hn3 hT root c.1) ≤
    Fintype.card (PlanarLensRegionalOwned axis hn2 hT root a) +
      Fintype.card (PlanarLensPassedTransition axis hn2 hn3 hT root a)

/-- An injective geometric assignment proves the local inequality without any
global resource or waste estimate. -/
theorem canonicalUpperU3_regionInequality_of_assignment
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (assignment : PlanarLensRegionalAssignment axis hn2 hn3 hT root a) :
    CanonicalUpperU3RegionInequality axis hn2 hn3 hT root a := by
  have hcard := Fintype.card_le_of_injective assignment assignment.injective
  simpa only [CanonicalUpperU3RegionInequality, PlanarLensRegionalDemand, PlanarLensRegionalAssignment,
    Fintype.card_sum, Fintype.card_sigma] using hcard

/-- Leaf planar regions are an exhaustive structural subtype on which U3 is
automatic: they have neither local merger excess nor arriving child passes. -/
theorem canonicalUpperU3_regionInequality_of_mem_leaves
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (ha : a ∈ (PlanarInwardLensForest axis hn2 hn3 hT root).leaves) :
    CanonicalUpperU3RegionInequality axis hn2 hn3 hT root a := by
  let F := PlanarInwardLensForest axis hn2 hn3 hT root
  have hchildCount : F.childCount a = 0 := by
    simpa [ParentForest.leaves] using ha
  have hchildren : F.children a = ∅ := Finset.card_eq_zero.mp hchildCount
  let : IsEmpty (PlanarLensLocalDebt axis hn2 hn3 hT root a) :=
    ⟨fun x => by
      have hmerger : F.mergerExcessAt x.1.1 = 0 := by
        rw [x.2]
        simp [ParentForest.mergerExcessAt, hchildCount]
      exact Fin.elim0 (Fin.cast hmerger x.1.2)⟩
  have hdebt : Fintype.card (PlanarLensLocalDebt axis hn2 hn3 hT root a) = 0 :=
    Fintype.card_eq_zero
  change Fintype.card (PlanarLensLocalDebt axis hn2 hn3 hT root a) +
      ∑ c : ↥(F.children a),
        Fintype.card (PlanarLensPassedTransition axis hn2 hn3 hT root c.1) ≤ _
  rw [hdebt, hchildren]
  simp

/-- The sole remaining structural class after the unconditional leaf proof.
It includes unary propagation regions and genuine planar reconvergences. -/
abbrev PlanarLensNonleafReconvergenceRegion (root : GridVertex n n) :=
  {a : PlanarInwardLensOccurrence axis hn2 hT root //
    a ∉ (PlanarInwardLensForest axis hn2 hn3 hT root).leaves}

abbrev PlanarLensUnaryPropagationRegion (root : GridVertex n n) :=
  {a : PlanarInwardLensOccurrence axis hn2 hT root //
    (PlanarInwardLensForest axis hn2 hn3 hT root).childCount a = 1}

abbrev PlanarLensGenuineReconvergenceRegion (root : GridVertex n n) :=
  {a : PlanarInwardLensOccurrence axis hn2 hT root //
    2 ≤ (PlanarInwardLensForest axis hn2 hn3 hT root).childCount a}

/-- The unique child of a unary propagation region. -/
noncomputable def planarLensUnaryChild
    {root : GridVertex n n}
    (a : PlanarLensUnaryPropagationRegion axis hn2 hn3 hT root) :
    PlanarInwardLensOccurrence axis hn2 hT root :=
  Classical.choose (Finset.card_eq_one.mp (by
    simpa [ParentForest.childCount] using a.2))

theorem planarLensUnary_children_eq_singleton
    {root : GridVertex n n}
    (a : PlanarLensUnaryPropagationRegion axis hn2 hn3 hT root) :
    (PlanarInwardLensForest axis hn2 hn3 hT root).children a.1 =
      {planarLensUnaryChild axis hn2 hn3 hT a} :=
  Classical.choose_spec (Finset.card_eq_one.mp (by
    simpa [ParentForest.childCount] using a.2))

theorem planarLensUnaryChild_parent
    {root : GridVertex n n}
    (a : PlanarLensUnaryPropagationRegion axis hn2 hn3 hT root) :
    (PlanarInwardLensForest axis hn2 hn3 hT root).parent
        (planarLensUnaryChild axis hn2 hn3 hT a) = some a.1 := by
  have hmem : planarLensUnaryChild axis hn2 hn3 hT a ∈
      (PlanarInwardLensForest axis hn2 hn3 hT root).children a.1 := by
    rw [planarLensUnary_children_eq_singleton axis hn2 hn3 hT a]
    simp
  simpa [ParentForest.children] using hmem

/-- Canonical coordinate witness for the only child-to-region boundary in a
unary propagation region. -/
noncomputable def planarLensUnaryFirstDifferenceSlot
    {root : GridVertex n n}
    (a : PlanarLensUnaryPropagationRegion axis hn2 hn3 hT root) :
    GridCompassSlot n n :=
  planarFirstDifferenceSlot axis hn2 hn3 hT
    (planarLensUnaryChild axis hn2 hn3 hT a) a.1
    (planarLensUnaryChild_parent axis hn2 hn3 hT a)

theorem planarLensUnaryBoundaryPort_exposed
    {root : GridVertex n n}
    (a : PlanarLensUnaryPropagationRegion axis hn2 hn3 hT root)
    (hsupport : (planarLensUnaryFirstDifferenceSlot axis hn2 hn3 hT a).1 ∈
      supportFinset (gridGraph n n \ T))
    (hmissing : gridNeighbor?
      (planarLensUnaryFirstDifferenceSlot axis hn2 hn3 hT a).1
      (planarLensUnaryFirstDifferenceSlot axis hn2 hn3 hT a).2 = none) :
    a.1.ExposesSplitOuterPort axis hn2 hT
      (supportedOuterPortOfMissingDirection (T := T)
        (planarLensUnaryFirstDifferenceSlot axis hn2 hn3 hT a).1
        (planarLensUnaryFirstDifferenceSlot axis hn2 hn3 hT a).2
        hsupport hmissing) := by
  rw [PlanarInwardLensOccurrence.ExposesSplitOuterPort,
    supportedOuterPortOfMissingDirection_vertex]
  exact (planarFirstDifferenceSlot_base_mem_parent_not_child
    axis hn2 hn3 hT (planarLensUnaryChild axis hn2 hn3 hT a) a.1
      (planarLensUnaryChild_parent axis hn2 hn3 hT a)).1

/-- The original all-crossing unary gate.  This is intentionally retained as a
diagnostic: it counts every origin/edge crossing pair, not only transitions
selected by a ranked propagation chain. -/
def CanonicalUpperU3AllCrossingUnaryAssignmentGate (root : GridVertex n n) : Prop :=
  ∀ a : PlanarLensUnaryPropagationRegion axis hn2 hn3 hT root,
    Nonempty (PlanarLensRegionalAssignment axis hn2 hn3 hT root a.1)

/-- Exact structural obstruction to the all-crossing gate.  At a unary root,
an incoming crossing occurrence has nowhere to go when no physical resource is
first-owned there. -/
theorem no_planarLensRegionalAssignment_of_unaryRoot_obstruction
    {root : GridVertex n n}
    (a : PlanarLensUnaryPropagationRegion axis hn2 hn3 hT root)
    (hroot : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a.1 = none)
    (howned : IsEmpty (PlanarLensRegionalOwned axis hn2 hT root a.1))
    (incoming : PlanarLensPassedTransition axis hn2 hn3 hT root
      (planarLensUnaryChild axis hn2 hn3 hT a)) :
    ¬Nonempty (PlanarLensRegionalAssignment axis hn2 hn3 hT root a.1) := by
  intro hassignment
  let child : ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a.1) :=
    ⟨planarLensUnaryChild axis hn2 hn3 hT a, by
      rw [planarLensUnary_children_eq_singleton axis hn2 hn3 hT a]
      simp⟩
  let demand : PlanarLensRegionalDemand axis hn2 hn3 hT root a.1 :=
    .inr ⟨child, incoming⟩
  let : IsEmpty (PlanarLensRegionalOwned axis hn2 hT root a.1) := howned
  let : IsEmpty (PlanarLensPassedTransition axis hn2 hn3 hT root a.1) :=
    planarLensPassedTransition_empty_of_isRoot axis hn2 hn3 hT a.1 hroot
  exact isEmptyElim (hassignment.some demand)

/-- A ranked U3 construction selects a finite subledger of the geometrically
possible origin-labelled crossing transitions. -/
structure PlanarLensPassSelection (root : GridVertex n n) where
  selected : ∀ a : PlanarInwardLensOccurrence axis hn2 hT root,
    Finset (PlanarLensPassedTransition axis hn2 hn3 hT root a)

abbrev PlanarLensSelectedPassed
    {root : GridVertex n n}
    (selection : PlanarLensPassSelection axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  ↥(selection.selected a)

abbrev PlanarLensSelectedRegionalDemand
    {root : GridVertex n n}
    (selection : PlanarLensPassSelection axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  PlanarLensLocalDebt axis hn2 hn3 hT root a ⊕
    Σ c : ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a),
      PlanarLensSelectedPassed axis hn2 hn3 hT selection c.1

abbrev PlanarLensSelectedRegionalAssignment
    {root : GridVertex n n}
    (selection : PlanarLensPassSelection axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  PlanarLensSelectedRegionalDemand axis hn2 hn3 hT selection a ↪
    (PlanarLensRegionalOwned axis hn2 hT root a ⊕
      PlanarLensSelectedPassed axis hn2 hn3 hT selection a)

/-- Corrected unary gate: only transition occurrences actually selected by the
ranked propagation construction enter the regional ledger. -/
def CanonicalUpperU3UnaryAssignmentGate
    {root : GridVertex n n}
    (selection : PlanarLensPassSelection axis hn2 hn3 hT root) : Prop :=
  ∀ a : PlanarLensUnaryPropagationRegion axis hn2 hn3 hT root,
    Nonempty (PlanarLensSelectedRegionalAssignment axis hn2 hn3 hT selection a.1)

def planarLensEmptyPassSelection (root : GridVertex n n) :
    PlanarLensPassSelection axis hn2 hn3 hT root where
  selected := fun _ => ∅

theorem planarLensLocalDebt_isEmpty_of_unary
    {root : GridVertex n n}
    (a : PlanarLensUnaryPropagationRegion axis hn2 hn3 hT root) :
    IsEmpty (PlanarLensLocalDebt axis hn2 hn3 hT root a.1) :=
  ⟨fun x => by
    have hcount :
        (PlanarInwardLensForest axis hn2 hn3 hT root).childCount x.1.1 = 1 := by
      rw [x.2]
      exact a.2
    have hzero :
        (PlanarInwardLensForest axis hn2 hn3 hT root).mergerExcessAt x.1.1 = 0 := by
      simp [ParentForest.mergerExcessAt, hcount]
    exact Fin.elim0 (Fin.cast hzero x.1.2)⟩

/-- Contracting all unary pass edges closes the corrected unary gate: unary
regions have no local merger debt, and no selected transition arrives there.
Transitions created at genuine mergers must subsequently target the next
non-unary region rather than every immediate planar parent. -/
theorem canonicalUpperU3_emptySelection_unaryAssignmentGate
    (root : GridVertex n n) :
    CanonicalUpperU3UnaryAssignmentGate axis hn2 hn3 hT
      (planarLensEmptyPassSelection axis hn2 hn3 hT root) := by
  intro a
  let := planarLensLocalDebt_isEmpty_of_unary axis hn2 hn3 hT a
  refine ⟨{
    toFun := fun demand => ?_
    inj' := by
      intro demand
      rcases demand with debt | incoming
      · exact isEmptyElim debt
      · rcases incoming with ⟨child, selected⟩
        exact (Finset.notMem_empty selected.1 selected.2).elim }⟩
  rcases demand with debt | incoming
  · exact isEmptyElim debt
  · rcases incoming with ⟨child, selected⟩
    exact (Finset.notMem_empty selected.1 selected.2).elim

/-! ### Corrected active-debt routing -/

abbrev PlanarLensOriginalDebt (root : GridVertex n n) :=
  (PlanarInwardLensForest axis hn2 hn3 hT root).MergerSlot

/-- Globally and injectively select one immediate planar child for every
original merger-excess slot. -/
noncomputable def planarLensOriginalDebtImmediateChildEmbedding
    (root : GridVertex n n) :
    PlanarLensOriginalDebt axis hn2 hn3 hT root ↪
      PlanarInwardLensOccurrence axis hn2 hT root := by
  let F := PlanarInwardLensForest axis hn2 hn3 hT root
  let selected := F.mergerSlotPhysicalChildEmbedding (fun _ => True) (by
    intro v
    simp [ParentForest.nonphysicalChildren])
  exact {
    toFun := fun debt => (selected debt).1
    inj' := by
      intro debt other h
      apply selected.injective
      exact Subtype.ext h }

/-- The selected child occurrence launches at its own first-stop merger slot.
Distinct original debts launch at distinct mergers. -/
noncomputable def planarLensOriginalDebtFirstStopMergerEmbedding
    (root : GridVertex n n) :
    PlanarLensOriginalDebt axis hn2 hn3 hT root ↪
      (planeChannelForest axis hn2 hT).forest.MergerSlot :=
  (planarLensOriginalDebtImmediateChildEmbedding axis hn2 hn3 hT root).trans
    ((planarInwardLensOccurrenceLensEmbedding axis hn2 hT root).trans
      { toFun := MarkedCycleFirstStop.ReconvergenceLens.mergerSlot
        inj' := by
          intro L K h
          exact MarkedCycleFirstStop.ReconvergenceLens.ext h })

@[simp] theorem planarLensOriginalDebtFirstStopMergerEmbedding_apply
    (root : GridVertex n n)
    (debt : PlanarLensOriginalDebt axis hn2 hn3 hT root) :
    planarLensOriginalDebtFirstStopMergerEmbedding axis hn2 hn3 hT root debt =
      (planarLensOriginalDebtImmediateChildEmbedding
        axis hn2 hn3 hT root debt).lens.mergerSlot := rfl

/-- Package the selected first-stop merger as a noninternal terminal token.
This records a component carrier; it does not count the tree edge as an
internal resource. -/
noncomputable def planarLensOriginalDebtNoninternalTokenEmbedding
    (root : GridVertex n n) :
    PlanarLensOriginalDebt axis hn2 hn3 hT root ↪
      NoninternalTreeEdgeToken
        (supportFinset (gridGraph n n \ T))
        (terminalTreeEdgeEmbedding axis hn2 hn3 hT) where
  toFun debt :=
    let merger := planarLensOriginalDebtFirstStopMergerEmbedding
      axis hn2 hn3 hT root debt
    ⟨.inl merger,
      terminalTreeEdgeEmbedding_isNoninternal axis hn2 hn3 hT (.inl merger)⟩
  inj' := by
    intro debt other h
    apply (planarLensOriginalDebtFirstStopMergerEmbedding
      axis hn2 hn3 hT root).injective
    exact Sum.inl.inj (congrArg Subtype.val h)

@[simp] theorem planarLensOriginalDebtNoninternalTokenEmbedding_value
    (root : GridVertex n n)
    (debt : PlanarLensOriginalDebt axis hn2 hn3 hT root) :
    (planarLensOriginalDebtNoninternalTokenEmbedding
      axis hn2 hn3 hT root debt).1 =
        .inl (planarLensOriginalDebtFirstStopMergerEmbedding
          axis hn2 hn3 hT root debt) := rfl

/-- Occurrence-labelled geometric outcomes of event routing.  These are events,
not fresh or paid resources. -/
inductive PlanarLensGeometricEvent (root : GridVertex n n) where
  | supportedOuterPort
      (origin : PlanarLensOriginalDebt axis hn2 hn3 hT root)
      (occurrence : PlanarInwardLensOccurrence axis hn2 hT root)
      (port : SupportedSplitOuterPortResource (T := T))
  | retainedInternalSupportEdge
      (origin : PlanarLensOriginalDebt axis hn2 hn3 hT root)
      (occurrence : PlanarInwardLensOccurrence axis hn2 hT root)
      (edge : RetainedInternalSupportEdgeResource (T := T))
  | freeComponentContact
      (origin : PlanarLensOriginalDebt axis hn2 hn3 hT root)
      (occurrence : PlanarInwardLensOccurrence axis hn2 hT root)
      (contact : FreeComponentContactResource (T := T))
  | omittedEdgeContinuation
      (origin : PlanarLensOriginalDebt axis hn2 hn3 hT root)
      (occurrence : PlanarInwardLensOccurrence axis hn2 hT root)
      (edge : LabelledCotreeTransition T)
  deriving Fintype

/-- One original debt escaping from a parentless planar root along the expanded
contour. -/
structure PlanarLensRootEscapeState (root : GridVertex n n) where
  origin : PlanarLensOriginalDebt axis hn2 hn3 hT root
  occurrence : PlanarInwardLensOccurrence axis hn2 hT root
  slot : GridCompassSlot n n

noncomputable instance planarLensRootEscapeStateFintype
    (root : GridVertex n n) :
    Fintype (PlanarLensRootEscapeState axis hn2 hn3 hT root) :=
  Fintype.ofInjective
    (fun state => (state.origin, state.occurrence, state.slot)) (by
      intro state other h
      cases state
      cases other
      simp_all)

def planarLensRootEscapeRank
    {root : GridVertex n n}
    (state : PlanarLensRootEscapeState axis hn2 hn3 hT root) : Nat :=
  (PlanarInwardLensForest axis hn2 hn3 hT root).rank state.occurrence *
      (Fintype.card (GridCompassSlot n n) + 1) +
    (firstStop axis hn2 hT).distance state.slot

noncomputable def planarLensRootEscapeSystem
    (root : GridVertex n n) :
    RankedTransitionSystem
      (PlanarLensOriginalDebt axis hn2 hn3 hT root)
      (PlanarLensRootEscapeState axis hn2 hn3 hT root)
      (GridCompassSlot n n)
      (PlanarLensGeometricEvent axis hn2 hn3 hT root) where
  next state :=
    if state.slot ∈ markedSlots (T := T) then none else
      some { state with slot := GridExpandedContour.equiv state.slot }
  rank := planarLensRootEscapeRank axis hn2 hn3 hT
  rank_next := by
    intro state next hnext
    split at hnext <;> rename_i hmarked
    · simp at hnext
    · simp only [Option.some.injEq] at hnext
      subst next
      unfold planarLensRootEscapeRank
      have hdecrease := (firstStop axis hn2 hT).distance_f_lt hmarked
      have hdecrease' :
          (firstStop axis hn2 hT).distance
              (GridExpandedContour.equiv (T := T) state.slot) <
            (firstStop axis hn2 hT).distance state.slot := by
        simpa [firstStop] using hdecrease
      change
        (PlanarInwardLensForest axis hn2 hn3 hT root).rank state.occurrence *
              (Fintype.card (GridCompassSlot n n) + 1) +
            (firstStop axis hn2 hT).distance
              (GridExpandedContour.equiv (T := T) state.slot) <
          (PlanarInwardLensForest axis hn2 hn3 hT root).rank state.occurrence *
              (Fintype.card (GridCompassSlot n n) + 1) +
            (firstStop axis hn2 hT).distance state.slot
      exact Nat.add_lt_add_left hdecrease' _
  origin := PlanarLensRootEscapeState.origin
  origin_next := by
    intro state next hnext
    split at hnext <;> rename_i hmarked
    · simp at hnext
    · simp only [Option.some.injEq] at hnext
      rw [← hnext]
  transition state :=
    if state.slot ∈ markedSlots (T := T) then none else some state.slot
  transition_some_iff_next_some := by
    intro state
    by_cases hmarked : state.slot ∈ markedSlots (T := T) <;> simp [hmarked]
  terminal state :=
    if hmarked : state.slot ∈ markedSlots (T := T) then
      some (.supportedOuterPort state.origin state.occurrence
        (outerPortOfMarkedSlot (T := T) ⟨state.slot, hmarked⟩))
    else none
  terminal_some_iff_next_none := by
    intro state
    by_cases hmarked : state.slot ∈ markedSlots (T := T) <;> simp [hmarked]

theorem planarLensRootEscape_exists_event
    {root : GridVertex n n}
    (state : PlanarLensRootEscapeState axis hn2 hn3 hT root) :
    ∃ terminal event,
      Relation.ReflTransGen
          (planarLensRootEscapeSystem axis hn2 hn3 hT root).Step state terminal ∧
        (planarLensRootEscapeSystem axis hn2 hn3 hT root).terminal terminal =
          some event ∧ terminal.origin = state.origin :=
  by
    simpa only [planarLensRootEscapeSystem] using
      RankedTransitionSystem.exists_terminal_same_origin
        (planarLensRootEscapeSystem axis hn2 hn3 hT root) state

/-- Structural no-go for pointwise first-event payment.  Whenever two distinct
canonical starts have reconverged at one used state, every assignment factoring
through their first marked terminal identifies them.  Occurrence labels can
retain the distinction, but a raw terminal resource cannot recover it. -/
theorem canonicalFirstMarkedEvent_not_injective_of_reconvergence
    {R : Type*}
    (event : (firstStop axis hn2 hT).State → R)
    {x : (firstStop axis hn2 hT).State}
    {s t : ↥(firstStop axis hn2 hT).starts}
    (hne : s ≠ t)
    (hs : s ∈ (firstStop axis hn2 hT).origins x)
    (ht : t ∈ (firstStop axis hn2 hT).origins x) :
    ¬Function.Injective
      (fun start => event ((firstStop axis hn2 hT).terminalState start)) := by
  intro hinjective
  apply hne
  apply hinjective
  exact congrArg event
    (MarkedCycleFirstStop.ReconvergenceLens.terminalState_eq_of_mem_origins hs ht)

/-- A marked root-escape terminal is supported, whereas free-component contacts
live in the complementary induced graph.  Hence the terminal vertex itself can
never be used as a raw free-component contact. -/
theorem rootEscapeOuterPort_vertex_not_free
    {root : GridVertex n n}
    (_origin : PlanarLensOriginalDebt axis hn2 hn3 hT root)
    (_occurrence : PlanarInwardLensOccurrence axis hn2 hT root)
    (port : SupportedSplitOuterPortResource (T := T)) :
    port.vertex ∉ (Finset.univ : Finset (GridVertex n n)) \
      supportFinset (gridGraph n n \ T) := by
  intro hfree
  exact (Finset.mem_sdiff.mp hfree).2 port.vertex_mem

/-- A retained child interface used only as a transport lane.  Its collar edge
is not inserted into the physical resource ledger. -/
structure PlanarLensInterfaceGapWitness
    (root : GridVertex n n)
    (parent : PlanarInwardLensOccurrence axis hn2 hT root) where
  child : PlanarInwardLensOccurrence axis hn2 hT root
  child_parent : (PlanarInwardLensForest axis hn2 hn3 hT root).parent child =
    some parent

namespace PlanarLensInterfaceGapWitness

def retainedDart
    {root : GridVertex n n}
    {parent : PlanarInwardLensOccurrence axis hn2 hT root}
    (lane : PlanarLensInterfaceGapWitness axis hn2 hn3 hT root parent) :
    GridDirectionalDart T :=
  (lane.child.rootedShore axis hn2 hT).1

def slot
    {root : GridVertex n n}
    {parent : PlanarInwardLensOccurrence axis hn2 hT root}
    (lane : PlanarLensInterfaceGapWitness axis hn2 hn3 hT root parent) :
    GridCompassSlot n n :=
  GridExpandedContour.slotOfDart lane.retainedDart

theorem slot_occupied
    {root : GridVertex n n}
    {parent : PlanarInwardLensOccurrence axis hn2 hT root}
    (lane : PlanarLensInterfaceGapWitness axis hn2 hn3 hT root parent) :
    GridExpandedContour.Occupied (T := T) lane.slot :=
  GridExpandedContour.occupied_slotOfDart lane.retainedDart

def collarEdge
    {root : GridVertex n n}
    {parent : PlanarInwardLensOccurrence axis hn2 hT root}
    (lane : PlanarLensInterfaceGapWitness axis hn2 hn3 hT root parent) :
    Sym2 (GridVertex (GridExpandedContour.collarSize n)
      (GridExpandedContour.collarSize n)) :=
  GridExpandedContour.localEdge (T := T) lane.slot false

def attachmentEmbedding
    (root : GridVertex n n)
    (parent : PlanarInwardLensOccurrence axis hn2 hT root) :
    PlanarLensChildAttachment axis hn2 hn3 hT root parent ↪
      PlanarLensInterfaceGapWitness axis hn2 hn3 hT root parent where
  toFun child := ⟨child.1, child.2⟩
  inj' := by
    intro child other h
    exact Subtype.ext (congrArg PlanarLensInterfaceGapWitness.child h)

noncomputable def collarEdgeEmbedding
    (root : GridVertex n n)
    (parent : PlanarInwardLensOccurrence axis hn2 hT root) :
    PlanarLensInterfaceGapWitness axis hn2 hn3 hT root parent ↪
      Sym2 (GridVertex (GridExpandedContour.collarSize n)
        (GridExpandedContour.collarSize n)) where
  toFun := collarEdge axis hn2 hn3 hT
  inj' := by
    intro lane other hedge
    change GridExpandedContour.localEdge (T := T) lane.slot false =
      GridExpandedContour.localEdge (T := T) other.slot false at hedge
    have hpairs : (lane.slot, false) = (other.slot, false) :=
      GridExpandedContour.localEdge_injective (T := T) hedge
    have hslots := congrArg Prod.fst hpairs
    have hdarts := GridExpandedContour.slotOfDart_injective hslots
    have hrooted : lane.child.rootedShore axis hn2 hT =
        other.child.rootedShore axis hn2 hT := by
      apply Subtype.ext
      exact hdarts
    have hchild := PlanarInwardLensOccurrence.rootedShore_injective
      axis hn2 hT hn3 root hrooted
    cases lane
    cases other
    simp_all

end PlanarLensInterfaceGapWitness

/-- Canonical `q - 1` interface lanes at a reconvergence. -/
noncomputable def planarLensLocalDebtInterfaceGapEmbedding
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    PlanarLensLocalDebt axis hn2 hn3 hT root a ↪
      PlanarLensInterfaceGapWitness axis hn2 hn3 hT root a :=
  (planarLensLocalDebtAttachmentEmbedding axis hn2 hn3 hT root a).trans
    (PlanarLensInterfaceGapWitness.attachmentEmbedding axis hn2 hn3 hT root a)

noncomputable def planarLensLocalDebtInterfaceCollarEdgeEmbedding
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    PlanarLensLocalDebt axis hn2 hn3 hT root a ↪
      Sym2 (GridVertex (GridExpandedContour.collarSize n)
        (GridExpandedContour.collarSize n)) :=
  (planarLensLocalDebtInterfaceGapEmbedding axis hn2 hn3 hT root a).trans
    (PlanarLensInterfaceGapWitness.collarEdgeEmbedding axis hn2 hn3 hT root a)

abbrev PlanarLensRootEscapeTransition
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  {state : PlanarLensRootEscapeState axis hn2 hn3 hT root //
    state.occurrence = a}

noncomputable def planarLensCanonicalRootEscape
    {root : GridVertex n n}
    (origin : PlanarLensOriginalDebt axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    PlanarLensRootEscapeTransition axis hn2 hn3 hT root a :=
  ⟨{
    origin := origin
    occurrence := a
    slot := GridExpandedContour.slotOfDart (a.rootedShore axis hn2 hT).1 }, rfl⟩

abbrev PlanarLensTransportLabel
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  LabelledCotreeTransition T ⊕
    (PlanarLensInterfaceGapWitness axis hn2 hn3 hT root a ⊕
      PlanarLensRootEscapeTransition axis hn2 hn3 hT root a)

noncomputable def planarLensLocalDebtInterfaceLabelEmbedding
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
  PlanarLensLocalDebt axis hn2 hn3 hT root a ↪
      PlanarLensTransportLabel axis hn2 hn3 hT root a :=
  (planarLensLocalDebtInterfaceGapEmbedding axis hn2 hn3 hT root a).trans
    { toFun := fun lane => .inr (.inl lane)
      inj' := by
        intro x y hxy
        exact Sum.inl.inj (Sum.inr.inj hxy) }

def PlanarLensTransportLabel.ValidForParent
    {root : GridVertex n n}
    (a parent : PlanarInwardLensOccurrence axis hn2 hT root) :
  PlanarLensTransportLabel axis hn2 hn3 hT root a → Prop
  | .inl e => a.CotreeTransitionCrossesToParent axis hn2 hT parent e
  | .inr (.inl _lane) => True
  | .inr (.inr _escape) => False

def PlanarLensTransportLabel.ValidAt
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (label : PlanarLensTransportLabel axis hn2 hn3 hT root a) : Prop :=
  (∃ parent,
    (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = some parent ∧
      label.ValidForParent axis hn2 hn3 hT a parent) ∨
  ((PlanarInwardLensForest axis hn2 hn3 hT root).parent a = none ∧
    ∃ escape, label = .inr (.inr escape))

theorem canonicalRootEscape_validAt
    {root : GridVertex n n}
    (origin : PlanarLensOriginalDebt axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (hroot : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = none) :
    PlanarLensTransportLabel.ValidAt axis hn2 hn3 hT a
      (Sum.inr (Sum.inr (planarLensCanonicalRootEscape
        axis hn2 hn3 hT origin a))) := by
  exact Or.inr ⟨hroot, _, rfl⟩

/-- Planar placement of a degenerate-corner omitted edge. A nonroot occurrence
must prove the local edge crosses to its typed parent; a root occurrence starts
the canonical provenance-preserving escape. -/
inductive CornerDegenerateTransportPlacement
    {component : ContactRawComponent (T := T)}
    {root : GridVertex n n}
    (origin : PlanarLensOriginalDebt axis hn2 hn3 hT root)
    (region : PlanarInwardLensOccurrence axis hn2 hT root)
    (debt : DuplicatedCornerOverlapDebt axis hn2 hT component) : Type where
  | parent
      (next : PlanarInwardLensOccurrence axis hn2 hT root)
      (parent_eq : (PlanarInwardLensForest axis hn2 hn3 hT root).parent region =
        some next)
      (crosses : region.CotreeTransitionCrossesToParent axis hn2 hT next
        (cornerDegenerateTransition axis hn2 hn3 hT debt).transition)
  | root
      (parent_eq : (PlanarInwardLensForest axis hn2 hn3 hT root).parent region = none)

noncomputable def CornerDegenerateTransportPlacement.label
    {component : ContactRawComponent (T := T)}
    {root : GridVertex n n}
    {origin : PlanarLensOriginalDebt axis hn2 hn3 hT root}
    {region : PlanarInwardLensOccurrence axis hn2 hT root}
    {debt : DuplicatedCornerOverlapDebt axis hn2 hT component} :
    CornerDegenerateTransportPlacement axis hn2 hn3 hT origin region debt →
      PlanarLensTransportLabel axis hn2 hn3 hT root region
  | .parent _ _ _ => .inl
      (cornerDegenerateTransition axis hn2 hn3 hT debt).transition
  | .root _ => .inr (.inr
      (planarLensCanonicalRootEscape axis hn2 hn3 hT origin region))

theorem CornerDegenerateTransportPlacement.label_validAt
    {component : ContactRawComponent (T := T)}
    {root : GridVertex n n}
    {origin : PlanarLensOriginalDebt axis hn2 hn3 hT root}
    {region : PlanarInwardLensOccurrence axis hn2 hT root}
    {debt : DuplicatedCornerOverlapDebt axis hn2 hT component}
    (placement : CornerDegenerateTransportPlacement
      axis hn2 hn3 hT origin region debt) :
    (placement.label axis hn2 hn3 hT).ValidAt axis hn2 hn3 hT region := by
  cases placement with
  | parent next hparent hcross => exact Or.inl ⟨next, hparent, hcross⟩
  | root hroot => exact Or.inr ⟨hroot, _, rfl⟩

/-- Planar placement of any occurrence-labelled component omitted edge. This
is transport data only: neither branch claims a physical payment. -/
inductive ComponentOmittedEdgeTransportPlacement
    {component : ContactRawComponent (T := T)}
    {root : GridVertex n n}
    (origin : PlanarLensOriginalDebt axis hn2 hn3 hT root)
    (region : PlanarInwardLensOccurrence axis hn2 hT root)
    (occurrence : ComponentOmittedEdgeOccurrence axis hn2 hT component) : Type where
  | parent
      (next : PlanarInwardLensOccurrence axis hn2 hT root)
      (parent_eq : (PlanarInwardLensForest axis hn2 hn3 hT root).parent region =
        some next)
      (crosses : region.CotreeTransitionCrossesToParent axis hn2 hT next
        (componentOmittedEdgeTransition axis hn2 hn3 hT occurrence))
  | root
      (parent_eq : (PlanarInwardLensForest axis hn2 hn3 hT root).parent region = none)

/-- If an edge crosses a vertex set but not a containing vertex set, its other
endpoint lies in the difference between the two sets. -/
theorem GridEdge.crossesToSuperset_of_crosses_of_not_crosses
    {A B : Finset (GridVertex n n)} (e : GridEdge n n)
    (hsub : A ⊆ B) (hcross : e.Crosses A) (hnotCross : ¬e.Crosses B) :
    (e.primalEndpoints.1 ∈ A ∧ e.primalEndpoints.2 ∈ B ∧
        e.primalEndpoints.2 ∉ A) ∨
      (e.primalEndpoints.2 ∈ A ∧ e.primalEndpoints.1 ∈ B ∧
        e.primalEndpoints.1 ∉ A) := by
  rcases hcross with hcross | hcross
  · left
    refine ⟨hcross.1, ?_, hcross.2⟩
    by_contra hout
    exact hnotCross (Or.inl ⟨hsub hcross.1, hout⟩)
  · right
    refine ⟨hcross.1, ?_, hcross.2⟩
    by_contra hout
    exact hnotCross (Or.inr ⟨hsub hcross.1, hout⟩)

/-- Occurrences whose rooted shores lie on the inclusion chain above `base`.
The non-strict relation includes `base`, so this finite chain is nonempty. -/
def PlanarInwardLensOccurrence.InSupershoreChain
    {root : GridVertex n n}
    (base region : PlanarInwardLensOccurrence axis hn2 hT root) : Prop :=
  planarInwardLensShoreRegion axis hn2 hT base ⊆
    planarInwardLensShoreRegion axis hn2 hT region

/-- Finite supershore chain above an occurrence. -/
noncomputable def planarInwardLensSupershoreChain
    {root : GridVertex n n}
    (base : PlanarInwardLensOccurrence axis hn2 hT root) :
    Finset (PlanarInwardLensOccurrence axis hn2 hT root) :=
  Finset.univ.filter (base.InSupershoreChain axis hn2 hT)

@[simp] theorem mem_planarInwardLensSupershoreChain
    {root : GridVertex n n}
    (base region : PlanarInwardLensOccurrence axis hn2 hT root) :
    region ∈ planarInwardLensSupershoreChain axis hn2 hT base ↔
      base.InSupershoreChain axis hn2 hT region := by
  simp [planarInwardLensSupershoreChain]

theorem planarInwardLensSupershoreChain_nonempty
    {root : GridVertex n n}
    (base : PlanarInwardLensOccurrence axis hn2 hT root) :
    (planarInwardLensSupershoreChain axis hn2 hT base).Nonempty := by
  exact ⟨base, by simp [PlanarInwardLensOccurrence.InSupershoreChain]⟩

/-- The crossed members of the finite supershore chain for a fixed edge. -/
noncomputable def planarInwardLensCrossedSupershores
    {root : GridVertex n n}
    (base : PlanarInwardLensOccurrence axis hn2 hT root) (e : GridEdge n n) :
    Finset (PlanarInwardLensOccurrence axis hn2 hT root) :=
  (planarInwardLensSupershoreChain axis hn2 hT base).filter fun region =>
    e.Crosses (planarInwardLensShoreRegion axis hn2 hT region)

/-- Canonical outermost crossed supershore, selected by maximal shore size. -/
noncomputable def canonicalOutermostCrossedSupershore
    {root : GridVertex n n}
    (base : PlanarInwardLensOccurrence axis hn2 hT root) (e : GridEdge n n)
    (hcrossed : (planarInwardLensCrossedSupershores
      axis hn2 hT base e).Nonempty) :
    PlanarInwardLensOccurrence axis hn2 hT root :=
  Classical.choose (Finset.exists_max_image
    (planarInwardLensCrossedSupershores axis hn2 hT base e)
    (fun region => (planarInwardLensShoreRegion axis hn2 hT region).card)
    hcrossed)

theorem canonicalOutermostCrossedSupershore_mem
    {root : GridVertex n n}
    (base : PlanarInwardLensOccurrence axis hn2 hT root) (e : GridEdge n n)
    (hcrossed : (planarInwardLensCrossedSupershores
      axis hn2 hT base e).Nonempty) :
    canonicalOutermostCrossedSupershore axis hn2 hT base e hcrossed ∈
      planarInwardLensCrossedSupershores axis hn2 hT base e :=
  (Classical.choose_spec (Finset.exists_max_image
    (planarInwardLensCrossedSupershores axis hn2 hT base e)
    (fun region => (planarInwardLensShoreRegion axis hn2 hT region).card)
    hcrossed)).1

theorem canonicalOutermostCrossedSupershore_card_maximal
    {root : GridVertex n n}
    (base : PlanarInwardLensOccurrence axis hn2 hT root) (e : GridEdge n n)
    (hcrossed : (planarInwardLensCrossedSupershores
      axis hn2 hT base e).Nonempty)
    {region : PlanarInwardLensOccurrence axis hn2 hT root}
    (hregion : region ∈ planarInwardLensCrossedSupershores axis hn2 hT base e) :
    (planarInwardLensShoreRegion axis hn2 hT region).card ≤
      (planarInwardLensShoreRegion axis hn2 hT
        (canonicalOutermostCrossedSupershore axis hn2 hT base e hcrossed)).card :=
  (Classical.choose_spec (Finset.exists_max_image
    (planarInwardLensCrossedSupershores axis hn2 hT base e)
    (fun region => (planarInwardLensShoreRegion axis hn2 hT region).card)
    hcrossed)).2 region hregion

/-- Canonical maximal supershore, used when the edge crosses no shore in the
chain. -/
noncomputable def canonicalMaximalSupershore
    {root : GridVertex n n}
    (base : PlanarInwardLensOccurrence axis hn2 hT root) :
    PlanarInwardLensOccurrence axis hn2 hT root :=
  Classical.choose (Finset.exists_max_image
    (planarInwardLensSupershoreChain axis hn2 hT base)
    (fun region => (planarInwardLensShoreRegion axis hn2 hT region).card)
    (planarInwardLensSupershoreChain_nonempty axis hn2 hT base))

theorem canonicalMaximalSupershore_mem
    {root : GridVertex n n}
    (base : PlanarInwardLensOccurrence axis hn2 hT root) :
    canonicalMaximalSupershore axis hn2 hT base ∈
      planarInwardLensSupershoreChain axis hn2 hT base :=
  (Classical.choose_spec (Finset.exists_max_image
    (planarInwardLensSupershoreChain axis hn2 hT base)
    (fun region => (planarInwardLensShoreRegion axis hn2 hT region).card)
    (planarInwardLensSupershoreChain_nonempty axis hn2 hT base))).1

theorem canonicalMaximalSupershore_card_maximal
    {root : GridVertex n n}
    (base : PlanarInwardLensOccurrence axis hn2 hT root)
    {region : PlanarInwardLensOccurrence axis hn2 hT root}
    (hregion : region ∈ planarInwardLensSupershoreChain axis hn2 hT base) :
    (planarInwardLensShoreRegion axis hn2 hT region).card ≤
      (planarInwardLensShoreRegion axis hn2 hT
        (canonicalMaximalSupershore axis hn2 hT base)).card :=
  (Classical.choose_spec (Finset.exists_max_image
    (planarInwardLensSupershoreChain axis hn2 hT base)
    (fun region => (planarInwardLensShoreRegion axis hn2 hT region).card)
    (planarInwardLensSupershoreChain_nonempty axis hn2 hT base))).2 region hregion

/-- Every occurrence-labelled omitted edge has a canonical relocated placement:
the outermost crossed supershore passes to its immediate parent, while an edge
crossing no supershore is placed at a maximal, hence parentless, supershore. -/
noncomputable def canonicalComponentOmittedEdgeTransportPlacement
    {component : ContactRawComponent (T := T)}
    {root : GridVertex n n}
    (origin : PlanarLensOriginalDebt axis hn2 hn3 hT root)
    (occurrence : ComponentOmittedEdgeOccurrence axis hn2 hT component) :
    Σ region, ComponentOmittedEdgeTransportPlacement axis hn2 hn3 hT
      origin region occurrence := by
  classical
  let base : PlanarInwardLensOccurrence axis hn2 hT root := origin.1
  let edge : GridEdge n n :=
    (componentOmittedEdgeTransition axis hn2 hn3 hT occurrence).1
  by_cases hcrossed : (planarInwardLensCrossedSupershores
      axis hn2 hT base edge).Nonempty
  · let region := canonicalOutermostCrossedSupershore
      axis hn2 hT base edge hcrossed
    cases hparent : (PlanarInwardLensForest axis hn2 hn3 hT root).parent region with
    | none => exact ⟨region, .root hparent⟩
    | some parent =>
        have hstrict : planarInwardLensShoreRegion axis hn2 hT region ⊂
            planarInwardLensShoreRegion axis hn2 hT parent :=
          (planarInwardLensParent_eq_some_iff
            axis hn2 hT hn3 region parent).1 hparent |>.1
        have hregionMem := canonicalOutermostCrossedSupershore_mem
          axis hn2 hT base edge hcrossed
        have hbaseRegion : base.InSupershoreChain axis hn2 hT region := by
          exact (Finset.mem_filter.mp hregionMem).1 |>
            (mem_planarInwardLensSupershoreChain axis hn2 hT base region).1
        have hparentChain : parent ∈
            planarInwardLensSupershoreChain axis hn2 hT base := by
          rw [mem_planarInwardLensSupershoreChain]
          exact Finset.Subset.trans hbaseRegion hstrict.1
        have hnotCrossParent : ¬edge.Crosses
            (planarInwardLensShoreRegion axis hn2 hT parent) := by
          intro hcrossParent
          have hparentMem : parent ∈ planarInwardLensCrossedSupershores
              axis hn2 hT base edge :=
            Finset.mem_filter.mpr ⟨hparentChain, hcrossParent⟩
          have hle := canonicalOutermostCrossedSupershore_card_maximal
            axis hn2 hT base edge hcrossed hparentMem
          exact (not_le_of_gt (Finset.card_lt_card hstrict)) hle
        have hcrossRegion : edge.Crosses
            (planarInwardLensShoreRegion axis hn2 hT region) :=
          (Finset.mem_filter.mp hregionMem).2
        exact ⟨region, .parent parent hparent
          (GridEdge.crossesToSuperset_of_crosses_of_not_crosses edge
            hstrict.1 hcrossRegion hnotCrossParent)⟩
  · let region := canonicalMaximalSupershore axis hn2 hT base
    have hroot : (PlanarInwardLensForest axis hn2 hn3 hT root).parent region = none := by
      cases hparent : (PlanarInwardLensForest axis hn2 hn3 hT root).parent region with
      | none => rfl
      | some parent =>
          have hstrict : planarInwardLensShoreRegion axis hn2 hT region ⊂
              planarInwardLensShoreRegion axis hn2 hT parent :=
            (planarInwardLensParent_eq_some_iff
              axis hn2 hT hn3 region parent).1 hparent |>.1
          have hbaseRegion : base.InSupershoreChain axis hn2 hT region :=
            (mem_planarInwardLensSupershoreChain axis hn2 hT base region).1
              (canonicalMaximalSupershore_mem axis hn2 hT base)
          have hparentMem : parent ∈
              planarInwardLensSupershoreChain axis hn2 hT base := by
            rw [mem_planarInwardLensSupershoreChain]
            exact Finset.Subset.trans hbaseRegion hstrict.1
          have hle := canonicalMaximalSupershore_card_maximal
            axis hn2 hT base hparentMem
          exact False.elim ((not_le_of_gt (Finset.card_lt_card hstrict)) hle)
    exact ⟨region, .root hroot⟩

noncomputable def ComponentOmittedEdgeTransportPlacement.label
    {component : ContactRawComponent (T := T)}
    {root : GridVertex n n}
    {origin : PlanarLensOriginalDebt axis hn2 hn3 hT root}
    {region : PlanarInwardLensOccurrence axis hn2 hT root}
    {occurrence : ComponentOmittedEdgeOccurrence axis hn2 hT component} :
    ComponentOmittedEdgeTransportPlacement axis hn2 hn3 hT
        origin region occurrence →
      PlanarLensTransportLabel axis hn2 hn3 hT root region
  | .parent _ _ _ => .inl
      (componentOmittedEdgeTransition axis hn2 hn3 hT occurrence)
  | .root _ => .inr (.inr
      (planarLensCanonicalRootEscape axis hn2 hn3 hT origin region))

theorem ComponentOmittedEdgeTransportPlacement.label_validAt
    {component : ContactRawComponent (T := T)}
    {root : GridVertex n n}
    {origin : PlanarLensOriginalDebt axis hn2 hn3 hT root}
    {region : PlanarInwardLensOccurrence axis hn2 hT root}
    {occurrence : ComponentOmittedEdgeOccurrence axis hn2 hT component}
    (placement : ComponentOmittedEdgeTransportPlacement axis hn2 hn3 hT
      origin region occurrence) :
    (placement.label axis hn2 hn3 hT).ValidAt axis hn2 hn3 hT region := by
  cases placement with
  | parent next hparent hcross => exact Or.inl ⟨next, hparent, hcross⟩
  | root hroot => exact Or.inr ⟨hroot, _, rfl⟩

/-- Generic selected outgoing fiber used inside the routing conservation law. -/
abbrev PlanarLensRoutingOutgoingFiber
    {root : GridVertex n n}
    (active : PlanarInwardLensOccurrence axis hn2 hT root →
      Finset (PlanarLensOriginalDebt axis hn2 hn3 hT root))
    (transition : ∀ a, ↥(active a) →
      Option (PlanarLensTransportLabel axis hn2 hn3 hT root a))
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  {q : ↥(active a) // ∃ label parent,
    transition a q = some label ∧
      (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = some parent ∧
        label.ValidForParent axis hn2 hn3 hT a parent}

/-- One active state and at most one labelled transition for each original debt
occurrence at a region.  `flow` is exact conservation: active debts are either
born locally or are the selected outgoing debts of one immediate child.
`flow_origin` prevents the equivalence from changing the original debt label. -/
structure PlanarLensDebtRouting (root : GridVertex n n) where
  active : PlanarInwardLensOccurrence axis hn2 hT root →
    Finset (PlanarLensOriginalDebt axis hn2 hn3 hT root)
  transition : ∀ a, ↥(active a) →
    Option (PlanarLensTransportLabel axis hn2 hn3 hT root a)
  transition_valid : ∀ a q label, transition a q = some label →
    label.ValidAt axis hn2 hn3 hT a
  transition_origin : ∀ a q label, transition a q = some label →
    match label with
    | .inr (.inr escape) => escape.1.origin = q.1
    | _ => True
  flow : ∀ a, ↥(active a) ≃
    (PlanarLensLocalDebt axis hn2 hn3 hT root a ⊕
      Σ c : ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a),
        PlanarLensRoutingOutgoingFiber axis hn2 hn3 hT active transition c.1)
  flow_origin : ∀ a q,
    match flow a q with
    | .inl localDebt => localDebt.1 = q.1
    | .inr incoming => incoming.2.1.1 = q.1

/-- Original debts whose birth occurrence lies below `a` in the planar parent
forest. -/
noncomputable def planarLensCanonicalActive
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    Finset (PlanarLensOriginalDebt axis hn2 hn3 hT root) :=
  Finset.univ.filter fun q =>
    Relation.ReflTransGen
      (PlanarInwardLensForest axis hn2 hn3 hT root).ParentStep q.1 a

@[simp] theorem mem_planarLensCanonicalActive
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (q : PlanarLensOriginalDebt axis hn2 hn3 hT root) :
    q ∈ planarLensCanonicalActive axis hn2 hn3 hT root a ↔
      Relation.ReflTransGen
        (PlanarInwardLensForest axis hn2 hn3 hT root).ParentStep q.1 a := by
  simp [planarLensCanonicalActive]

/-- The canonical occurrence-preserving move. Roots enter the contour escape;
at a nonroot, local births use their designated gap and older debts use the
last child on their parent chain. -/
noncomputable def planarLensCanonicalTransition
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (q : ↥(planarLensCanonicalActive axis hn2 hn3 hT root a)) :
    Option (PlanarLensTransportLabel axis hn2 hn3 hT root a) := by
  let F := PlanarInwardLensForest axis hn2 hn3 hT root
  if hroot : F.parent a = none then
    exact some (.inr (.inr
      (planarLensCanonicalRootEscape axis hn2 hn3 hT q.1 a)))
  else
    have hreach : Relation.ReflTransGen F.ParentStep q.1.1 a :=
      (mem_planarLensCanonicalActive axis hn2 hn3 hT root a q.1).1 q.2
    if hbirth : a = q.1.1 then
      exact some (planarLensLocalDebtInterfaceLabelEmbedding
        axis hn2 hn3 hT root a ⟨q.1, hbirth.symm⟩)
    else
      have hexists : ∃ child, Relation.ReflTransGen F.ParentStep q.1.1 child ∧
          F.ParentStep child a := hreach.cases_tail.resolve_left hbirth
      let child := Classical.choose hexists
      exact some (.inr (.inl ⟨child, (Classical.choose_spec hexists).2⟩))

theorem planarLensCanonicalTransition_of_parent
    {root : GridVertex n n}
    {a parent : PlanarInwardLensOccurrence axis hn2 hT root}
    (hparent : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = some parent)
    (q : ↥(planarLensCanonicalActive axis hn2 hn3 hT root a)) :
    ∃ label, planarLensCanonicalTransition axis hn2 hn3 hT root a q = some label ∧
      label.ValidForParent axis hn2 hn3 hT a parent := by
  classical
  simp only [planarLensCanonicalTransition, hparent, Option.some_ne_none,
    ↓reduceDIte]
  split <;> exact ⟨_, rfl, trivial⟩

noncomputable def planarLensCanonicalOutgoing
    {root : GridVertex n n}
    {a child : PlanarInwardLensOccurrence axis hn2 hT root}
    (hchild : (PlanarInwardLensForest axis hn2 hn3 hT root).parent child = some a)
    (q : ↥(planarLensCanonicalActive axis hn2 hn3 hT root child)) :
    PlanarLensRoutingOutgoingFiber axis hn2 hn3 hT
      (planarLensCanonicalActive axis hn2 hn3 hT root)
      (planarLensCanonicalTransition axis hn2 hn3 hT root) child := by
  let hexists := planarLensCanonicalTransition_of_parent
    axis hn2 hn3 hT hchild q
  exact ⟨q, Classical.choose hexists, a, (Classical.choose_spec hexists).1,
    hchild, (Classical.choose_spec hexists).2⟩

theorem parentForest_rank_le_of_reflTransGen_parentStep
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ParentForest V) {a b : V}
    (h : Relation.ReflTransGen F.ParentStep a b) : F.rank b ≤ F.rank a := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail h hparent ih => exact (Nat.le_of_lt (F.rank_parent hparent)).trans ih

theorem parentForest_finalChild_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ParentForest V) {q c d a : V}
    (hqc : Relation.ReflTransGen F.ParentStep q c) (hca : F.ParentStep c a)
    (hqd : Relation.ReflTransGen F.ParentStep q d) (hda : F.ParentStep d a) : c = d := by
  have hright : Relator.RightUnique F.ParentStep := by
    intro x y z hxy hxz
    exact Option.some.inj (hxy.symm.trans hxz)
  rcases Relation.ReflTransGen.total_of_right_unique hright hqc hqd with hcd | hdc
  · rcases hcd.cases_head with h | ⟨e, hce, hed⟩
    · exact h
    · have hea : e = a := hright hce hca
      subst e
      have hle := parentForest_rank_le_of_reflTransGen_parentStep F hed
      exact False.elim ((not_le_of_gt (F.rank_parent hda)) hle)
  · rcases hdc.cases_head with h | ⟨e, hde, hec⟩
    · exact h.symm
    · have hea : e = a := hright hde hda
      subst e
      have hle := parentForest_rank_le_of_reflTransGen_parentStep F hec
      exact False.elim ((not_le_of_gt (F.rank_parent hca)) hle)

/-- Exact decomposition of active origins into births at `a` and origins
arriving from one immediate child. -/
noncomputable def planarLensCanonicalFlow
    (root : GridVertex n n)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    ↥(planarLensCanonicalActive axis hn2 hn3 hT root a) ≃
      (PlanarLensLocalDebt axis hn2 hn3 hT root a ⊕
        Σ c : ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a),
          PlanarLensRoutingOutgoingFiber axis hn2 hn3 hT
            (planarLensCanonicalActive axis hn2 hn3 hT root)
            (planarLensCanonicalTransition axis hn2 hn3 hT root) c.1) where
  toFun q := by
    have hreach :=
      (mem_planarLensCanonicalActive axis hn2 hn3 hT root a q.1).1 q.2
    if hbirth : a = q.1.1 then
      exact .inl ⟨q.1, hbirth.symm⟩
    else
      have hexists : ∃ child,
          Relation.ReflTransGen
              (PlanarInwardLensForest axis hn2 hn3 hT root).ParentStep q.1.1 child ∧
            (PlanarInwardLensForest axis hn2 hn3 hT root).ParentStep child a :=
        hreach.cases_tail.resolve_left hbirth
      let child := Classical.choose hexists
      have hchild := (Classical.choose_spec hexists).2
      have hmem : child ∈
          (PlanarInwardLensForest axis hn2 hn3 hT root).children a := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hchild⟩
      let childDebt : ↥(planarLensCanonicalActive axis hn2 hn3 hT root child) :=
        ⟨q.1, (mem_planarLensCanonicalActive
          axis hn2 hn3 hT root child q.1).2 (Classical.choose_spec hexists).1⟩
      exact .inr ⟨⟨child, hmem⟩,
        planarLensCanonicalOutgoing axis hn2 hn3 hT hchild childDebt⟩
  invFun debt := by
    rcases debt with birth | incoming
    · exact ⟨birth.1, (mem_planarLensCanonicalActive
        axis hn2 hn3 hT root a birth.1).2 (by
          simpa [birth.2] using Relation.ReflTransGen.refl)⟩
    · exact ⟨incoming.2.1.1, (mem_planarLensCanonicalActive
        axis hn2 hn3 hT root a incoming.2.1.1).2
          ((mem_planarLensCanonicalActive axis hn2 hn3 hT root
            incoming.1.1 incoming.2.1.1).1 incoming.2.1.2 |>.tail
              (Finset.mem_filter.mp incoming.1.2).2)⟩
  left_inv q := by
    apply Subtype.ext
    by_cases hbirth : a = q.1.1
    · simp [hbirth]
    · simp only [hbirth, ↓reduceDIte]
      rfl
  right_inv debt := by
    rcases debt with birth | incoming
    · simp [birth.2]
    · have hreachChild := (mem_planarLensCanonicalActive axis hn2 hn3 hT root
          incoming.1.1 incoming.2.1.1).1 incoming.2.1.2
      have hchildParent := (Finset.mem_filter.mp incoming.1.2).2
      have hbirth : a ≠ incoming.2.1.1.1 := by
        intro h
        rw [← h] at hreachChild
        have hle := parentForest_rank_le_of_reflTransGen_parentStep
          (PlanarInwardLensForest axis hn2 hn3 hT root) hreachChild
        exact (not_le_of_gt
          ((PlanarInwardLensForest axis hn2 hn3 hT root).rank_parent hchildParent)) hle
      simp only [hbirth, ↓reduceDIte]
      let hexists : ∃ child,
          Relation.ReflTransGen
              (PlanarInwardLensForest axis hn2 hn3 hT root).ParentStep
                incoming.2.1.1.1 child ∧
            (PlanarInwardLensForest axis hn2 hn3 hT root).ParentStep child a :=
        (hreachChild.tail hchildParent).cases_tail.resolve_left hbirth
      have hchosen : Classical.choose hexists = incoming.1.1 :=
        parentForest_finalChild_unique
          (PlanarInwardLensForest axis hn2 hn3 hT root)
          (Classical.choose_spec hexists).1 (Classical.choose_spec hexists).2
          hreachChild hchildParent
      have hchosen' : (⟨Classical.choose hexists, by
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, (Classical.choose_spec hexists).2⟩⟩ :
          ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a)) = incoming.1 :=
        Subtype.ext hchosen
      apply congrArg Sum.inr
      apply Sigma.ext hchosen'
      change planarLensCanonicalOutgoing axis hn2 hn3 hT
          (Classical.choose_spec hexists).2
          ⟨incoming.2.1.1, _⟩ ≍ incoming.2
      apply (Subtype.heq_iff_coe_heq
        (congrArg (fun c :
          ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a) =>
            ↥(planarLensCanonicalActive axis hn2 hn3 hT root c.1)) hchosen')
        (congr_arg_heq (fun c :
          ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a) =>
            fun q : ↥(planarLensCanonicalActive axis hn2 hn3 hT root c.1) =>
              ∃ label parent,
                planarLensCanonicalTransition axis hn2 hn3 hT root c.1 q = some label ∧
                (PlanarInwardLensForest axis hn2 hn3 hT root).parent c.1 = some parent ∧
                label.ValidForParent axis hn2 hn3 hT c.1 parent) hchosen')).2
      apply (Subtype.heq_iff_coe_eq (by
        intro origin
        change origin ∈ planarLensCanonicalActive axis hn2 hn3 hT root
            (Classical.choose hexists) ↔
          origin ∈ planarLensCanonicalActive axis hn2 hn3 hT root incoming.1.1
        rw [hchosen])).2
      rfl

/-- Canonical routing of every original merger-slot occurrence along its unique
parent chain. -/
noncomputable def canonicalPlanarLensDebtRouting
    (root : GridVertex n n) :
    PlanarLensDebtRouting axis hn2 hn3 hT root where
  active := planarLensCanonicalActive axis hn2 hn3 hT root
  transition := planarLensCanonicalTransition axis hn2 hn3 hT root
  transition_valid := by
    intro a q label hlabel
    classical
    simp only [planarLensCanonicalTransition] at hlabel
    split at hlabel
    · rename_i hroot
      simp only [Option.some.injEq] at hlabel
      subst label
      exact canonicalRootEscape_validAt axis hn2 hn3 hT q.1 a hroot
    · rename_i hnonroot
      obtain ⟨parent, hparent⟩ := Option.ne_none_iff_exists'.mp hnonroot
      split at hlabel
      · rename_i hbirth
        simp only [Option.some.injEq] at hlabel
        subst label
        exact Or.inl ⟨parent, hparent, trivial⟩
      · rename_i hbirth
        simp only [Option.some.injEq] at hlabel
        subst label
        exact Or.inl ⟨parent, hparent, trivial⟩
  transition_origin := by
    intro a q label hlabel
    classical
    simp only [planarLensCanonicalTransition] at hlabel
    split at hlabel
    · simp only [Option.some.injEq] at hlabel
      subst label
      rfl
    · split at hlabel <;> simp only [Option.some.injEq] at hlabel <;>
        subst label <;> trivial
  flow := planarLensCanonicalFlow axis hn2 hn3 hT root
  flow_origin := by
    intro a q
    classical
    cases hflow : planarLensCanonicalFlow axis hn2 hn3 hT root a q with
    | inl birth =>
        have h := congrArg
          (fun x => ((planarLensCanonicalFlow axis hn2 hn3 hT root a).symm x).1)
          hflow
        simp only [Equiv.symm_apply_apply] at h
        exact h.symm
    | inr incoming =>
        have h := congrArg
          (fun x => ((planarLensCanonicalFlow axis hn2 hn3 hT root a).symm x).1)
          hflow
        simp only [Equiv.symm_apply_apply] at h
        exact h.symm

namespace PlanarLensDebtRouting

abbrev ActiveDebtFiber
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  ↥(routing.active a)

abbrev SelectedOutgoingPass
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  PlanarLensRoutingOutgoingFiber axis hn2 hn3 hT
    routing.active routing.transition a

abbrev SelectedRootEscape
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  {q : routing.ActiveDebtFiber axis hn2 hn3 hT a //
    ∃ escape, routing.transition a q = some (.inr (.inr escape))}

theorem selectedRootEscape_parentless
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    {a : PlanarInwardLensOccurrence axis hn2 hT root}
    (q : routing.SelectedRootEscape axis hn2 hn3 hT a) :
    (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = none := by
  obtain ⟨escape, hescape⟩ := q.2
  rcases routing.transition_valid a q.1 (.inr (.inr escape)) hescape with
    hparent | hroot
  · obtain ⟨_parent, _hp, hvalid⟩ := hparent
    exact hvalid.elim
  · exact hroot.1

/-- Root escape reaches a finite occurrence-labelled geometric event while
preserving the original active debt.  No event is declared fresh or paid. -/
theorem interfaceLane_eventTermination
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    {a : PlanarInwardLensOccurrence axis hn2 hT root}
    (q : routing.SelectedRootEscape axis hn2 hn3 hT a) :
    ∃ terminal event,
      Relation.ReflTransGen
          (planarLensRootEscapeSystem axis hn2 hn3 hT root).Step
          (Classical.choose q.2).1 terminal ∧
        (planarLensRootEscapeSystem axis hn2 hn3 hT root).terminal terminal =
          some event ∧ terminal.origin = q.1.1 := by
  let escape := Classical.choose q.2
  have htransition := Classical.choose_spec q.2
  obtain ⟨terminal, event, hsteps, hevent, horigin⟩ :=
    planarLensRootEscape_exists_event axis hn2 hn3 hT escape.1
  have hsource : escape.1.origin = q.1.1 :=
    routing.transition_origin a q.1 (.inr (.inr escape)) htransition
  exact ⟨terminal, event, hsteps, hevent, horigin.trans hsource⟩

theorem selectedOutgoing_parent_typed
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    {a : PlanarInwardLensOccurrence axis hn2 hT root}
    (q : routing.SelectedOutgoingPass axis hn2 hn3 hT a) :
    ∃ label parent, routing.transition a q.1 = some label ∧
      (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = some parent ∧
        label.ValidForParent axis hn2 hn3 hT a parent := by
  exact q.2

theorem selectedOutgoing_shellStep
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    {a : PlanarInwardLensOccurrence axis hn2 hT root}
    (q : routing.SelectedOutgoingPass axis hn2 hn3 hT a) :
    ∃ parent,
      (planarShellRankedTransitionSystem axis hn2 hn3 hT root).Step
        (q.1.1.1, a) (q.1.1.1, parent) := by
  obtain ⟨_e, parent, _he, hp, _hcross⟩ :=
    routing.selectedOutgoing_parent_typed axis hn2 hn3 hT q
  exact ⟨parent, by simp [RankedTransitionSystem.Step,
    planarShellRankedTransitionSystem, hp]⟩

/-- Regional capacity now counts original active debts once, not all
origin/edge products. -/
def RegionInequality
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) : Prop :=
  Fintype.card (routing.ActiveDebtFiber axis hn2 hn3 hT a) ≤
    Fintype.card (PlanarLensRegionalOwned axis hn2 hT root a) +
      Fintype.card (routing.SelectedOutgoingPass axis hn2 hn3 hT a)

abbrev RegionalAssignment
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  routing.ActiveDebtFiber axis hn2 hn3 hT a ↪
    (PlanarLensRegionalOwned axis hn2 hT root a ⊕
      routing.SelectedOutgoingPass axis hn2 hn3 hT a)

theorem regionInequality_of_assignment
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (assignment : routing.RegionalAssignment axis hn2 hn3 hT a) :
    routing.RegionInequality axis hn2 hn3 hT a := by
  simpa [RegionInequality, Fintype.card_sum] using
    Fintype.card_le_of_injective assignment assignment.injective

def CarriesCanonicalLocalInterfacesAt
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) : Prop :=
  ∀ localDebt,
    routing.transition a ((routing.flow a).symm (.inl localDebt)) =
      some (planarLensLocalDebtInterfaceLabelEmbedding
        axis hn2 hn3 hT root a localDebt)

def PassesIncomingAt
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) : Prop :=
  ∀ q incoming, routing.flow a q = .inr incoming →
    routing.transition a q ≠ none

theorem allActiveMoves_of_localInterfaces_of_passesIncoming
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (hlocal : routing.CarriesCanonicalLocalInterfacesAt axis hn2 hn3 hT a)
    (hincoming : routing.PassesIncomingAt axis hn2 hn3 hT a) :
    ∀ q : routing.ActiveDebtFiber axis hn2 hn3 hT a,
      routing.transition a q ≠ none := by
  intro q
  cases hflow : routing.flow a q with
  | inl localDebt =>
      have hq : q = (routing.flow a).symm (.inl localDebt) := by
        apply (routing.flow a).injective
        simp [hflow]
      rw [hq, hlocal localDebt]
      simp
  | inr incoming => exact hincoming q incoming hflow

noncomputable def regionalAssignmentOfAllActiveMoves
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (hnonroot : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a ≠ none)
    (hmoves : ∀ q : routing.ActiveDebtFiber axis hn2 hn3 hT a,
      routing.transition a q ≠ none) :
    routing.RegionalAssignment axis hn2 hn3 hT a where
  toFun q := .inr ⟨q, by
    obtain ⟨label, hlabel⟩ := Option.ne_none_iff_exists'.mp (hmoves q)
    rcases routing.transition_valid a q label hlabel with hparent | hescape
    · obtain ⟨parent, hp, hvalid⟩ := hparent
      exact ⟨label, parent, hlabel, hp, hvalid⟩
    · exact (hnonroot hescape.1).elim⟩
  inj' := by
    intro q r hqr
    exact Subtype.ext (congrArg (fun x => x.elim (fun _ => q.1) fun p => p.1.1) hqr)

theorem genuine_regionInequality_of_transport
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarLensGenuineReconvergenceRegion axis hn2 hn3 hT root)
    (hnonroot : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a.1 ≠ none)
    (hlocal : routing.CarriesCanonicalLocalInterfacesAt axis hn2 hn3 hT a.1)
    (hincoming : routing.PassesIncomingAt axis hn2 hn3 hT a.1) :
    routing.RegionInequality axis hn2 hn3 hT a.1 := by
  apply routing.regionInequality_of_assignment axis hn2 hn3 hT a.1
  exact routing.regionalAssignmentOfAllActiveMoves axis hn2 hn3 hT a.1 hnonroot
    (routing.allActiveMoves_of_localInterfaces_of_passesIncoming
      axis hn2 hn3 hT a.1 hlocal hincoming)

theorem card_active_eq_local_add_incoming
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :
    Fintype.card (routing.ActiveDebtFiber axis hn2 hn3 hT a) =
      Fintype.card (PlanarLensLocalDebt axis hn2 hn3 hT root a) +
        ∑ c : ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a),
          Fintype.card (routing.SelectedOutgoingPass axis hn2 hn3 hT c.1) := by
  rw [Fintype.card_congr (routing.flow a), Fintype.card_sum,
    Fintype.card_sigma]

theorem selectedOutgoing_isEmpty_of_root
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (ha : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = none) :
    IsEmpty (routing.SelectedOutgoingPass axis hn2 hn3 hT a) :=
  ⟨fun q => by
    obtain ⟨_e, parent, _he, hp, _hcross⟩ :=
      routing.selectedOutgoing_parent_typed axis hn2 hn3 hT q
    rw [ha] at hp
    cases hp⟩

abbrev RootTerminationAssignment
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root) :=
  routing.ActiveDebtFiber axis hn2 hn3 hT a ↪
    PlanarLensRegionalOwned axis hn2 hT root a

theorem root_regionInequality_of_termination
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (hroot : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = none)
    (terminal : routing.RootTerminationAssignment axis hn2 hn3 hT a) :
    routing.RegionInequality axis hn2 hn3 hT a := by
  let := routing.selectedOutgoing_isEmpty_of_root axis hn2 hn3 hT a hroot
  have hout : Fintype.card
      (routing.SelectedOutgoingPass axis hn2 hn3 hT a) = 0 := Fintype.card_eq_zero
  rw [RegionInequality, hout, add_zero]
  exact Fintype.card_le_of_injective terminal terminal.injective

theorem exists_ranked_terminal_same_origin
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    {a : PlanarInwardLensOccurrence axis hn2 hT root}
    (q : routing.ActiveDebtFiber axis hn2 hn3 hT a) :
    ∃ y terminal,
      Relation.ReflTransGen
          (planarShellRankedTransitionSystem axis hn2 hn3 hT root).Step
          (q.1.1, a) y ∧
        (planarShellRankedTransitionSystem axis hn2 hn3 hT root).terminal y =
          some terminal ∧ y.1 = q.1.1 :=
  exists_planarShellRanked_terminal axis hn2 hn3 hT root q.1.1 a

theorem card_active_eq_incoming_of_unary
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : PlanarLensUnaryPropagationRegion axis hn2 hn3 hT root) :
    Fintype.card (routing.ActiveDebtFiber axis hn2 hn3 hT a.1) =
      ∑ c : ↥((PlanarInwardLensForest axis hn2 hn3 hT root).children a.1),
        Fintype.card (routing.SelectedOutgoingPass axis hn2 hn3 hT c.1) := by
  rw [routing.card_active_eq_local_add_incoming axis hn2 hn3 hT a.1]
  let := planarLensLocalDebt_isEmpty_of_unary axis hn2 hn3 hT a
  rw [Fintype.card_eq_zero, zero_add]

theorem canonicalPlanarLensDebtRouting_carriesCanonicalLocalInterfacesAt
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (hnonroot : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a ≠ none) :
    CarriesCanonicalLocalInterfacesAt axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root) a := by
  intro birth
  change planarLensCanonicalTransition axis hn2 hn3 hT root a
      ((planarLensCanonicalFlow axis hn2 hn3 hT root a).symm (.inl birth)) =
    some (planarLensLocalDebtInterfaceLabelEmbedding
      axis hn2 hn3 hT root a birth)
  simp [planarLensCanonicalFlow, planarLensCanonicalTransition, hnonroot, birth.2]

theorem canonicalPlanarLensDebtRouting_passesIncomingAt
    {root : GridVertex n n}
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (hnonroot : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a ≠ none) :
    PassesIncomingAt axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root) a := by
  intro q incoming _hflow
  obtain ⟨parent, hparent⟩ := Option.ne_none_iff_exists'.mp hnonroot
  obtain ⟨label, hlabel, _hvalid⟩ :=
    planarLensCanonicalTransition_of_parent axis hn2 hn3 hT hparent q
  change planarLensCanonicalTransition axis hn2 hn3 hT root a q ≠ none
  rw [hlabel]
  simp

end PlanarLensDebtRouting

/-- Main U3 local statement for the corrected active-debt model. -/
def CanonicalUpperU3ActiveLocalInequality
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root) : Prop :=
  ∀ a, routing.RegionInequality axis hn2 hn3 hT a

theorem canonicalUpperU3_activeLocalInequality_globalCard
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (hlocal : CanonicalUpperU3ActiveLocalInequality axis hn2 hn3 hT routing) :
    Fintype.card (PlanarLensOriginalDebt axis hn2 hn3 hT root) ≤
      Fintype.card (PlanarLensFirstOwnedResource axis hn2 hT root) := by
  let F := PlanarInwardLensForest axis hn2 hn3 hT root
  let debt := fun a => Fintype.card (PlanarLensLocalDebt axis hn2 hn3 hT root a)
  let owned := fun a => Fintype.card (PlanarLensRegionalOwned axis hn2 hT root a)
  let passed := fun a =>
    Fintype.card (routing.SelectedOutgoingPass axis hn2 hn3 hT a)
  have hroot : ∀ a, F.parent a = none → passed a = 0 := by
    intro a ha
    let := routing.selectedOutgoing_isEmpty_of_root axis hn2 hn3 hT a ha
    exact Fintype.card_eq_zero
  have hlocal' : ∀ a,
      debt a + ∑ c ∈ F.children a, passed c ≤ owned a + passed a := by
    intro a
    have ha := hlocal a
    rw [PlanarLensDebtRouting.RegionInequality,
      routing.card_active_eq_local_add_incoming axis hn2 hn3 hT a] at ha
    change debt a + (∑ c : ↥(F.children a), passed c.1) ≤
      owned a + passed a at ha
    rw [sum_finset_subtype_eq_sum_filter] at ha
    exact ha
  have hglobal : ∑ a, debt a ≤ ∑ a, owned a :=
    parentForest_global_le_of_regional_telescope F debt owned passed hroot hlocal'
  calc
    Fintype.card (PlanarLensOriginalDebt axis hn2 hn3 hT root) =
        ∑ a, debt a := by
      rw [Fintype.card_congr
        (planarLensLocalDebtDecomposition axis hn2 hn3 hT root),
        Fintype.card_sigma]
    _ ≤ ∑ a, owned a := hglobal
    _ = Fintype.card (PlanarLensFirstOwnedResource axis hn2 hT root) := by
      exact (card_planarLensRegionalOwnedDecomposition axis hn2 hT root).symm

def canonicalUpperU3ActiveNeighborhood
    {root : GridVertex n n}
    (_ : PlanarLensOriginalDebt axis hn2 hn3 hT root) :
    Finset (PlanarLensFirstOwnedResource axis hn2 hT root) := Finset.univ

theorem canonicalUpperU3_activeLocalInequality_globalHall
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (hlocal : CanonicalUpperU3ActiveLocalInequality axis hn2 hn3 hT routing) :
    LocalizedHall (canonicalUpperU3ActiveNeighborhood
      (root := root) axis hn2 hn3 hT) := by
  have hcard := canonicalUpperU3_activeLocalInequality_globalCard
    axis hn2 hn3 hT routing hlocal
  intro S
  by_cases hS : S = ∅
  · simp [hS]
  · have hbi : S.biUnion (canonicalUpperU3ActiveNeighborhood axis hn2 hn3 hT) =
        (Finset.univ : Finset (PlanarLensFirstOwnedResource axis hn2 hT root)) := by
      ext r
      simp only [Finset.mem_biUnion, canonicalUpperU3ActiveNeighborhood,
        Finset.mem_univ, iff_true]
      obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      exact ⟨q, hq, trivial⟩
    rw [hbi]
    calc
      S.card ≤ Fintype.card (PlanarLensOriginalDebt axis hn2 hn3 hT root) := by
        simpa [← Finset.card_univ] using Finset.card_le_card (Finset.subset_univ S)
      _ ≤ Fintype.card (PlanarLensFirstOwnedResource axis hn2 hT root) := hcard
      _ = (Finset.univ : Finset
          (PlanarLensFirstOwnedResource axis hn2 hT root)).card :=
        (Finset.card_univ).symm

/-- Exact remaining constructive U3 object.  It contains no local cardinality,
Hall, waste, or resource-capacity assumption. -/
structure CanonicalUpperU3ActiveDebtCertificate (root : GridVertex n n) where
  routing : PlanarLensDebtRouting axis hn2 hn3 hT root
  regionalAssignment : ∀ a,
    routing.RegionalAssignment axis hn2 hn3 hT a

/-- Geometric fill required by the research reduction.  Nonroot active debts
continue through cotree or interface-gap labels.  Only roots must inject their
remaining active debts into first-owned physical resources. -/
structure CanonicalUpperU3TransportCertificate (root : GridVertex n n) where
  routing : PlanarLensDebtRouting axis hn2 hn3 hT root
  localInterfaces : ∀ a,
    (PlanarInwardLensForest axis hn2 hn3 hT root).parent a ≠ none →
      routing.CarriesCanonicalLocalInterfacesAt axis hn2 hn3 hT a
  passIncoming : ∀ a,
    (PlanarInwardLensForest axis hn2 hn3 hT root).parent a ≠ none →
      routing.PassesIncomingAt axis hn2 hn3 hT a
  rootTermination : ∀ a,
    (hroot : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = none) →
      routing.RootTerminationAssignment axis hn2 hn3 hT a

/-- Event-termination variant.  Root debts may either already have an owned
resource or enter a provenance-preserving expanded-contour escape.  This
package intentionally has no Hall or payment theorem. -/
structure CanonicalUpperU3InterfaceLaneEventTermination
    (root : GridVertex n n) where
  routing : PlanarLensDebtRouting axis hn2 hn3 hT root
  localInterfaces : ∀ a,
    (PlanarInwardLensForest axis hn2 hn3 hT root).parent a ≠ none →
      routing.CarriesCanonicalLocalInterfacesAt axis hn2 hn3 hT a
  passIncoming : ∀ a,
    (PlanarInwardLensForest axis hn2 hn3 hT root).parent a ≠ none →
      routing.PassesIncomingAt axis hn2 hn3 hT a
  rootOutcome : ∀ a,
    (hroot : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = none) →
      routing.ActiveDebtFiber axis hn2 hn3 hT a ↪
        (PlanarLensRegionalOwned axis hn2 hT root a ⊕
          routing.SelectedRootEscape axis hn2 hn3 hT a)

theorem CanonicalUpperU3InterfaceLaneEventTermination.rootEscapeTerminates
    {root : GridVertex n n}
    (certificate : CanonicalUpperU3InterfaceLaneEventTermination
      axis hn2 hn3 hT root)
    {a : PlanarInwardLensOccurrence axis hn2 hT root}
    (escape : certificate.routing.SelectedRootEscape axis hn2 hn3 hT a) :
    ∃ terminal event,
      Relation.ReflTransGen
          (planarLensRootEscapeSystem axis hn2 hn3 hT root).Step
          (Classical.choose escape.2).1 terminal ∧
        (planarLensRootEscapeSystem axis hn2 hn3 hT root).terminal terminal =
          some event ∧ terminal.origin = escape.1.1 :=
  certificate.routing.interfaceLane_eventTermination axis hn2 hn3 hT escape

/-! ### C5: root Hall over raw physical resources -/

/-- Physical U2 resources with free-component contacts collapsed to their raw
component.  Contacts are never counted as separate resources here. -/
abbrev PlanarLensRawPhysicalResource :=
  SupportedSplitOuterPortResource (T := T) ⊕
    (RetainedInternalSupportEdgeResource (T := T) ⊕
      FreeFullVertexComponentResource (T := T))

noncomputable instance planarLensRawPhysicalResourceDecidableEq :
    DecidableEq (PlanarLensRawPhysicalResource (T := T)) := Classical.decEq _

def planarLensFirstOwnedResourceRaw
    {root : GridVertex n n} :
    PlanarLensFirstOwnedResource axis hn2 hT root →
      PlanarLensRawPhysicalResource (T := T)
  | .inl port => .inl port.resource
  | .inr (.inl edge) => .inr (.inl edge.resource)
  | .inr (.inr contact) => .inr (.inr contact.resource.component)

/-! ### C5: full pruned-source regional routing -/

/-- Regional interpretation of the boundary-cell construction.  The selected
cell-edge alternatives are already globally injective.  This certificate asks
only for their geometric placement relative to canonical reservations and the
planar parent forest. -/
structure RankedCarrierBoundaryCellRegionalCertificate
    (root : GridVertex n n) where
  cells : RankedCarrierBoundaryCellRoutingData axis hn2 hT
  region : RankedContactEnrichedCarrierCollision axis hn2 hT →
    PlanarInwardLensOccurrence axis hn2 hT root
  internal_unreserved : ∀ collision edge,
    cells.alternative axis hn2 hT collision = .inl edge →
    edge ∉ Set.range (internalTreeEdgeTokenEmbedding
      (supportFinset (gridGraph n n \ T))
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT))
  internal_first_owned : ∀ collision edge,
    cells.alternative axis hn2 hT collision = .inl edge →
    ∃ owned : PlanarLensRegionalOwned axis hn2 hT root (region collision),
      planarLensFirstOwnedResourceRaw axis hn2 hT owned.1 = .inr (.inl edge)
  cotree_selected_pass : ∀ collision edge,
    cells.alternative axis hn2 hT collision = .inr edge →
    ∃ parent,
      (PlanarInwardLensForest axis hn2 hn3 hT root).parent (region collision) =
        some parent ∧
      (region collision).CotreeTransitionCrossesToParent axis hn2 hT parent edge

/-! ### The sole duplicated-corner overlap -/

abbrev RegionalDuplicatedCornerDebt
    {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (component : ContactRawComponent (T := T)) :=
  {gap : ComponentSpatialGap axis hn2 hT component //
    (componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1 =
      gap.1.1.contact.1}

/-- The physical route available after following the duplicated corner's second
attachment orientation to its first supported planar event. Both branches retain
the original debt occurrence. -/
inductive DuplicatedCornerOverlapOutcome
    {component : ContactRawComponent (T := T)}
    (root : GridVertex n n)
    (reserved : Set (PlanarLensRawPhysicalResource (T := T)))
    (debt : RegionalDuplicatedCornerDebt axis hn2 hT component)
    (region : PlanarInwardLensOccurrence axis hn2 hT root) where
  | paid
      (owned : PlanarLensRegionalOwned axis hn2 hT root region)
      (unreserved : planarLensFirstOwnedResourceRaw axis hn2 hT owned.1 ∉ reserved)
  | passed
      (label : PlanarLensTransportLabel axis hn2 hn3 hT root region)
      (valid : label.ValidAt axis hn2 hn3 hT region)

/-- Exact missing shore-follow theorem for the corner defect. `region` must be
the occurrence reached from the second attachment orientation; `second_dart`
keeps that physical orientation explicit rather than collapsing to the corner
vertex. -/
structure DuplicatedCornerOverlapResolution
    {component : ContactRawComponent (T := T)}
    (root : GridVertex n n)
    (reserved : Set (PlanarLensRawPhysicalResource (T := T)))
    (debt : RegionalDuplicatedCornerDebt axis hn2 hT component) where
  region : PlanarInwardLensOccurrence axis hn2 hT root
  second_dart : GridDirectionalDart T := debt.1.1.1.inwardDart
  second_dart_eq : second_dart = debt.1.1.1.inwardDart
  outcome : DuplicatedCornerOverlapOutcome axis hn2 hn3 hT root reserved debt region

/-- Occurrence-labelled paid-or-passed residual. This is the precise gate still
needed to splice the corner debt into the full-pruned regional certificate. -/
def DuplicatedCornerOverlapPaidOrPassed
    {component : ContactRawComponent (T := T)}
    (root : GridVertex n n)
    (reserved : Set (PlanarLensRawPhysicalResource (T := T)))
    (debt : RegionalDuplicatedCornerDebt axis hn2 hT component) : Prop :=
  Nonempty (DuplicatedCornerOverlapResolution axis hn2 hn3 hT root reserved debt)

/-- Constructive regional alternative for the separated corner port. -/
inductive DuplicatedCornerSeparatedPortOutcome
    (root : GridVertex n n)
    (reserved : Set (PlanarLensRawPhysicalResource (T := T)))
    (region : PlanarInwardLensOccurrence axis hn2 hT root)
    (port : SupportedSplitOuterPortResource (T := T)) : Type where
  | paid
      (owned : PlanarLensRegionalOwned axis hn2 hT root region)
      (raw_eq : planarLensFirstOwnedResourceRaw axis hn2 hT owned.1 = .inl port)
      (unreserved : planarLensFirstOwnedResourceRaw axis hn2 hT owned.1 ∉ reserved)
  | rootEscape
      (isRoot : (PlanarInwardLensForest axis hn2 hn3 hT root).parent region = none)

/-- Regional interpretation of the port in the second open corner interval.
The selected port is either first-owned by the launched occurrence and outside
the reservation, or that occurrence is a planar root and therefore starts a
valid occurrence-labelled root escape. -/
structure DuplicatedCornerSeparatedPortRegionalization
    {component : ContactRawComponent (T := T)}
    (root : GridVertex n n)
    (reserved : Set (PlanarLensRawPhysicalResource (T := T)))
    (debt : RegionalDuplicatedCornerDebt axis hn2 hT component)
    (separation : DuplicatedCornerOpenIntervalsMarked axis hn2 hT debt) where
  region : PlanarInwardLensOccurrence axis hn2 hT root
  origin : PlanarLensOriginalDebt axis hn2 hn3 hT root
  selectedPort : SupportedSplitOuterPortResource (T := T) :=
    outerPortOfMarkedSlot (T := T) separation.secondMark
  selectedPort_eq : selectedPort =
    outerPortOfMarkedSlot (T := T) separation.secondMark
  distinct_from_adjacent : selectedPort ≠
    outerPortOfMarkedSlot (T := T) separation.firstMark
  outcome : DuplicatedCornerSeparatedPortOutcome
    axis hn2 hn3 hT root reserved region selectedPort

/-- Conditional discharge after the two exact missing geometric bridges:
open-interval outer-port separation and regional first-ownership/root launch. -/
noncomputable def duplicatedCornerOverlapPaidOrPassed_of_regionalization
    {component : ContactRawComponent (T := T)}
    (root : GridVertex n n)
    (reserved : Set (PlanarLensRawPhysicalResource (T := T)))
    (debt : RegionalDuplicatedCornerDebt axis hn2 hT component)
    (separation : DuplicatedCornerOpenIntervalsMarked axis hn2 hT debt)
    (regional : DuplicatedCornerSeparatedPortRegionalization
      axis hn2 hn3 hT root reserved debt separation) :
    DuplicatedCornerOverlapResolution axis hn2 hn3 hT root reserved debt := by
  cases regional.outcome with
  | paid owned _hraw hunreserved => exact
      { region := regional.region
        second_dart := debt.1.1.1.inwardDart
        second_dart_eq := rfl
        outcome := .paid owned hunreserved }
  | rootEscape hroot =>
    let escape := planarLensCanonicalRootEscape axis hn2 hn3 hT
      regional.origin regional.region
    exact
      { region := regional.region
        second_dart := debt.1.1.1.inwardDart
        second_dart_eq := rfl
        outcome := .passed (.inr (.inr escape))
          (Or.inr ⟨hroot, escape, rfl⟩) }

theorem duplicatedCornerOverlapPaidOrPassed_of_regional_gate
    {component : ContactRawComponent (T := T)}
    (root : GridVertex n n)
    (reserved : Set (PlanarLensRawPhysicalResource (T := T)))
    (debt : RegionalDuplicatedCornerDebt axis hn2 hT component)
    (hregional : ∀ separation :
      DuplicatedCornerOpenIntervalsMarked axis hn2 hT debt,
      Nonempty (DuplicatedCornerSeparatedPortRegionalization
        axis hn2 hn3 hT root reserved debt separation)) :
    DuplicatedCornerOverlapPaidOrPassed axis hn2 hn3 hT root reserved debt := by
  let separation := Classical.choice
    (cornerOuterPortSeparationTopologicalLemma axis hn2 hT component debt)
  let regional := Classical.choice (hregional separation)
  exact ⟨duplicatedCornerOverlapPaidOrPassed_of_regionalization
    axis hn2 hn3 hT root reserved debt separation regional⟩

def DuplicatedCornerOverlapResolution.IsPaid
    {component : ContactRawComponent (T := T)}
    {root : GridVertex n n}
    {reserved : Set (PlanarLensRawPhysicalResource (T := T))}
    {debt : RegionalDuplicatedCornerDebt axis hn2 hT component}
    (resolution : DuplicatedCornerOverlapResolution
      axis hn2 hn3 hT root reserved debt) : Prop :=
  match resolution.outcome with
  | .paid _ _ => True
  | .passed _ _ => False

def DuplicatedCornerOverlapResolution.IsPassed
    {component : ContactRawComponent (T := T)}
    {root : GridVertex n n}
    {reserved : Set (PlanarLensRawPhysicalResource (T := T))}
    {debt : RegionalDuplicatedCornerDebt axis hn2 hT component}
    (resolution : DuplicatedCornerOverlapResolution
      axis hn2 hn3 hT root reserved debt) : Prop :=
  match resolution.outcome with
  | .paid _ _ => False
  | .passed _ _ => True

theorem DuplicatedCornerOverlapResolution.isPaid_or_isPassed
    {component : ContactRawComponent (T := T)}
    {root : GridVertex n n}
    {reserved : Set (PlanarLensRawPhysicalResource (T := T))}
    {debt : RegionalDuplicatedCornerDebt axis hn2 hT component}
    (resolution : DuplicatedCornerOverlapResolution
      axis hn2 hn3 hT root reserved debt) :
    resolution.IsPaid axis hn2 hn3 hT ∨
      resolution.IsPassed axis hn2 hn3 hT := by
  rcases houtcome : resolution.outcome with owned | label
  · left
    simp [DuplicatedCornerOverlapResolution.IsPaid, houtcome]
  · right
    simp [DuplicatedCornerOverlapResolution.IsPassed, houtcome]

theorem RankedCarrierBoundaryCellRegionalCertificate.alternative_injective
    {root : GridVertex n n}
    (certificate : RankedCarrierBoundaryCellRegionalCertificate
      axis hn2 hn3 hT root) :
    Function.Injective (certificate.cells.alternative axis hn2 hT) :=
  certificate.cells.alternative_injective axis hn2 hT

/-- The exact source left by pruning all canonical expanded-contour demands.
It contains reached split-port exits, merger tokens, and surviving roots.  For
the expanded first-stop forest the surviving-root branch is empty, but retaining
the standard type makes the connection to `canonicalShoreDemandPrunedRootEmbeddingWithDirectExits`
definitionally transparent. -/
abbrev FullPrunedSource :=
  (planeChannelForest axis hn2 hT).PrunedRootResource

/-- All canonical demands enter the expanded first-stop forest, so the generic
pruning injection lands directly in its full pruned source. -/
noncomputable def canonicalDemandFullPrunedEmbedding :
    CanonicalShoreDemand axis n ↪ FullPrunedSource axis hn2 hT :=
  (demandEmbedding axis hn2 hn3 hT).trans
    ((planeChannelForest axis hn2 hT).prunedRootDemandEmbedding
      (demands_subset_leaves axis hn2 hT)
      (by rw [exits_eq_roots axis hn2 hT]))

/-- The three pools left after canonical exit-port, internal-edge, and one-per-
carrier component reservations. -/
abbrev FullPrunedTerminalToken :=
  ((planeChannelForest axis hn2 hT).forest.MergerSlot ⊕
    ↥((planeChannelForest axis hn2 hT).forest.roots \
      (planeChannelForest axis hn2 hT).exits))

abbrev FullPrunedTokenCarrier :=
  noninternalTreeEdgeTokenComponent
    (supportFinset (gridGraph n n \ T))
    (terminalTreeEdgeEmbedding axis hn2 hn3 hT)

abbrev FullPrunedResidualResource :=
  ({p : GridCotreeOuterPort T //
      p ∉ Set.range (exitEmbedding axis hn2 hT)} ⊕
    ({e : ↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T))) //
        e ∉ Set.range (internalTreeEdgeTokenEmbedding
          (supportFinset (gridGraph n n \ T))
          (terminalTreeEdgeEmbedding axis hn2 hn3 hT))} ⊕
      {k : FreeFullVertexComponentResource (T := T) //
        k ∉ Set.range (carrierQuotientEmbedding
          (FullPrunedTokenCarrier axis hn2 hn3 hT))}))

/-- Forget reservation proofs and view a residual target as a raw physical
resource. -/
def fullPrunedResidualRaw :
    FullPrunedResidualResource axis hn2 hn3 hT →
      PlanarLensRawPhysicalResource (T := T)
  | .inl p => .inl p.1
  | .inr (.inl e) => .inr (.inl e.1)
  | .inr (.inr k) => .inr (.inr k.1)

/-- Forget reservation proofs without identifying distinct residual resources. -/
def fullPrunedResidualRawEmbedding :
    FullPrunedResidualResource axis hn2 hn3 hT ↪
      PlanarLensRawPhysicalResource (T := T) where
  toFun := fullPrunedResidualRaw axis hn2 hn3 hT
  inj' := by
    intro x y h
    rcases x with p | x <;> rcases y with q | y
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
    · rcases y with e | k <;> simp [fullPrunedResidualRaw] at h
    · rcases x with e | k <;> simp [fullPrunedResidualRaw] at h
    · rcases x with e | k <;> rcases y with f | l
      · exact congrArg (fun z => Sum.inr (Sum.inl z))
          (Subtype.ext (Sum.inl.inj (Sum.inr.inj h)))
      · simp [fullPrunedResidualRaw] at h
      · simp [fullPrunedResidualRaw] at h
      · exact congrArg (fun z => Sum.inr (Sum.inr z))
          (Subtype.ext (Sum.inr.inj (Sum.inr.inj h)))

/-- Contour rank on the full terminal-token type.  The surviving-root case is
empty for the expanded first-stop forest. -/
def fullPrunedTokenRank
    (token : NoninternalTreeEdgeToken
      (supportFinset (gridGraph n n \ T))
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT)) : Nat :=
  match token.1 with
  | .inl merger => canonicalMergerForwardRank axis hn2 hT merger
  | .inr root => False.elim (noSurvivingRoot axis hn2 hT root)

abbrev FullPrunedOrderedCollision :=
  RankedCarrierCollision (FullPrunedTokenCarrier axis hn2 hn3 hT)
    (fullPrunedTokenRank axis hn2 hn3 hT)

/-- Launch every original planar merger debt at its selected child's terminal
token, then split that token into either its unique representative raw
component or an occurrence-labelled ranked collision. -/
noncomputable def planarLensOriginalDebtFullPrunedLaunchEmbedding
    (root : GridVertex n n) :
    PlanarLensOriginalDebt axis hn2 hn3 hT root ↪
      CarrierQuotient (FullPrunedTokenCarrier axis hn2 hn3 hT) ⊕
        FullPrunedOrderedCollision axis hn2 hn3 hT :=
  (planarLensOriginalDebtNoninternalTokenEmbedding
    axis hn2 hn3 hT root).trans
      (rankedCarrierQuotientCollisionEquiv
        (FullPrunedTokenCarrier axis hn2 hn3 hT)
        (fullPrunedTokenRank axis hn2 hn3 hT)).toEmbedding

/-- A representative launch pays with exactly the raw component carried by
the selected noninternal merger token. -/
theorem planarLensOriginalDebtFullPrunedLaunchEmbedding_representative
    (root : GridVertex n n)
    (debt : PlanarLensOriginalDebt axis hn2 hn3 hT root)
    (component : CarrierQuotient
      (FullPrunedTokenCarrier axis hn2 hn3 hT))
    (hlaunch : planarLensOriginalDebtFullPrunedLaunchEmbedding
      axis hn2 hn3 hT root debt = .inl component) :
    carrierQuotientEmbedding (FullPrunedTokenCarrier axis hn2 hn3 hT)
        component =
      FullPrunedTokenCarrier axis hn2 hn3 hT
        (planarLensOriginalDebtNoninternalTokenEmbedding
          axis hn2 hn3 hT root debt) := by
  let token := planarLensOriginalDebtNoninternalTokenEmbedding
    axis hn2 hn3 hT root debt
  let splitEquiv := rankedCarrierQuotientCollisionEquiv
    (FullPrunedTokenCarrier axis hn2 hn3 hT)
    (fullPrunedTokenRank axis hn2 hn3 hT)
  have hsplit : splitEquiv token = .inl component := by
    simpa [planarLensOriginalDebtFullPrunedLaunchEmbedding, token, splitEquiv]
      using hlaunch
  have hrepresentative : token = rankedCarrierRepresentative
      (FullPrunedTokenCarrier axis hn2 hn3 hT)
      (fullPrunedTokenRank axis hn2 hn3 hT) component := by
    calc
      token = splitEquiv.symm (splitEquiv token) :=
        (splitEquiv.symm_apply_apply token).symm
      _ = splitEquiv.symm (.inl component) := congrArg splitEquiv.symm hsplit
      _ = rankedCarrierRepresentative
          (FullPrunedTokenCarrier axis hn2 hn3 hT)
          (fullPrunedTokenRank axis hn2 hn3 hT) component := rfl
  calc
    carrierQuotientEmbedding (FullPrunedTokenCarrier axis hn2 hn3 hT) component =
        carrierQuotientEmbedding (FullPrunedTokenCarrier axis hn2 hn3 hT)
          (carrierQuotientMk (FullPrunedTokenCarrier axis hn2 hn3 hT)
            (rankedCarrierRepresentative
              (FullPrunedTokenCarrier axis hn2 hn3 hT)
              (fullPrunedTokenRank axis hn2 hn3 hT) component)) := by
                rw [carrierQuotientMk_rankedCarrierRepresentative]
    _ = FullPrunedTokenCarrier axis hn2 hn3 hT
        (rankedCarrierRepresentative
          (FullPrunedTokenCarrier axis hn2 hn3 hT)
          (fullPrunedTokenRank axis hn2 hn3 hT) component) := by
            rw [carrierQuotientEmbedding_mk]
    _ = FullPrunedTokenCarrier axis hn2 hn3 hT token := by
      rw [hrepresentative]

/-- A propagated launch collision retains the exact selected terminal token,
and hence the exact original debt through the launch embedding. -/
theorem planarLensOriginalDebtFullPrunedLaunchEmbedding_collision
    (root : GridVertex n n)
    (debt : PlanarLensOriginalDebt axis hn2 hn3 hT root)
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT)
    (hlaunch : planarLensOriginalDebtFullPrunedLaunchEmbedding
      axis hn2 hn3 hT root debt = .inr collision) :
    collision.1 = planarLensOriginalDebtNoninternalTokenEmbedding
      axis hn2 hn3 hT root debt := by
  let token := planarLensOriginalDebtNoninternalTokenEmbedding
    axis hn2 hn3 hT root debt
  let splitEquiv := rankedCarrierQuotientCollisionEquiv
    (FullPrunedTokenCarrier axis hn2 hn3 hT)
    (fullPrunedTokenRank axis hn2 hn3 hT)
  have hsplit : splitEquiv token = .inr collision := by
    simpa [planarLensOriginalDebtFullPrunedLaunchEmbedding, token, splitEquiv]
      using hlaunch
  have htoken : token = collision.1 := by
    calc
      token = splitEquiv.symm (splitEquiv token) :=
        (splitEquiv.symm_apply_apply token).symm
      _ = splitEquiv.symm (.inr collision) := congrArg splitEquiv.symm hsplit
      _ = collision.1 := rfl
  exact htoken.symm

/-- A repeated-carrier collision moving through the planar occurrence forest.
The collision label is never quotiented away while transitions reconverge. -/
structure FullPrunedRegionalState (root : GridVertex n n) where
  collision : FullPrunedOrderedCollision axis hn2 hn3 hT
  region : PlanarInwardLensOccurrence axis hn2 hT root

noncomputable instance fullPrunedRegionalStateFintype (root : GridVertex n n) :
    Fintype (FullPrunedRegionalState axis hn2 hn3 hT root) :=
  Fintype.ofInjective (fun s => (s.collision, s.region)) (by
    intro s t h
    cases s
    cases t
    simpa using h)

/-- Exact constructive C5 certificate over the full pruned source.  Canonical
ports, internal token edges, and one component representative per noninternal
carrier are reserved by the quotient API.  Only ranked, occurrence-labelled
collisions enter this system.  Every nonterminal state uses one selected
cotree transition to its typed planar parent; terminal states are paid by a
first-owned resource outside all canonical reservation ranges.

`terminal_origin` is the geometric no-collision statement at payment.  It is
strictly local to terminal events and is what turns paid-or-passed routing into
the residual embedding; no cardinal or unrestricted-capacity field occurs. -/
structure FullPrunedRegionalCertificate (root : GridVertex n n) where
  system : RankedTransitionSystem
    (FullPrunedOrderedCollision axis hn2 hn3 hT)
    (FullPrunedRegionalState axis hn2 hn3 hT root)
    (LabelledCotreeTransition T)
    (FullPrunedResidualResource axis hn2 hn3 hT)
  origin_eq : ∀ state, system.origin state = state.collision
  start : FullPrunedOrderedCollision axis hn2 hn3 hT ↪
    FullPrunedRegionalState axis hn2 hn3 hT root
  start_origin : ∀ collision, system.origin (start collision) = collision
  selected_parent_transition : ∀ {state next}, system.next state = some next →
    ∃ edge,
      system.transition state = some edge ∧
      (PlanarInwardLensForest axis hn2 hn3 hT root).parent state.region =
        some next.region ∧
      state.region.CotreeTransitionCrossesToParent
        axis hn2 hT next.region edge
  terminal_owned : ∀ {state raw}, system.terminal state = some raw →
    ∃ owned : PlanarLensRegionalOwned axis hn2 hT root state.region,
      planarLensFirstOwnedResourceRaw axis hn2 hT owned.1 =
        fullPrunedResidualRaw axis hn2 hn3 hT raw
  terminal_origin : ∀ {state other raw},
    system.terminal state = some raw →
    system.terminal other = some raw →
    system.origin state = system.origin other

/-- Selected paid-or-passed regional routing gives an injection of the ordered
repeated-carrier collisions into exactly the unreserved physical pools. -/
noncomputable def FullPrunedRegionalCertificate.orderedCollisionEmbedding
    {root : GridVertex n n}
    (certificate : FullPrunedRegionalCertificate axis hn2 hn3 hT root) :
    FullPrunedOrderedCollision axis hn2 hn3 hT ↪
      FullPrunedResidualResource axis hn2 hn3 hT where
  toFun collision := by
    let outcome := certificate.system.exists_terminal_same_origin
      (certificate.start collision)
    exact Classical.choose (Classical.choose_spec outcome)
  inj' := by
    intro collision other heq
    let outcome := certificate.system.exists_terminal_same_origin
      (certificate.start collision)
    let otherOutcome := certificate.system.exists_terminal_same_origin
      (certificate.start other)
    let state := Classical.choose outcome
    let otherState := Classical.choose otherOutcome
    let raw := Classical.choose (Classical.choose_spec outcome)
    let otherRaw := Classical.choose (Classical.choose_spec otherOutcome)
    have hterminal := (Classical.choose_spec
      (Classical.choose_spec outcome)).2.1
    have hotherTerminal := (Classical.choose_spec
      (Classical.choose_spec otherOutcome)).2.1
    have horigin := (Classical.choose_spec
      (Classical.choose_spec outcome)).2.2
    have hotherOrigin := (Classical.choose_spec
      (Classical.choose_spec otherOutcome)).2.2
    change raw = otherRaw at heq
    have hotherTerminal' : certificate.system.terminal otherState = some raw := by
      rw [heq]
      exact hotherTerminal
    have hsame : certificate.system.origin state =
        certificate.system.origin otherState :=
      certificate.terminal_origin hterminal hotherTerminal'
    rw [horigin, hotherOrigin, certificate.start_origin,
      certificate.start_origin] at hsame
    exact hsame

/-- Convert ranked representatives to the arbitrary representative convention
used by `PortAwarePhysicalTreeTokenQuotientRouting`, without changing any
physical reservation. -/
noncomputable def FullPrunedRegionalCertificate.portAwareRouting
    {root : GridVertex n n}
    (certificate : FullPrunedRegionalCertificate axis hn2 hn3 hT root) :
    PortAwarePhysicalTreeTokenQuotientRouting
      (exitEmbedding axis hn2 hT)
      (supportFinset (gridGraph n n \ T))
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT) where
  complementaryEmbedding :=
    (rankedCarrierCollisionEquivCarrierCollision
      (FullPrunedTokenCarrier axis hn2 hn3 hT)
      (fullPrunedTokenRank axis hn2 hn3 hT)).symm.toEmbedding.trans
        certificate.orderedCollisionEmbedding

/-- Embed the ranked launch split directly into physical resources.  Unlike the
legacy port-aware adapter, this map never passes ranked collisions through a
cardinality-built equivalence, so their occurrence labels are preserved. -/
noncomputable def FullPrunedRegionalCertificate.rankedLaunchPhysicalEmbedding
    {root : GridVertex n n}
    (certificate : FullPrunedRegionalCertificate axis hn2 hn3 hT root) :
    (CarrierQuotient (FullPrunedTokenCarrier axis hn2 hn3 hT) ⊕
      FullPrunedOrderedCollision axis hn2 hn3 hT) ↪
        PlanarLensRawPhysicalResource (T := T) where
  toFun
    | .inl q => .inr (.inr (carrierQuotientEmbedding
        (FullPrunedTokenCarrier axis hn2 hn3 hT) q))
    | .inr collision => fullPrunedResidualRaw axis hn2 hn3 hT
        (certificate.orderedCollisionEmbedding axis hn2 hn3 hT collision)
  inj' := by
    intro x y h
    rcases x with q | collision <;> rcases y with r | other
    · exact congrArg Sum.inl
        ((carrierQuotientEmbedding
          (FullPrunedTokenCarrier axis hn2 hn3 hT)).injective
            (Sum.inr.inj (Sum.inr.inj h)))
    · rcases hresidual : certificate.orderedCollisionEmbedding
          axis hn2 hn3 hT other with port | residual
      · simp [hresidual, fullPrunedResidualRaw] at h
      · rcases residual with edge | component
        · simp [hresidual, fullPrunedResidualRaw] at h
        · have heq : carrierQuotientEmbedding
              (FullPrunedTokenCarrier axis hn2 hn3 hT) q = component.1 := by
            simpa [hresidual, fullPrunedResidualRaw] using h
          exact (component.2 ⟨q, heq⟩).elim
    · rcases hresidual : certificate.orderedCollisionEmbedding
          axis hn2 hn3 hT collision with port | residual
      · simp [hresidual, fullPrunedResidualRaw] at h
      · rcases residual with edge | component
        · simp [hresidual, fullPrunedResidualRaw] at h
        · have heq : component.1 = carrierQuotientEmbedding
              (FullPrunedTokenCarrier axis hn2 hn3 hT) r := by
            simpa [hresidual, fullPrunedResidualRaw] using h
          exact (component.2 ⟨r, heq.symm⟩).elim
    · apply congrArg Sum.inr
      apply certificate.orderedCollisionEmbedding.injective
      exact (fullPrunedResidualRawEmbedding axis hn2 hn3 hT).injective h

/-- The full regional certificate supplies an embedding of the exact pruned
source into raw physical resources.  Injectivity and disjointness of all
already-canonical reservations are inherited from
`PortAwarePhysicalTreeTokenQuotientRouting.resourceEmbedding`. -/
noncomputable def FullPrunedRegionalCertificate.fullPrunedEmbedding
    {root : GridVertex n n}
    (certificate : FullPrunedRegionalCertificate axis hn2 hn3 hT root) :
    FullPrunedSource axis hn2 hT ↪
      PlanarLensRawPhysicalResource (T := T) := by
  exact certificate.portAwareRouting.resourceEmbedding

theorem FullPrunedRegionalCertificate.fullPrunedEmbedding_injective
    {root : GridVertex n n}
    (certificate : FullPrunedRegionalCertificate axis hn2 hn3 hT root) :
    Function.Injective certificate.fullPrunedEmbedding :=
  certificate.fullPrunedEmbedding.injective

/-- Every original planar debt has a distinct global physical destination once
the collision-continuation certificate is supplied.  The direct ranked adapter
preserves the exact collision occurrence selected at launch.  This is a
transport into the global raw ledger, not a claim that the selected resource is
first-owned by `root`; regional first-owner stopping remains separate. -/
noncomputable def
    FullPrunedRegionalCertificate.planarLensOriginalDebtPhysicalEmbedding
    {root : GridVertex n n}
    (certificate : FullPrunedRegionalCertificate axis hn2 hn3 hT root) :
    PlanarLensOriginalDebt axis hn2 hn3 hT root ↪
      PlanarLensRawPhysicalResource (T := T) :=
  (planarLensOriginalDebtFullPrunedLaunchEmbedding
    axis hn2 hn3 hT root).trans
      certificate.rankedLaunchPhysicalEmbedding

@[simp] theorem
    FullPrunedRegionalCertificate.planarLensOriginalDebtPhysicalEmbedding_apply
    {root : GridVertex n n}
    (certificate : FullPrunedRegionalCertificate axis hn2 hn3 hT root)
    (debt : PlanarLensOriginalDebt axis hn2 hn3 hT root) :
    certificate.planarLensOriginalDebtPhysicalEmbedding
        axis hn2 hn3 hT debt =
      certificate.rankedLaunchPhysicalEmbedding axis hn2 hn3 hT
        (planarLensOriginalDebtFullPrunedLaunchEmbedding
          axis hn2 hn3 hT root debt) := rfl

/-- An exact ranked representative launch pays with its canonical raw
component. -/
theorem FullPrunedRegionalCertificate.planarLensOriginalDebtPhysicalEmbedding_representative
    {root : GridVertex n n}
    (certificate : FullPrunedRegionalCertificate axis hn2 hn3 hT root)
    (debt : PlanarLensOriginalDebt axis hn2 hn3 hT root)
    (component : CarrierQuotient (FullPrunedTokenCarrier axis hn2 hn3 hT))
    (hlaunch : planarLensOriginalDebtFullPrunedLaunchEmbedding
        axis hn2 hn3 hT root debt = .inl component) :
    certificate.planarLensOriginalDebtPhysicalEmbedding
        axis hn2 hn3 hT debt =
      .inr (.inr (carrierQuotientEmbedding
        (FullPrunedTokenCarrier axis hn2 hn3 hT) component)) := by
  change certificate.rankedLaunchPhysicalEmbedding axis hn2 hn3 hT
      (planarLensOriginalDebtFullPrunedLaunchEmbedding
        axis hn2 hn3 hT root debt) = _
  rw [hlaunch]
  rfl

/-- The exact ranked collision selected at launch is sent to the raw residual
terminal selected for that same collision by the regional certificate. -/
theorem FullPrunedRegionalCertificate.planarLensOriginalDebtPhysicalEmbedding_collision
    {root : GridVertex n n}
    (certificate : FullPrunedRegionalCertificate axis hn2 hn3 hT root)
    (debt : PlanarLensOriginalDebt axis hn2 hn3 hT root)
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT)
    (hlaunch : planarLensOriginalDebtFullPrunedLaunchEmbedding
        axis hn2 hn3 hT root debt = .inr collision) :
    certificate.planarLensOriginalDebtPhysicalEmbedding
        axis hn2 hn3 hT debt =
      fullPrunedResidualRaw axis hn2 hn3 hT
        (certificate.orderedCollisionEmbedding axis hn2 hn3 hT collision) := by
  change certificate.rankedLaunchPhysicalEmbedding axis hn2 hn3 hT
      (planarLensOriginalDebtFullPrunedLaunchEmbedding
        axis hn2 hn3 hT root debt) = _
  rw [hlaunch]
  rfl

/-- Per-planar-root-fiber form of the global physical transport.  Projection to
the original debt is injective inside a fixed active fiber, without asserting
that the physical destination is owned at that planar root occurrence. -/
noncomputable def
    FullPrunedRegionalCertificate.rootActiveDebtFiberPhysicalEmbedding
    {root : GridVertex n n}
    (certificate : FullPrunedRegionalCertificate axis hn2 hn3 hT root)
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (a : ↥((PlanarInwardLensForest axis hn2 hn3 hT root).roots)) :
    routing.ActiveDebtFiber axis hn2 hn3 hT a.1 ↪
      PlanarLensRawPhysicalResource (T := T) where
  toFun debt := certificate.rankedLaunchPhysicalEmbedding axis hn2 hn3 hT
    (planarLensOriginalDebtFullPrunedLaunchEmbedding
      axis hn2 hn3 hT root debt.1)
  inj' := by
    intro debt other h
    apply Subtype.ext
    exact ((planarLensOriginalDebtFullPrunedLaunchEmbedding
      axis hn2 hn3 hT root).trans
        certificate.rankedLaunchPhysicalEmbedding).injective h

/-- The full regional certificate is a constructive strengthening of the old
joint collision residual. -/
theorem FullPrunedRegionalCertificate.canonicalExpandedJointCollisionRouting
    {root : GridVertex n n}
    (certificate : FullPrunedRegionalCertificate axis hn2 hn3 hT root) :
    CanonicalExpandedJointCollisionRouting axis hn2 hn3 hT :=
  ⟨certificate.portAwareRouting⟩

/-! #### Ranked carrier-block gap attempt -/

/-- The terminal token underlying a ranked repeated-carrier collision. -/
def fullPrunedCollisionToken
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT) :
    FullPrunedTerminalToken axis hn2 hT := collision.1.1

/-- Every collision token is a merger token; expanded first-stop roots are all
exits and therefore cannot occur in the surviving-root branch. -/
def fullPrunedCollisionMerger
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT) :
    (planeChannelForest axis hn2 hT).forest.MergerSlot :=
  match fullPrunedCollisionToken axis hn2 hn3 hT collision with
  | .inl merger => merger
  | .inr root => False.elim (noSurvivingRoot axis hn2 hT root)

/-- C5-facing contact enrichment of a residual collision.  Regional routing
can now retain the exact outside contact and attachment orientation instead of
recovering only its quotient component. -/
def fullPrunedCollisionEnrichedToken
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT) :
    ContactEnrichedCanonicalMergerToken axis hn2 hT :=
  ⟨fullPrunedCollisionMerger axis hn2 hn3 hT collision⟩

/-- The impossible surviving-root branch identifies full pruned terminal tokens
with contact-enriched merger tokens. -/
def fullPrunedTokenEnrichedEquiv :
    NoninternalTreeEdgeToken
        (supportFinset (gridGraph n n \ T))
        (terminalTreeEdgeEmbedding axis hn2 hn3 hT) ≃
      ContactEnrichedCanonicalMergerToken axis hn2 hT where
  toFun token := match token.1 with
    | .inl merger => ⟨merger⟩
    | .inr root => False.elim (noSurvivingRoot axis hn2 hT root)
  invFun token := ⟨.inl token.mergerSlot,
    terminalTreeEdgeEmbedding_isNoninternal axis hn2 hn3 hT (.inl token.mergerSlot)⟩
  left_inv token := by
    rcases token with ⟨token, hnoninternal⟩
    rcases token with merger | root
    apply Subtype.ext
    · rfl
    exact False.elim (noSurvivingRoot axis hn2 hT root)
  right_inv token := by
    apply (contactEnrichedCanonicalMergerTokenEquiv axis hn2 hT).injective
    rfl

theorem fullPrunedTokenEnrichedEquiv_rank
    (token : NoninternalTreeEdgeToken
      (supportFinset (gridGraph n n \ T))
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT)) :
    contactEnrichedCanonicalMergerRank axis hn2 hT
        (fullPrunedTokenEnrichedEquiv axis hn2 hn3 hT token) =
      fullPrunedTokenRank axis hn2 hn3 hT token := by
  rcases token with ⟨token, hnoninternal⟩
  rcases token with merger | root
  · rfl
  · exact False.elim (noSurvivingRoot axis hn2 hT root)

theorem fullPrunedTokenEnrichedEquiv_component
    (token : NoninternalTreeEdgeToken
      (supportFinset (gridGraph n n \ T))
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT)) :
    (fullPrunedTokenEnrichedEquiv axis hn2 hn3 hT token).component =
      FullPrunedTokenCarrier axis hn2 hn3 hT token := by
  rcases token with ⟨token, hnoninternal⟩
  rcases token with merger | root
  · exact
      (contactEnrichedCanonicalMergerToken_component_compatible
        axis hn2 hn3 hT (⟨merger⟩ : ContactEnrichedCanonicalMergerToken axis hn2 hT))
  · exact False.elim (noSurvivingRoot axis hn2 hT root)

theorem fullPrunedTokenRank_injective :
    Function.Injective (fullPrunedTokenRank axis hn2 hn3 hT) := by
  intro a b hab
  apply (fullPrunedTokenEnrichedEquiv axis hn2 hn3 hT).injective
  apply contactEnrichedCanonicalMergerRank_injective axis hn2 hT
  simpa only [fullPrunedTokenEnrichedEquiv_rank] using hab

/-- Full-pruned ranked collisions are canonically the enriched merger
collisions with the same carrier and contour rank. -/
def fullPrunedOrderedCollisionEquivEnriched :
    FullPrunedOrderedCollision axis hn2 hn3 hT ≃
      RankedContactEnrichedCarrierCollision axis hn2 hT :=
  rankedCarrierCollisionEquivOfEquiv
    (FullPrunedTokenCarrier axis hn2 hn3 hT)
    (fullPrunedTokenRank axis hn2 hn3 hT)
    (contactEnrichedCanonicalMergerCarrier axis hn2 hT)
    (contactEnrichedCanonicalMergerRank axis hn2 hT)
    (fullPrunedTokenRank_injective axis hn2 hn3 hT)
    (contactEnrichedCanonicalMergerRank_injective axis hn2 hT)
    (fullPrunedTokenEnrichedEquiv axis hn2 hn3 hT)
    (fun a b => by
      rw [contactEnrichedCanonicalMergerCarrier,
        contactEnrichedCanonicalMergerCarrier,
        fullPrunedTokenEnrichedEquiv_component,
        fullPrunedTokenEnrichedEquiv_component])
    (fullPrunedTokenEnrichedEquiv_rank axis hn2 hn3 hT)

theorem fullPrunedOrderedCollisionEquivEnriched_value
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT) :
    (fullPrunedOrderedCollisionEquivEnriched axis hn2 hn3 hT collision).1 =
      fullPrunedCollisionEnrichedToken axis hn2 hn3 hT collision := by
  apply (contactEnrichedCanonicalMergerTokenEquiv axis hn2 hT).injective
  rcases collision with ⟨⟨token, hnoninternal⟩, hcollision⟩
  rcases token with merger | root
  · rfl
  · exact False.elim (noSurvivingRoot axis hn2 hT root)

/-- Restrict an enriched collision to the raw component of its current token. -/
def fullPrunedCollisionComponentContourCollision
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT) :
    ComponentContourCollision axis hn2 hT
      (fullPrunedCollisionEnrichedToken axis hn2 hn3 hT collision).component := by
  let enriched := fullPrunedOrderedCollisionEquivEnriched axis hn2 hn3 hT collision
  let current : ComponentContact axis hn2 hT enriched.1.component := ⟨enriched.1, rfl⟩
  have hvalue : enriched.1 =
      fullPrunedCollisionEnrichedToken axis hn2 hn3 hT collision :=
    fullPrunedOrderedCollisionEquivEnriched_value axis hn2 hn3 hT collision
  rw [← hvalue]
  refine ⟨current, ?_⟩
  rw [mem_rankedCarrierCollision_iff_exists_lt
    (componentContactCarrier axis hn2 hT)
    (componentContourRank axis hn2 hT)
    (componentContourRank_injective axis hn2 hT)]
  have hcollision := enriched.property
  rw [mem_rankedCarrierCollision_iff_exists_lt
    (contactEnrichedCanonicalMergerCarrier axis hn2 hT)
    (contactEnrichedCanonicalMergerRank axis hn2 hT)
    (contactEnrichedCanonicalMergerRank_injective axis hn2 hT)] at hcollision
  obtain ⟨previous, hcomponent, hrank⟩ := hcollision
  let previousLocal : ComponentContact axis hn2 hT enriched.1.component :=
    ⟨previous, hcomponent⟩
  exact ⟨previousLocal, rfl, hrank⟩

/-- Canonical spatial gap selected by a full-pruned ordered collision. -/
noncomputable def fullPrunedCollisionSpatialGap
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT) :
    ComponentSpatialGap axis hn2 hT
      (fullPrunedCollisionEnrichedToken axis hn2 hn3 hT collision).component :=
  componentContourCollisionEquivSpatialGap axis hn2 hT _
    (fullPrunedCollisionComponentContourCollision axis hn2 hn3 hT collision)

theorem fullPrunedCollisionEnrichedToken_component_compatible
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT) :
    (fullPrunedCollisionEnrichedToken axis hn2 hn3 hT collision).component =
      canonicalMergerTokenCarrier axis hn2 hn3 hT
        (fullPrunedCollisionMerger axis hn2 hn3 hT collision) :=
  contactEnrichedCanonicalMergerToken_component_compatible
    axis hn2 hn3 hT _

theorem fullPrunedCollisionEnrichedToken_contact_mem
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT) :
    (fullPrunedCollisionEnrichedToken axis hn2 hn3 hT collision).contact ∈
      (canonicalMergerTokenCarrier axis hn2 hn3 hT
        (fullPrunedCollisionMerger axis hn2 hn3 hT collision)).supp := by
  rw [← fullPrunedCollisionEnrichedToken_component_compatible
    axis hn2 hn3 hT collision]
  exact ContactEnrichedCanonicalMergerToken.contact_mem_component axis hn2 hT _

/-! #### Full-pruned collision germ partition -/

/-- The canonical lens carried by a full-pruned ordered collision. -/
abbrev fullPrunedCollisionLens
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT) :
    CanonicalLens axis hn2 hT :=
  MarkedCycleFirstStop.ReconvergenceLens.ofSlot
    (fullPrunedCollisionMerger axis hn2 hn3 hT collision)

/-- Full-pruned collisions whose direct merger germ is an inward retained
dart. These, rather than all full-pruned collisions, are the natural source of
the planar inward-lens launch API. -/
abbrev FullPrunedInwardCollision :=
  {collision : FullPrunedOrderedCollision axis hn2 hn3 hT //
    ∃ dart : GridDirectionalDart T,
      lensDirectBranchGerm axis hn2 hT
        (fullPrunedCollisionLens axis hn2 hn3 hT collision) = .inward dart}

/-- Full-pruned collisions whose direct merger germ is an actual split outer
port. These rank-zero boundary degeneracies are reserved exits, not inward
regional debts. -/
abbrev FullPrunedOuterCollision :=
  {collision : FullPrunedOrderedCollision axis hn2 hn3 hT //
    ∃ port : GridCotreeOuterPort T,
      lensDirectBranchGerm axis hn2 hT
        (fullPrunedCollisionLens axis hn2 hn3 hT collision) = .outer port}

/-- Every full-pruned collision has exactly one of the two direct-germ forms. -/
theorem fullPrunedCollision_inward_or_outer
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT) :
    (∃ dart : GridDirectionalDart T,
      lensDirectBranchGerm axis hn2 hT
        (fullPrunedCollisionLens axis hn2 hn3 hT collision) = .inward dart) ∨
    (∃ port : GridCotreeOuterPort T,
      lensDirectBranchGerm axis hn2 hT
        (fullPrunedCollisionLens axis hn2 hn3 hT collision) = .outer port) := by
  cases h : lensDirectBranchGerm axis hn2 hT
      (fullPrunedCollisionLens axis hn2 hn3 hT collision) with
  | inward dart => exact Or.inl ⟨dart, rfl⟩
  | outer port => exact Or.inr ⟨port, rfl⟩

/-- The inward and outer collision predicates are disjoint. -/
theorem fullPrunedCollision_not_inward_and_outer
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT) :
    ¬((∃ dart : GridDirectionalDart T,
        lensDirectBranchGerm axis hn2 hT
          (fullPrunedCollisionLens axis hn2 hn3 hT collision) = .inward dart) ∧
      (∃ port : GridCotreeOuterPort T,
        lensDirectBranchGerm axis hn2 hT
          (fullPrunedCollisionLens axis hn2 hn3 hT collision) = .outer port)) := by
  rintro ⟨⟨dart, hdart⟩, ⟨port, hport⟩⟩
  rw [hdart] at hport
  cases hport

/-- Direct germs partition all full-pruned ordered collisions into inward and
outer source obligations. -/
noncomputable def fullPrunedCollisionInwardOuterEquiv :
    FullPrunedOrderedCollision axis hn2 hn3 hT ≃
      (FullPrunedInwardCollision axis hn2 hn3 hT ⊕
        FullPrunedOuterCollision axis hn2 hn3 hT) where
  toFun collision := if h : ∃ dart : GridDirectionalDart T,
      lensDirectBranchGerm axis hn2 hT
        (fullPrunedCollisionLens axis hn2 hn3 hT collision) = .inward dart
    then .inl ⟨collision, h⟩
    else .inr ⟨collision,
      (fullPrunedCollision_inward_or_outer axis hn2 hn3 hT collision).resolve_left h⟩
  invFun
    | .inl collision => collision.1
    | .inr collision => collision.1
  left_inv collision := by
    dsimp only
    split_ifs <;> rfl
  right_inv collision := by
    rcases collision with collision | collision
    · simp only [dif_pos collision.property]
    · have hnot : ¬∃ dart : GridDirectionalDart T,
          lensDirectBranchGerm axis hn2 hT
            (fullPrunedCollisionLens axis hn2 hn3 hT collision.1) = .inward dart := by
        intro hinward
        exact fullPrunedCollision_not_inward_and_outer axis hn2 hn3 hT collision.1
          ⟨hinward, collision.property⟩
      simp only [dif_neg hnot]

/-- Cardinal form of the direct-germ source partition. -/
theorem card_fullPrunedOrderedCollision_eq_inward_add_outer :
    Fintype.card (FullPrunedOrderedCollision axis hn2 hn3 hT) =
      Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) +
        Fintype.card (FullPrunedOuterCollision axis hn2 hn3 hT) := by
  rw [Fintype.card_congr
    (fullPrunedCollisionInwardOuterEquiv axis hn2 hn3 hT), Fintype.card_sum]

/-- A full-pruned collision is recoverable from its merger occurrence. -/
theorem fullPrunedCollisionMerger_injective :
    Function.Injective (fullPrunedCollisionMerger axis hn2 hn3 hT) := by
  intro a b hab
  apply Subtype.ext
  apply fullPrunedTokenRank_injective axis hn2 hn3 hT
  rcases a with ⟨⟨tokenA, hnoninternalA⟩, hcollisionA⟩
  rcases b with ⟨⟨tokenB, hnoninternalB⟩, hcollisionB⟩
  rcases tokenA with mergerA | rootA
  · rcases tokenB with mergerB | rootB
    · exact congrArg (canonicalMergerForwardRank axis hn2 hT) hab
    · exact False.elim (noSurvivingRoot axis hn2 hT rootB)
  · exact False.elim (noSurvivingRoot axis hn2 hT rootA)

namespace FullPrunedInwardCollision

/-- The uniquely determined inward dart of an inward collision. -/
noncomputable def dart
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    GridDirectionalDart T :=
  Classical.choose collision.property

theorem direct_eq
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    lensDirectBranchGerm axis hn2 hT
        (fullPrunedCollisionLens axis hn2 hn3 hT collision.1) =
      .inward (collision.dart axis hn2 hn3 hT) :=
  Classical.choose_spec collision.property

/-- Canonical occurrence at which an inward collision enters the planar lens
hierarchy. -/
noncomputable def launch
    (root : GridVertex n n)
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    PlanarInwardLensOccurrence axis hn2 hT root :=
  planarInwardLensOccurrence axis hn2 hT root
    (fullPrunedCollisionLens axis hn2 hn3 hT collision.1)
    (collision.direct_eq axis hn2 hn3 hT)

/-- The canonical inward launch retains exactly the collision's merger slot. -/
@[simp] theorem launch_slot
    (root : GridVertex n n)
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    (collision.launch axis hn2 hn3 hT root).lens.mergerSlot =
      fullPrunedCollisionMerger axis hn2 hn3 hT collision.1 := rfl

/-- Inward collision labels embed in their canonical planar launch
occurrences; injectivity follows from recovery of the merger token. -/
noncomputable def launchEmbedding (root : GridVertex n n) :
    FullPrunedInwardCollision axis hn2 hn3 hT ↪
      PlanarInwardLensOccurrence axis hn2 hT root where
  toFun collision := collision.launch axis hn2 hn3 hT root
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply fullPrunedCollisionMerger_injective axis hn2 hn3 hT
    exact congrArg
      (fun occurrence : PlanarInwardLensOccurrence axis hn2 hT root =>
        occurrence.lens.mergerSlot) hab

end FullPrunedInwardCollision

namespace FullPrunedOuterCollision

/-- The uniquely determined direct outer port of an outer collision. -/
noncomputable def port
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
    GridCotreeOuterPort T :=
  Classical.choose collision.property

theorem direct_eq
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
    lensDirectBranchGerm axis hn2 hT
        (fullPrunedCollisionLens axis hn2 hn3 hT collision.1) =
      .outer (collision.port axis hn2 hn3 hT) :=
  Classical.choose_spec collision.property

/-- An outer collision is a rank-zero boundary degeneration. -/
theorem lensRank_eq_zero
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
    (fullPrunedCollisionLens axis hn2 hn3 hT collision.1).rank = 0 := by
  let L := fullPrunedCollisionLens axis hn2 hn3 hT collision.1
  have hdirect := collision.direct_eq axis hn2 hn3 hT
  have hslot := lensDirectBranchGerm_slot axis hn2 hT L
  rw [hdirect, lensMergerBranches_directStart_value] at hslot
  have hslot' : GridExpandedContour.outerPortSlot
      (collision.port axis hn2 hn3 hT) = L.mergerState.1.1 := by
    simpa only [CanonicalDirectBranchGerm.slot, lensMergerBranches] using hslot
  rw [L.rank_eq]
  apply ((firstStop axis hn2 hT).distance_eq_zero_iff _).mpr
  rw [← hslot']
  exact Finset.mem_image.mpr
    ⟨collision.port axis hn2 hn3 hT, Finset.mem_univ _, rfl⟩

/-- At rank zero the direct outer port is the same port reached by the lens. -/
theorem port_eq_lensOuterPort
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
    collision.port axis hn2 hn3 hT =
      lensOuterPort axis hn2 hT
        (fullPrunedCollisionLens axis hn2 hn3 hT collision.1) := by
  let L := fullPrunedCollisionLens axis hn2 hn3 hT collision.1
  have hdirect := collision.direct_eq axis hn2 hn3 hT
  have hslot := lensDirectBranchGerm_slot axis hn2 hT L
  rw [hdirect, lensMergerBranches_directStart_value] at hslot
  have hslot' : GridExpandedContour.outerPortSlot
      (collision.port axis hn2 hn3 hT) = L.mergerState.1.1 := by
    simpa only [CanonicalDirectBranchGerm.slot, lensMergerBranches] using hslot
  have hrank := collision.lensRank_eq_zero axis hn2 hn3 hT
  have hreached :=
    MarkedCycleFirstStop.ReconvergenceLens.iterate_rank_mergerState_eq_reachedStop L
  rw [hrank] at hreached
  apply GridExpandedContour.outerPortSlot_injective
  rw [hslot', show L.mergerState.1.1 = L.reachedStop.1 by simpa using hreached]
  exact (outerPortSlot_outerPortOfMarkedSlot (T := T)
    (lensMarkedSlot axis hn2 hT L)).symm

/-- An outer collision's direct port is already in the canonical first-stop
exit reservation range. This is a reservation statement, not a payment. -/
theorem port_mem_range_exitEmbedding
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
    collision.port axis hn2 hn3 hT ∈
      Set.range (exitEmbedding axis hn2 hT) := by
  rw [collision.port_eq_lensOuterPort axis hn2 hn3 hT]
  exact lensOuterPort_mem_range_exitEmbedding axis hn2 hT _

end FullPrunedOuterCollision

/-- A ranked collision launches into the planar hierarchy only when its
concrete merger lens has an inward direct germ.  Marked outer-germ mergers are
deliberately not coerced into inward occurrences. -/
def FullPrunedCollisionLaunchable
    (root : GridVertex n n)
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT) : Prop :=
  ∃ occurrence : PlanarInwardLensOccurrence axis hn2 hT root,
    occurrence.lens.mergerSlot =
      fullPrunedCollisionMerger axis hn2 hn3 hT collision

/-- An explicit inward germ constructs the corresponding collision launch. -/
def fullPrunedCollisionLaunchOfInward
    (root : GridVertex n n)
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT)
    (dart : GridDirectionalDart T)
    (hdart : lensDirectBranchGerm axis hn2 hT
      (MarkedCycleFirstStop.ReconvergenceLens.ofSlot
        (fullPrunedCollisionMerger axis hn2 hn3 hT collision)) = .inward dart) :
    PlanarInwardLensOccurrence axis hn2 hT root :=
  planarInwardLensOccurrence axis hn2 hT root
    (MarkedCycleFirstStop.ReconvergenceLens.ofSlot
      (fullPrunedCollisionMerger axis hn2 hn3 hT collision)) hdart

theorem fullPrunedCollisionLaunchOfInward_slot
    (root : GridVertex n n)
    (collision : FullPrunedOrderedCollision axis hn2 hn3 hT)
    (dart : GridDirectionalDart T)
    (hdart : lensDirectBranchGerm axis hn2 hT
      (MarkedCycleFirstStop.ReconvergenceLens.ofSlot
        (fullPrunedCollisionMerger axis hn2 hn3 hT collision)) = .inward dart) :
    (fullPrunedCollisionLaunchOfInward axis hn2 hn3 hT root collision dart hdart).lens.mergerSlot =
      fullPrunedCollisionMerger axis hn2 hn3 hT collision := rfl

/-- One of the four bare-comb gap orientations, already checked to be assigned
to a concrete planar region.  The retained fourth edge is a local payment
candidate; the omitted fourth edge is a selected, occurrence-labelled pass to
the typed parent. -/
inductive FullPrunedBareCombGap
    (root : GridVertex n n)
    (region : PlanarInwardLensOccurrence axis hn2 hT root) : Type where
  | horizontalSouth (comb : HorizontalSouthBareComb T) (gap : Fin comb.gapCount)
      (assigned : PlanarLensBareCombAlternativeAssigned
        axis hn2 hn3 hT region comb gap)
  | horizontalNorth (comb : HorizontalNorthBareComb T) (gap : Fin comb.gapCount)
      (assigned : PlanarLensHorizontalNorthBareCombAlternativeAssigned
        axis hn2 hn3 hT region comb gap)
  | verticalEast (comb : VerticalEastBareComb T) (gap : Fin comb.gapCount)
      (assigned : PlanarLensVerticalEastBareCombAlternativeAssigned
        axis hn2 hn3 hT region comb gap)
  | verticalWest (comb : VerticalWestBareComb T) (gap : Fin comb.gapCount)
      (assigned : PlanarLensVerticalWestBareCombAlternativeAssigned
        axis hn2 hn3 hT region comb gap)

/-- A bare-comb block gap always yields the already-typed local paid-or-passed
alternative.  This theorem uses no global resource count. -/
theorem FullPrunedBareCombGap.owned_or_passed
    {root : GridVertex n n}
    {region : PlanarInwardLensOccurrence axis hn2 hT root}
    (gap : FullPrunedBareCombGap axis hn2 hn3 hT root region) :
    Nonempty (PlanarLensRegionalOwned axis hn2 hT root region ⊕
      PlanarLensPassedTransition axis hn2 hn3 hT root region) := by
  cases gap with
  | horizontalSouth comb i assigned =>
      exact PlanarLensBoundaryAlternative.assignedTo_owned_or_passed
        axis hn2 hn3 hT region
        (horizontalSouthBareCombPlanarLensBoundaryAlternative comb i) assigned
  | horizontalNorth comb i assigned =>
      exact PlanarLensBoundaryAlternative.assignedTo_owned_or_passed
        axis hn2 hn3 hT region
        (horizontalNorthBareCombPlanarLensBoundaryAlternative comb i) assigned
  | verticalEast comb i assigned =>
      exact PlanarLensBoundaryAlternative.assignedTo_owned_or_passed
        axis hn2 hn3 hT region
        (verticalEastBareCombPlanarLensBoundaryAlternative comb i) assigned
  | verticalWest comb i assigned =>
      exact PlanarLensBoundaryAlternative.assignedTo_owned_or_passed
        axis hn2 hn3 hT region
        (verticalWestBareCombPlanarLensBoundaryAlternative comb i) assigned

/-- A launch-local planar debt exists exactly when the launch is a merger in
the corrected rooted-shore parent forest. Collisionhood itself is defined in
the unrelated first-stop carrier quotient and supplies no such child-count
fact. -/
theorem fullPrunedInwardCollision_launchLocalDebt_nonempty_iff
    (root : GridVertex n n)
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    Nonempty (PlanarLensLocalDebt axis hn2 hn3 hT root
      (collision.launch axis hn2 hn3 hT root)) ↔
      2 ≤ (PlanarInwardLensForest axis hn2 hn3 hT root).childCount
        (collision.launch axis hn2 hn3 hT root) := by
  rw [← (PlanarInwardLensForest axis hn2 hn3 hT root).mem_mergers]
  rw [← (PlanarInwardLensForest axis hn2 hn3 hT root).mergerExcessAt_pos_iff]
  rw [← Fintype.card_pos_iff]
  rw [Fintype.card_congr (planarLensLocalDebtEquivFin
    axis hn2 hn3 hT root (collision.launch axis hn2 hn3 hT root))]
  simp

/-- Exact structural obstruction to attaching a collision at its launch. In
particular, a leaf or unary launch has an empty local-debt fiber regardless of
the collision witness in the first-stop carrier quotient. -/
theorem fullPrunedInwardCollision_launchLocalDebt_isEmpty_of_childCount_le_one
    (root : GridVertex n n)
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT)
    (hcount : (PlanarInwardLensForest axis hn2 hn3 hT root).childCount
      (collision.launch axis hn2 hn3 hT root) ≤ 1) :
    IsEmpty (PlanarLensLocalDebt axis hn2 hn3 hT root
      (collision.launch axis hn2 hn3 hT root)) :=
  ⟨fun debt => by
    have hmerger := (fullPrunedInwardCollision_launchLocalDebt_nonempty_iff
      axis hn2 hn3 hT root collision).mp ⟨debt⟩
    omega⟩

/-- Carrier-block bookkeeping has no geometric assignment data.  An inward
collision already determines its launch, raw component, spatial-gap occurrence,
and omitted cotree edge.  In particular it is not embedded artificially into a
merger slot of the unrelated corrected shore forest: a component contact-tree
leaf is accounted for by either a component root or branch excess. -/
structure FullPrunedCarrierBlockGapAssignment (root : GridVertex n n) : Prop where
  private marker : ∀ collision : FullPrunedInwardCollision axis hn2 hn3 hT,
    collision.launch axis hn2 hn3 hT root =
      collision.launch axis hn2 hn3 hT root := by simp

/-- The carrier-block bookkeeping required by C5 is unconditional. -/
theorem fullPrunedCarrierBlockGapAssignment
    (root : GridVertex n n) :
    FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root :=
  {}

/-- The canonical launch embedding; it is data of the inward collision, not of
the transport assignment. -/
noncomputable def FullPrunedCarrierBlockGapAssignment.launch
    {root : GridVertex n n}
    (_assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  FullPrunedInwardCollision.launchEmbedding axis hn2 hn3 hT root

@[simp] theorem FullPrunedCarrierBlockGapAssignment.launch_slot
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    (assignment.launch axis hn2 hn3 hT collision).lens.mergerSlot =
      fullPrunedCollisionMerger axis hn2 hn3 hT collision.1 :=
  FullPrunedInwardCollision.launch_slot axis hn2 hn3 hT root collision

def FullPrunedCarrierBlockGapAssignment.component
    {axis : ShoreSweepAxis} {hn2 : 2 ≤ n} {hn3 : 3 ≤ n}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    {hT : IsSpanningSubtree (gridGraph n n) T}
    {root : GridVertex n n}
    (_assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    ContactRawComponent (T := T) :=
  (fullPrunedCollisionEnrichedToken axis hn2 hn3 hT collision).component

noncomputable def FullPrunedCarrierBlockGapAssignment.spatialGap
    {axis : ShoreSweepAxis} {hn2 : 2 ≤ n} {hn3 : 3 ≤ n}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    {hT : IsSpanningSubtree (gridGraph n n) T}
    {root : GridVertex n n}
    (_assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    ComponentSpatialGap axis hn2 hT
      (_assignment.component collision) :=
  fullPrunedCollisionSpatialGap axis hn2 hn3 hT collision

noncomputable def FullPrunedCarrierBlockGapAssignment.occurrence
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    ComponentOmittedEdgeOccurrence axis hn2 hT (assignment.component collision) :=
  componentSpatialGapEquivOrdinarySumDuplicatedCorner axis hn2 hT
    (assignment.component collision) (assignment.spatialGap collision)

noncomputable def FullPrunedCarrierBlockGapAssignment.transition
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    LabelledCotreeTransition T :=
  componentOmittedEdgeTransition axis hn2 hn3 hT
    (assignment.occurrence axis hn2 hn3 hT collision)

/-- One endpoint-side of an occurrence-labelled omitted edge in the cotree
dual. The original collision remains in the state, so equal geometric edges do
not identify propagation states. -/
structure FullPrunedCotreeDualPropagationState
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) where
  collision : FullPrunedInwardCollision axis hn2 hn3 hT
  face : GridFace n n
  incident : face = (assignment.transition axis hn2 hn3 hT collision).1.dualEndpoints.1 ∨
    face = (assignment.transition axis hn2 hn3 hT collision).1.dualEndpoints.2

/-- Cross the selected omitted coordinate edge to its other incident dual
face, preserving the collision and ordinary/corner occurrence labels. -/
noncomputable def FullPrunedCotreeDualPropagationState.next
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (state : FullPrunedCotreeDualPropagationState axis hn2 hn3 hT assignment) :
    FullPrunedCotreeDualPropagationState axis hn2 hn3 hT assignment := by
  let endpoints :=
    (assignment.transition axis hn2 hn3 hT state.collision).1.dualEndpoints
  by_cases hfirst : state.face = endpoints.1
  · exact
      { collision := state.collision
        face := endpoints.2
        incident := Or.inr rfl }
  · have hsecond : state.face = endpoints.2 := state.incident.resolve_left hfirst
    exact
      { collision := state.collision
        face := endpoints.1
        incident := Or.inl rfl }

@[simp] theorem FullPrunedCotreeDualPropagationState.next_collision
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (state : FullPrunedCotreeDualPropagationState axis hn2 hn3 hT assignment) :
    (state.next (axis := axis) (hn2 := hn2) (hn3 := hn3)
      (hT := hT)).collision = state.collision := by
  classical
  unfold FullPrunedCotreeDualPropagationState.next
  dsimp only
  split_ifs <;> rfl

/-! #### Component-resolved boundary-gap forest ledger -/

/-- Boundary ports not already occupied by actual first-stop exits. -/
abbrev UnreservedCanonicalBoundaryPort :=
  {p : GridCotreeOuterPort T // p ∉ Set.range (exitEmbedding axis hn2 hT)}

/-- An outer collision's port is reserved by the canonical exit embedding and
therefore cannot be packaged as an unreserved boundary port. This does not
assert that the collision is paid by that port. -/
theorem FullPrunedOuterCollision.port_not_unreserved
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
    ¬∃ port : UnreservedCanonicalBoundaryPort axis hn2 hT,
      port.1 = collision.port axis hn2 hn3 hT := by
  rintro ⟨port, hport⟩
  apply port.2
  rw [hport]
  exact collision.port_mem_range_exitEmbedding axis hn2 hn3 hT

/-- Branch resources retain their planar first-owner witness. Forgetting these
witnesses gives either a retained internal support edge or one raw free
component, never an occurrence-counted contact. -/
abbrev BoundaryGapFirstOwnedBranchResource (root : GridVertex n n) :=
  FirstOwnedInternalSupportEdges axis hn2 hT root ⊕
    FirstOwnedFreeComponents axis hn2 hT root

/-- Raw physical resource underlying a first-owned boundary-gap branch. -/
def boundaryGapFirstOwnedBranchResourceRaw
    {root : GridVertex n n} :
    BoundaryGapFirstOwnedBranchResource axis hn2 hT root →
      (RetainedInternalSupportEdgeResource (T := T) ⊕
        FreeFullVertexComponentResource (T := T))
  | .inl edge => .inl edge.resource
  | .inr component => .inr component.resource

theorem boundaryGapFirstOwnedBranchResourceRaw_injective
    (hn3 : 3 ≤ n) {root : GridVertex n n} :
    Function.Injective
      (boundaryGapFirstOwnedBranchResourceRaw (axis := axis) (hn2 := hn2)
        (hT := hT) (root := root)) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl
      ((firstOwnedInternalSupportEdgeEmbedding axis hn2 hT hn3 root).injective
        (Sum.inl.inj hab))
  · cases hab
  · cases hab
  · exact congrArg Sum.inr
      ((firstOwnedFreeComponentEmbedding axis hn2 hT hn3 root).injective
        (Sum.inr.inj hab))

/-- Assignment-selected omitted-edge occurrences in one raw component.  The
collision itself is retained as provenance even when coordinate edges agree. -/
abbrev FullPrunedComponentEdgeOccurrence
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (component : ContactRawComponent (T := T)) :=
  {collision : FullPrunedInwardCollision axis hn2 hn3 hT //
    assignment.component collision = component}

/-- The selected transition of a component occurrence is exactly
`assignment.transition`. -/
noncomputable def fullPrunedComponentOccurrenceTransition
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    {component : ContactRawComponent (T := T)}
    (occurrence : FullPrunedComponentEdgeOccurrence
      axis hn2 hn3 hT assignment component) : LabelledCotreeTransition T :=
  assignment.transition axis hn2 hn3 hT occurrence.1

/-- Legacy complete edge-occurrence universe for dual paths in one component fiber:
every component spatial-gap occurrence plus one continuation occurrence for
every genuine cotree edge.  The summands are not quotiented when their
coordinate edges agree.  The active grouped ledger uses the global shared
universe below instead; this component-indexed universe duplicates its
continuation core. -/
abbrev FullPrunedComponentCotreeDualEdgeOccurrence
    {root : GridVertex n n}
    (_assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (component : ContactRawComponent (T := T)) :=
  ComponentOmittedEdgeOccurrence axis hn2 hT component ⊕
    LabelledCotreeTransition T

noncomputable def fullPrunedComponentCotreeDualEdgeTransition
    {root : GridVertex n n}
  (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    {component : ContactRawComponent (T := T)} :
    FullPrunedComponentCotreeDualEdgeOccurrence
      axis hn2 hn3 hT assignment component → LabelledCotreeTransition T
  | .inl gap => componentOmittedEdgeTransition axis hn2 hn3 hT gap
  | .inr continuation => continuation

/-! #### Global shared occurrence-labelled cotree dual

The left summand below contains only private selected-gap occurrences.  The
right summand is the actual cotree-transition type itself, so each genuine
continuation transition occurs exactly once globally.  Consequently bounded
faces and continuation vertices are shared across all raw components. -/

/-- Selected gaps whose chosen edge is not itself a boundary edge. Boundary
selected gaps use the unique actual continuation occurrence instead, ensuring
that the shared core has one boundary occurrence per coordinate cotree edge. -/
abbrev FullPrunedSharedInteriorGapOccurrence
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  {collision : FullPrunedInwardCollision axis hn2 hn3 hT //
    (assignment.transition axis hn2 hn3 hT collision).1.dualEndpoints.1 ≠
        GridFace.out ∧
      (assignment.transition axis hn2 hn3 hT collision).1.dualEndpoints.2 ≠
        GridFace.out}

/-- Global edge-occurrence universe. A nonboundary selected gap retains its
complete collision provenance; actual transitions, including every boundary
transition, are not component indexed. -/
noncomputable instance fullPrunedInwardCollisionFintype :
    Fintype (FullPrunedInwardCollision axis hn2 hn3 hT) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

abbrev FullPrunedSharedCotreeDualEdgeOccurrence
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  FullPrunedSharedInteriorGapOccurrence axis hn2 hn3 hT assignment ⊕
    LabelledCotreeTransition T

noncomputable instance canonicalFullPrunedSharedCotreeDualEdgeOccurrenceFintype
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    Fintype (FullPrunedSharedCotreeDualEdgeOccurrence
      axis hn2 hn3 hT assignment) := by
  unfold FullPrunedSharedCotreeDualEdgeOccurrence
  infer_instance

noncomputable instance canonicalFullPrunedSharedCotreeDualEdgeOccurrenceDecidableEq
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    DecidableEq (FullPrunedSharedCotreeDualEdgeOccurrence
      axis hn2 hn3 hT assignment) := by
  unfold FullPrunedSharedCotreeDualEdgeOccurrence
  infer_instance

/-- Transition label of a global occurrence.  Equal selected gap labels remain
private occurrence vertices, while the continuation summand has exactly one
vertex per actual labelled cotree transition. -/
noncomputable def fullPrunedSharedCotreeDualEdgeTransition
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    FullPrunedSharedCotreeDualEdgeOccurrence axis hn2 hn3 hT assignment →
      LabelledCotreeTransition T :=
  CotreeDualEdgeOccurrenceUniverse.transition
    (fun gap : FullPrunedSharedInteriorGapOccurrence axis hn2 hn3 hT assignment =>
      assignment.transition axis hn2 hn3 hT gap.1) id

/-- A boundary-selected collision attaches to the unique continuation
occurrence for its actual edge; only nonboundary collisions retain a private
gap occurrence in the core. -/
noncomputable def fullPrunedSharedCotreeDualSelectedOccurrence
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    FullPrunedInwardCollision axis hn2 hn3 hT →
      FullPrunedSharedCotreeDualEdgeOccurrence axis hn2 hn3 hT assignment :=
  fun collision => if hboundary :
      (assignment.transition axis hn2 hn3 hT collision).1.dualEndpoints.1 =
          GridFace.out ∨
        (assignment.transition axis hn2 hn3 hT collision).1.dualEndpoints.2 =
          GridFace.out
    then .inr (assignment.transition axis hn2 hn3 hT collision)
    else .inl ⟨collision, not_or.mp hboundary⟩

/-- A selected global occurrence retains its raw-component provenance. -/
def fullPrunedSharedCotreeDualSelectedComponent
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    ContactRawComponent (T := T) :=
  assignment.component collision

/-- A selected global occurrence retains its spatial-gap provenance. -/
noncomputable def fullPrunedSharedCotreeDualSelectedSpatialGap
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    ComponentSpatialGap axis hn2 hT
      (fullPrunedSharedCotreeDualSelectedComponent
        axis hn2 hn3 hT assignment collision) :=
  assignment.spatialGap collision

/-- Shared global carrier: private collision leaves over one shared split
occurrence-labelled cotree core. -/
abbrev FullPrunedSharedCotreeDualCarrier
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  SplitOccurrenceLabelledCotreeDualCarrier
    (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
    (FullPrunedInwardCollision axis hn2 hn3 hT)

/-- Parent forest on the global shared occurrence-labelled dual. -/
noncomputable def fullPrunedSharedCotreeDualForest
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    ParentForest (FullPrunedSharedCotreeDualCarrier
      axis hn2 hn3 hT assignment) :=
  SplitOccurrenceLabelledCotreeDualCarrier.forest
    (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
    (fullPrunedSharedCotreeDualSelectedOccurrence
      axis hn2 hn3 hT assignment)

/-- Every inward collision is attached as a private leaf to its selected actual
transition occurrence in the shared core. -/
noncomputable def fullPrunedSharedCotreeDualStartLeaf
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    FullPrunedInwardCollision axis hn2 hn3 hT ↪
      ↥((fullPrunedSharedCotreeDualForest
        axis hn2 hn3 hT assignment).leaves) :=
  SplitOccurrenceLabelledCotreeDualCarrier.startLeafEmbedding
    (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
    (fullPrunedSharedCotreeDualSelectedOccurrence
      axis hn2 hn3 hT assignment)

@[simp] theorem fullPrunedSharedCotreeDualStartLeaf_parent
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    (fullPrunedSharedCotreeDualForest axis hn2 hn3 hT assignment).parent
        (fullPrunedSharedCotreeDualStartLeaf
          axis hn2 hn3 hT assignment collision).1 =
      some (.inr (.inl
        (fullPrunedSharedCotreeDualSelectedOccurrence
          axis hn2 hn3 hT assignment collision))) := by
  rfl

/-- The identity continuation summand, exhibiting exactly one continuation
occurrence for each actual labelled cotree transition. -/
def fullPrunedSharedCotreeDualContinuationOccurrence
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    LabelledCotreeTransition T ↪
      FullPrunedSharedCotreeDualEdgeOccurrence axis hn2 hn3 hT assignment where
  toFun := Sum.inr
  inj' := Sum.inr_injective

@[simp] theorem fullPrunedSharedCotreeDualContinuation_transition
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (transition : LabelledCotreeTransition T) :
    fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment
        (fullPrunedSharedCotreeDualContinuationOccurrence
          axis hn2 hn3 hT assignment transition) =
      transition := rfl

/-- Every boundary occurrence in the shared universe is the unique continuation
occurrence of its actual cotree edge. Consequently its edge label is injective. -/
theorem fullPrunedSharedCotreeDualBoundary_edge_injective
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    Function.Injective fun boundary : BoundaryTransitionOccurrence
        (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment) =>
      (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment
        boundary.1).1 := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hedge
  apply Subtype.ext
  cases a with
  | inl a => exact (ha.elim a.2.1 a.2.2).elim
  | inr a =>
      cases b with
      | inl b => exact (hb.elim b.2.1 b.2.2).elim
      | inr b =>
          apply congrArg Sum.inr
          exact Subtype.ext hedge

/-- Boundary occurrences in the global shared core choose distinct physical
ports. Corners are separated by their side tags. -/
theorem fullPrunedSharedCotreeDualBoundary_portChoiceInjective
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    BoundaryTransitionOccurrence.PortChoiceInjective
      (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
      hn2 hn2 :=
  BoundaryTransitionOccurrence.portChoiceInjective_of_edge_injective
    (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
    hn2 hn2
    (fullPrunedSharedCotreeDualBoundary_edge_injective
      axis hn2 hn3 hT assignment)

/-- The shared universe reaches the split outer boundary because it contains
the identity continuation occurrence for every actual cotree transition. -/
theorem fullPrunedSharedCotreeDualBoundaryConnectivity
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    SplitOccurrenceCotreeDualCore.ReachesSplitOuterBoundary
      (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment) := by
  apply SplitOccurrenceCotreeDualCore.reachesSplitOuterBoundary_of_fullCotree
    (transition := fullPrunedSharedCotreeDualEdgeTransition
      axis hn2 hn3 hT assignment)
    (SplitOccurrenceCotreeDualCore.gridSpanningTreeCotreeDualBoundaryConnectivity_square
      hn3 hT) Sum.inr
  · intro edge
    rfl
  · intro occurrence
    cases occurrence with
    | inr edge => exact SimpleGraph.Reachable.refl _
    | inl collision =>
        apply SplitOccurrenceCotreeDualCore.occurrences_reachable_of_transition_eq
          (transition := fullPrunedSharedCotreeDualEdgeTransition
            axis hn2 hn3 hT assignment) hn2 hn2
        rfl

/-- Exact ambient root classification: global roots are precisely private
outer occurrences.  There are no fictitious bounded roots. -/
theorem fullPrunedSharedCotreeDual_mem_roots_iff_boundary
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (x : FullPrunedSharedCotreeDualCarrier axis hn2 hn3 hT assignment) :
    x ∈ (fullPrunedSharedCotreeDualForest axis hn2 hn3 hT assignment).roots ↔
      ∃ b : BoundaryTransitionOccurrence
        (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment),
        x = .inr (.inr (.inr b)) := by
  unfold fullPrunedSharedCotreeDualForest
  rw [SplitOccurrenceLabelledCotreeDualCarrier.mem_roots_iff]
  constructor
  · rintro (⟨b, rfl⟩ | ⟨y, rfl, hunreachable⟩)
    · exact ⟨b, rfl⟩
    · exact False.elim (hunreachable
        (fullPrunedSharedCotreeDualBoundaryConnectivity
          axis hn2 hn3 hT assignment y))
  · rintro ⟨b, rfl⟩
    exact Or.inl ⟨b, rfl⟩

/-- Minimal ancestor hull generated by exactly the inward collision leaves. -/
abbrev FullPrunedSharedCotreeDualHullCarrier
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  (fullPrunedSharedCotreeDualForest axis hn2 hn3 hT assignment).AncestorHull
    (fullPrunedSharedCotreeDualStartLeaf axis hn2 hn3 hT assignment)

noncomputable def fullPrunedSharedCotreeDualHullForest
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    ParentForest (FullPrunedSharedCotreeDualHullCarrier
      axis hn2 hn3 hT assignment) :=
  (fullPrunedSharedCotreeDualForest axis hn2 hn3 hT assignment).ancestorHullForest
    (fullPrunedSharedCotreeDualStartLeaf axis hn2 hn3 hT assignment)

/-- Inward sources below a vertex of the global shared hull. -/
noncomputable def fullPrunedSharedCotreeDualHullDescendantSources
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (vertex : FullPrunedSharedCotreeDualHullCarrier
      axis hn2 hn3 hT assignment) :
    Finset (FullPrunedInwardCollision axis hn2 hn3 hT) :=
  (fullPrunedSharedCotreeDualForest axis hn2 hn3 hT assignment)
    |>.ancestorHullDescendantSources
      (fullPrunedSharedCotreeDualStartLeaf axis hn2 hn3 hT assignment) vertex

/-- Raw component labels of every inward source below a global hull vertex. -/
noncomputable def fullPrunedSharedCotreeDualHullDescendantComponents
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (vertex : FullPrunedSharedCotreeDualHullCarrier
      axis hn2 hn3 hT assignment) : Finset (ContactRawComponent (T := T)) :=
  (fullPrunedSharedCotreeDualForest axis hn2 hn3 hT assignment)
    |>.ancestorHullDescendantLabels
      (fullPrunedSharedCotreeDualStartLeaf axis hn2 hn3 hT assignment)
      assignment.component vertex

/-- Active global branch slots retain all descendant source-component labels. -/
noncomputable def fullPrunedSharedCotreeDualHullMergerSlotDescendantComponents
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    Finset (ContactRawComponent (T := T)) :=
  (fullPrunedSharedCotreeDualForest axis hn2 hn3 hT assignment)
    |>.ancestorHullMergerSlotDescendantLabels
      (fullPrunedSharedCotreeDualStartLeaf axis hn2 hn3 hT assignment)
      assignment.component slot

theorem fullPrunedSharedCotreeDualHullMergerSlotDescendantComponents_nonempty
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    (fullPrunedSharedCotreeDualHullMergerSlotDescendantComponents
      axis hn2 hn3 hT assignment slot).Nonempty :=
  (fullPrunedSharedCotreeDualForest axis hn2 hn3 hT assignment)
    |>.ancestorHullMergerSlotDescendantLabels_nonempty
      (fullPrunedSharedCotreeDualStartLeaf axis hn2 hn3 hT assignment)
      assignment.component slot

/-- One active global shared-hull merger slot, refined by one of the raw
components actually represented below that slot.  A shared sector need not have
a canonical single component, so the component is part of the obligation. -/
abbrev FullPrunedSharedCotreeDualHullMergerComponentObligation
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  Σ slot : (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot,
    ↥(fullPrunedSharedCotreeDualHullMergerSlotDescendantComponents
      axis hn2 hn3 hT assignment slot)

/-- The component fiber of a refined active merger obligation. -/
def fullPrunedSharedCotreeDualHullMergerObligationComponent
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root} :
    FullPrunedSharedCotreeDualHullMergerComponentObligation
        axis hn2 hn3 hT assignment → ContactRawComponent (T := T) :=
  fun obligation => obligation.2.1

/-- The leaves of the minimal shared hull are exactly, not merely at least, the
inward collision starts. -/
noncomputable def fullPrunedSharedCotreeDualHullLeafEquiv
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    FullPrunedInwardCollision axis hn2 hn3 hT ≃
      ↥((fullPrunedSharedCotreeDualHullForest
        axis hn2 hn3 hT assignment).leaves) :=
  (fullPrunedSharedCotreeDualForest axis hn2 hn3 hT assignment).ancestorHullLeafEquiv
    (fullPrunedSharedCotreeDualStartLeaf axis hn2 hn3 hT assignment)

/-- A retained hull root is an ambient shared-dual root. -/
noncomputable def fullPrunedSharedCotreeDualHullRootEmbedding
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    ↥((fullPrunedSharedCotreeDualHullForest
        axis hn2 hn3 hT assignment).roots) ↪
      ↥((fullPrunedSharedCotreeDualForest
        axis hn2 hn3 hT assignment).roots) where
  toFun x := ⟨x.1.1,
    ((fullPrunedSharedCotreeDualForest axis hn2 hn3 hT assignment)
      |>.mem_ancestorHullForest_roots_iff
        (fullPrunedSharedCotreeDualStartLeaf axis hn2 hn3 hT assignment)
        x.1).mp x.2⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun x : ↥((fullPrunedSharedCotreeDualForest
        axis hn2 hn3 hT assignment).roots) => x.1) hab

/-- Boundary occurrence represented by an ambient shared-dual root. -/
noncomputable def fullPrunedSharedCotreeDualRootBoundary
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (x : ↥((fullPrunedSharedCotreeDualForest
      axis hn2 hn3 hT assignment).roots)) :
    BoundaryTransitionOccurrence
      (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment) :=
  Classical.choose ((fullPrunedSharedCotreeDual_mem_roots_iff_boundary
    axis hn2 hn3 hT assignment x.1).mp x.2)

theorem fullPrunedSharedCotreeDualRootBoundary_spec
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (x : ↥((fullPrunedSharedCotreeDualForest
      axis hn2 hn3 hT assignment).roots)) :
    x.1 = .inr (.inr (.inr
      (fullPrunedSharedCotreeDualRootBoundary axis hn2 hn3 hT assignment x))) :=
  Classical.choose_spec ((fullPrunedSharedCotreeDual_mem_roots_iff_boundary
    axis hn2 hn3 hT assignment x.1).mp x.2)

/-- Physical outer-port map obtained from the exact private-boundary root
classification. -/
noncomputable def fullPrunedSharedCotreeDualHullRootPort
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots) → GridCotreeOuterPort T :=
  fun activeRoot => BoundaryTransitionOccurrence.outerPort
    (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
    hn2 hn2
    (fullPrunedSharedCotreeDualRootBoundary axis hn2 hn3 hT assignment
      (fullPrunedSharedCotreeDualHullRootEmbedding
        axis hn2 hn3 hT assignment activeRoot))

/-- The physical root-port map of the active global hull is injective. -/
theorem fullPrunedSharedCotreeDualHullRootPort_injective
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    Function.Injective (fullPrunedSharedCotreeDualHullRootPort
      axis hn2 hn3 hT assignment) := by
  intro a b hab
  let ea := fullPrunedSharedCotreeDualHullRootEmbedding
    axis hn2 hn3 hT assignment a
  let eb := fullPrunedSharedCotreeDualHullRootEmbedding
    axis hn2 hn3 hT assignment b
  have hboundary : fullPrunedSharedCotreeDualRootBoundary
      axis hn2 hn3 hT assignment ea =
      fullPrunedSharedCotreeDualRootBoundary
        axis hn2 hn3 hT assignment eb :=
    fullPrunedSharedCotreeDualBoundary_portChoiceInjective
      axis hn2 hn3 hT assignment hab
  apply (fullPrunedSharedCotreeDualHullRootEmbedding
    axis hn2 hn3 hT assignment).injective
  apply Subtype.ext
  rw [fullPrunedSharedCotreeDualRootBoundary_spec axis hn2 hn3 hT assignment ea,
    fullPrunedSharedCotreeDualRootBoundary_spec axis hn2 hn3 hT assignment eb,
    hboundary]

/-- No duplicate-root debt remains in the active global shared hull. -/
theorem fullPrunedSharedCotreeDualHull_rootPortDebt_eq_zero
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    (fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment).rootPortDebt
      (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment) = 0 :=
  ((fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment)
    |>.rootPortDebt_eq_zero_iff_injective
      (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment)).2
    (fullPrunedSharedCotreeDualHullRootPort_injective
      axis hn2 hn3 hT assignment)

/-- Exact global Euler ledger after boundary occurrence canonicalization:
`|I| = usedPorts + branchExcess`. -/
theorem fullPrunedSharedCotreeDualHull_card_starts_eq_grouped
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) =
      ((fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment).usedRootPorts
        (fullPrunedSharedCotreeDualHullRootPort
          axis hn2 hn3 hT assignment)).card +
      (fullPrunedSharedCotreeDualHullForest
        axis hn2 hn3 hT assignment).branchExcess := by
  let F := fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment
  let rootPort := fullPrunedSharedCotreeDualHullRootPort
    axis hn2 hn3 hT assignment
  have heuler : Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) =
      F.roots.card + F.branchExcess :=
    ParentForest.card_start_eq_card_ancestorHull_roots_add_branchExcess
      (fullPrunedSharedCotreeDualForest axis hn2 hn3 hT assignment)
      (fullPrunedSharedCotreeDualStartLeaf axis hn2 hn3 hT assignment)
  have hroots : (F.usedRootPorts rootPort).card + F.rootPortDebt rootPort =
      F.roots.card := F.card_usedRootPorts_add_rootPortDebt rootPort
  have hdebt : F.rootPortDebt rootPort = 0 :=
    fullPrunedSharedCotreeDualHull_rootPortDebt_eq_zero
      axis hn2 hn3 hT assignment
  change Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) =
    (F.usedRootPorts rootPort).card + F.branchExcess
  omega

/-- The exact all-gap occurrence selected by an inward start.  The component
equality in the start subtype performs the dependent reindexing. -/
noncomputable def fullPrunedComponentSelectedEdgeOccurrence
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    {component : ContactRawComponent (T := T)}
    (selected : FullPrunedComponentEdgeOccurrence
      axis hn2 hn3 hT assignment component) :
    FullPrunedComponentCotreeDualEdgeOccurrence
      axis hn2 hn3 hT assignment component := by
  rcases selected with ⟨collision, hcomponent⟩
  subst component
  exact .inl (assignment.occurrence axis hn2 hn3 hT collision)

/-- Legacy carrier of the componentwise occurrence-split cotree-dual forest. Each raw
component has its own bounded-face vertices and private boundary occurrences. -/
abbrev FullPrunedComponentCotreeDualCarrier
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  Σ component : ContactRawComponent (T := T),
    SplitOccurrenceLabelledCotreeDualCarrier
      (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment
        (component := component))
      (FullPrunedComponentEdgeOccurrence axis hn2 hn3 hT assignment component)

/-- Legacy disjoint union indexed by raw component.  Its component-labelled
face and continuation copies are precisely what the global shared core removes. -/
noncomputable def fullPrunedComponentCotreeDualForest
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    ParentForest (FullPrunedComponentCotreeDualCarrier
      axis hn2 hn3 hT assignment) where
  parent x :=
    ((SplitOccurrenceLabelledCotreeDualCarrier.forest
      (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
      (fullPrunedComponentSelectedEdgeOccurrence
        axis hn2 hn3 hT assignment)).parent x.2).map (Sigma.mk x.1)
  rank x :=
    (SplitOccurrenceLabelledCotreeDualCarrier.forest
      (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
      (fullPrunedComponentSelectedEdgeOccurrence
        axis hn2 hn3 hT assignment)).rank x.2
  rank_parent := by
    rintro ⟨component, v⟩ ⟨component', w⟩ hparent
    simp only [Option.map_eq_some_iff] at hparent
    obtain ⟨w', hw', hw⟩ := hparent
    cases hw
    exact (SplitOccurrenceLabelledCotreeDualCarrier.forest
      (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
      (fullPrunedComponentSelectedEdgeOccurrence
        axis hn2 hn3 hT assignment)).rank_parent hw'

/-- Every inward collision is the private leaf attached to its selected omitted
occurrence in its raw-component fiber. -/
noncomputable def fullPrunedComponentCotreeDualStartLeaf
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    FullPrunedInwardCollision axis hn2 hn3 hT ↪
      ↥((fullPrunedComponentCotreeDualForest
        axis hn2 hn3 hT assignment).leaves) where
  toFun collision := by
    let occurrence : FullPrunedComponentEdgeOccurrence
        axis hn2 hn3 hT assignment (assignment.component collision) :=
      ⟨collision, rfl⟩
    refine ⟨⟨assignment.component collision, .inl occurrence⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨component, v⟩ hv
    have hparent : (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment).parent
        ⟨component, v⟩ = some ⟨assignment.component collision, .inl occurrence⟩ :=
      by simpa only [ParentForest.children, Finset.mem_filter, Finset.mem_univ, true_and] using hv
    simp only [fullPrunedComponentCotreeDualForest, Option.map_eq_some_iff] at hparent
    obtain ⟨a, ha, heq⟩ := hparent
    obtain ⟨hcomponent, hea⟩ := Sigma.mk.inj_iff.mp heq
    subst component
    have hea' : a = .inl occurrence := eq_of_heq hea
    subst a
    exact SplitOccurrenceLabelledCotreeDualCarrier.no_parent_is_privateLeaf
      (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
      (fullPrunedComponentSelectedEdgeOccurrence
        axis hn2 hn3 hT assignment)
      v occurrence ha
  inj' := by
    intro a b hab
    have hcarrier := congrArg (fun x => x.1) hab
    have hcollision := congrArg
      (fun x : FullPrunedComponentCotreeDualCarrier
          axis hn2 hn3 hT assignment =>
        match x.2 with
        | .inl occurrence => some occurrence.1
        | .inr _ => none) hcarrier
    exact Option.some.inj hcollision

/-! #### Legacy component-split hull audit layer

This layer copies the cotree continuation universe into each raw-component
fiber.  It remains useful for counterexamples and exact Euler identities, but
global-core correction supersedes it as a payment construction.  In particular,
component-private roots and merger slots below are bookkeeping occurrences, not
independent ports, components, or branch-owned resources. -/

/-- Legacy carrier of the minimal ancestor hull generated by the selected inward
collision leaves.  Unselected natural cotree leaves and their private branches
are absent from this subtype. -/
abbrev FullPrunedComponentCotreeDualHullCarrier
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment).AncestorHull
    (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment)

/-- Minimal componentwise cotree-dual ancestor hull of all selected starts. -/
noncomputable def fullPrunedComponentCotreeDualHullForest
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    ParentForest (FullPrunedComponentCotreeDualHullCarrier
      axis hn2 hn3 hT assignment) :=
  (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment).ancestorHullForest
    (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment)

/-- Physical vertices of the occurrence-split hull retain every occurrence,
including private selected-start occurrences.  Declaring private starts to be
ghosts would be unsound: distinct starts can select the same omitted edge and
therefore can be siblings. -/
def FullPrunedComponentCotreeDualHullCarrier.IsPhysical
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root} :
    FullPrunedComponentCotreeDualHullCarrier axis hn2 hn3 hT assignment → Prop
  | _ => True

noncomputable instance fullPrunedComponentCotreeDualHullCarrierIsPhysicalDecidablePred
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root} :
    DecidablePred (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
      (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT)
      (assignment := assignment)) := by
  intro _
  exact Classical.propDecidable _

/-- There are no ghost children in the occurrence-split hull. -/
theorem fullPrunedComponentCotreeDualHull_nonphysicalChildren_card_le_one
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (v : FullPrunedComponentCotreeDualHullCarrier axis hn2 hn3 hT assignment) :
    ((fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
      |>.nonphysicalChildren
        (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
          (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT)
          (assignment := assignment)) v).card ≤ 1 := by
  classical
  simp [ParentForest.nonphysicalChildren,
    FullPrunedComponentCotreeDualHullCarrier.IsPhysical]

/-- The hull has exactly the inward collisions as leaves, not merely an
embedding of inward collisions among ambient cotree leaves. -/
noncomputable def fullPrunedComponentCotreeDualHullLeafEquiv
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    FullPrunedInwardCollision axis hn2 hn3 hT ≃
      ↥((fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).leaves) :=
  (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment).ancestorHullLeafEquiv
    (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment)

/-- Exact Euler ledger for the selected component cotree-dual hull. -/
theorem fullPrunedComponentCotreeDualHull_card_starts_eq
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) =
      (fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).roots.card +
        (fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).branchExcess :=
  ParentForest.card_start_eq_card_ancestorHull_roots_add_branchExcess
    (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment)
    (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment)

/-- Component-indexed private boundary roots. Unlike physical ports, these
retain both the raw component and the selected transition occurrence. -/
abbrev FullPrunedComponentPrivateBoundaryRoot
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  Σ component : ContactRawComponent (T := T),
    BoundaryTransitionOccurrence
      (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment
        (component := component))

/-- A private boundary root determines its supported outer cotree port. -/
def fullPrunedComponentPrivateBoundaryRootPort
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (boundary : FullPrunedComponentPrivateBoundaryRoot
      axis hn2 hn3 hT assignment) : GridCotreeOuterPort T :=
  BoundaryTransitionOccurrence.outerPort
    (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
    hn2 hn2 boundary.2

/-- Legacy component-split artifact: a full-cotree boundary occurrence has a
continuation copy in every raw-component fiber.  These copies must not be paid
as distinct roots; the active global core contains one physical occurrence. -/
def fullCotreeBoundaryContinuationRoot
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    (ContactRawComponent (T := T) ×
      BoundaryTransitionOccurrence
        (fun edge : LabelledCotreeTransition T => edge)) ↪
      FullPrunedComponentPrivateBoundaryRoot axis hn2 hn3 hT assignment where
  toFun source :=
    ⟨source.1, ⟨Sum.inr source.2.1, by
      simpa only [fullPrunedComponentCotreeDualEdgeTransition] using source.2.2⟩⟩
  inj' := by
    rintro ⟨component₁, boundary₁⟩ ⟨component₂, boundary₂⟩ hab
    obtain ⟨hcomponent, hboundaryOccurrence⟩ := Sigma.mk.inj_iff.mp hab
    change component₁ = component₂ at hcomponent
    subst component₂
    have hoccurrence :
        (Sum.inr boundary₁.1 : FullPrunedComponentCotreeDualEdgeOccurrence
          axis hn2 hn3 hT assignment component₁) = Sum.inr boundary₂.1 :=
      congrArg Subtype.val (eq_of_heq hboundaryOccurrence)
    have hboundary : boundary₁ = boundary₂ := by
      apply Subtype.ext
      exact Sum.inr.inj hoccurrence
    exact congrArg (Prod.mk component₁) hboundary

@[simp] theorem fullCotreeBoundaryContinuationRoot_port
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : ContactRawComponent (T := T) ×
      BoundaryTransitionOccurrence
        (fun edge : LabelledCotreeTransition T => edge)) :
    fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment
        (fullCotreeBoundaryContinuationRoot axis hn2 hn3 hT assignment source) =
      BoundaryTransitionOccurrence.outerPort
        (fun edge : LabelledCotreeTransition T => edge) hn2 hn2 source.2 := by
  rfl

/-- Exact multiplicity of a physical port in the component-private root
carrier, including both continuation and component-gap occurrences. -/
def fullPrunedComponentPrivateBoundaryRootMultiplicity
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (port : GridCotreeOuterPort T) : Nat :=
  Fintype.card {boundary : FullPrunedComponentPrivateBoundaryRoot
      axis hn2 hn3 hT assignment //
    fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment
      boundary = port}

/-- Every full-cotree boundary occurrence contributes exactly one labelled
continuation root in each component fiber.  Additional gap occurrences can only
increase this physical-port multiplicity. -/
theorem card_components_le_privateBoundaryRootMultiplicity
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (boundary : BoundaryTransitionOccurrence
      (fun edge : LabelledCotreeTransition T => edge)) :
    Fintype.card (ContactRawComponent (T := T)) ≤
      fullPrunedComponentPrivateBoundaryRootMultiplicity
        axis hn2 hn3 hT assignment
        (BoundaryTransitionOccurrence.outerPort
          (fun edge : LabelledCotreeTransition T => edge) hn2 hn2 boundary) := by
  let copies : ContactRawComponent (T := T) ↪
      {privateRoot : FullPrunedComponentPrivateBoundaryRoot
          axis hn2 hn3 hT assignment //
        fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment
            privateRoot =
          BoundaryTransitionOccurrence.outerPort
            (fun edge : LabelledCotreeTransition T => edge) hn2 hn2 boundary} :=
    { toFun := fun component =>
        ⟨fullCotreeBoundaryContinuationRoot axis hn2 hn3 hT assignment
          ⟨component, boundary⟩, by simp⟩
      inj' := fun a b hab => by
        have := (fullCotreeBoundaryContinuationRoot axis hn2 hn3 hT assignment).injective
          (congrArg Subtype.val hab)
        exact congrArg Prod.fst this }
  exact Fintype.card_le_of_injective copies copies.injective

/-- Distinct component fibers already refute pointwise root-port injectivity:
the same geometric continuation boundary occurrence maps to the same physical
`GridCotreeOuterPort` in both fibers. -/
theorem fullPrunedComponentPrivateBoundaryRootPort_not_injective_of_components
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    {component₁ component₂ : ContactRawComponent (T := T)}
    (hne : component₁ ≠ component₂)
    (boundary : BoundaryTransitionOccurrence
      (fun edge : LabelledCotreeTransition T => edge)) :
    ¬Function.Injective
      (fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment) := by
  intro hinjective
  let source₁ := (component₁, boundary)
  let source₂ := (component₂, boundary)
  have hport :
      fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment
          (fullCotreeBoundaryContinuationRoot axis hn2 hn3 hT assignment source₁) =
        fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment
          (fullCotreeBoundaryContinuationRoot axis hn2 hn3 hT assignment source₂) := by
    simp [source₁, source₂]
  have heq := hinjective hport
  exact hne (congrArg Sigma.fst heq)

/-- The precise condition under which component-indexed private boundary roots
inject into physical ports. It includes possible collisions across components;
no connectivity hypothesis implies it. -/
def FullPrunedComponentPortChoiceInjective
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) : Prop :=
  Function.Injective
    (fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment)

/-- Public short name for the exact component-indexed root-port condition. -/
abbrev PortChoiceInjective
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  FullPrunedComponentPortChoiceInjective axis hn2 hn3 hT assignment

theorem fullPrunedComponentPrivateBoundaryRootPort_injective_iff
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    Function.Injective
        (fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment) ↔
      FullPrunedComponentPortChoiceInjective axis hn2 hn3 hT assignment :=
  Iff.rfl

/-- Exact componentwise root classification. The second alternative is kept
explicit: bounded or occurrence vertices in components not reaching a private
boundary are roots, but are not mapped to `GridCotreeOuterPort`. -/
theorem fullPrunedComponentCotreeDual_mem_roots_iff
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (x : FullPrunedComponentCotreeDualCarrier axis hn2 hn3 hT assignment) :
    x ∈ (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment).roots ↔
      (∃ b : BoundaryTransitionOccurrence
          (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment
            (component := x.1)),
        x.2 = .inr (.inr (.inr b))) ∨
      (∃ y : SplitOccurrenceCotreeDualCore
          (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment
            (component := x.1)),
        x.2 = .inr y ∧
          ¬(SplitOccurrenceCotreeDualCore.routingGraph
              (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
              |>.Reachable)
            (.inl y)
              (SplitOccurrenceCotreeDualCore.hub
                (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment))) := by
  classical
  simpa only [ParentForest.roots, Finset.mem_filter, Finset.mem_univ, true_and,
    fullPrunedComponentCotreeDualForest, Option.map_eq_none_iff] using
      (SplitOccurrenceLabelledCotreeDualCarrier.mem_roots_iff
        (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
        (fullPrunedComponentSelectedEdgeOccurrence
          axis hn2 hn3 hT assignment) x.2)

/-- Roots of core components that do not reach any private boundary occurrence.
No function from this explicit type to physical ports is defined. -/
abbrev FullPrunedComponentUnreachableRoot
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  Σ component : ContactRawComponent (T := T),
    {y : SplitOccurrenceCotreeDualCore
        (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment
          (component := component)) //
      ¬(SplitOccurrenceCotreeDualCore.routingGraph
          (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment)).Reachable
        (.inl y)
        (SplitOccurrenceCotreeDualCore.hub
          (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment))}

/-- Connectivity of every component fiber in the expanded component forest. -/
def FullPrunedComponentCotreeDualBoundaryConnectivity
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) : Prop :=
  ∀ (component : ContactRawComponent (T := T))
    (y : SplitOccurrenceCotreeDualCore
      (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment
        (component := component))),
    (SplitOccurrenceCotreeDualCore.routingGraph
      (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment)).Reachable
      (.inl y)
      (SplitOccurrenceCotreeDualCore.hub
        (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment))

/-- Full tree-cotree connectivity instantiates every component fiber because
the right summand contains an identity-labelled continuation occurrence for
every actual cotree edge. -/
theorem fullPrunedComponentCotreeDualBoundaryConnectivity_of_fullCotree
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (hfull : SplitOccurrenceCotreeDualCore.GridSpanningTreeCotreeDualBoundaryConnectivity
      (T := T) hT) :
    FullPrunedComponentCotreeDualBoundaryConnectivity
      axis hn2 hn3 hT assignment := by
  intro component
  apply SplitOccurrenceCotreeDualCore.reachesSplitOuterBoundary_of_fullCotree
    (transition := fullPrunedComponentCotreeDualEdgeTransition
      axis hn2 hn3 hT assignment) hfull Sum.inr
  · intro edge
    rfl
  · intro occurrence
    cases occurrence with
    | inr edge =>
        change (SplitOccurrenceCotreeDualCore.routingGraph
          (fullPrunedComponentCotreeDualEdgeTransition
            axis hn2 hn3 hT assignment)).Reachable
          (.inl (.inl (.inr edge))) (.inl (.inl (.inr edge)))
        exact SimpleGraph.Reachable.refl _
    | inl gap =>
        apply SplitOccurrenceCotreeDualCore.occurrences_reachable_of_transition_eq
          (transition := fullPrunedComponentCotreeDualEdgeTransition
            axis hn2 hn3 hT assignment) hn2 hn2
        rfl

/-- Square-grid cotree-dual connectivity applies in every component fiber. -/
theorem fullPrunedComponentCotreeDualBoundaryConnectivity
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    FullPrunedComponentCotreeDualBoundaryConnectivity
      axis hn2 hn3 hT assignment :=
  fullPrunedComponentCotreeDualBoundaryConnectivity_of_fullCotree
    axis hn2 hn3 hT assignment
      (SplitOccurrenceCotreeDualCore.gridSpanningTreeCotreeDualBoundaryConnectivity_square
        hn3 hT)

/-- Bounded unreachable roots disappear: every root is an actual private
split-boundary occurrence. -/
theorem fullPrunedComponentCotreeDual_mem_roots_iff_boundary
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (x : FullPrunedComponentCotreeDualCarrier axis hn2 hn3 hT assignment) :
    x ∈ (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment).roots ↔
      ∃ b : BoundaryTransitionOccurrence
        (fullPrunedComponentCotreeDualEdgeTransition axis hn2 hn3 hT assignment
          (component := x.1)),
        x.2 = .inr (.inr (.inr b)) := by
  rw [fullPrunedComponentCotreeDual_mem_roots_iff
    axis hn2 hn3 hT assignment x]
  simp [fullPrunedComponentCotreeDualBoundaryConnectivity
    axis hn2 hn3 hT assignment x.1]

/-- Canonical forest roots are exactly component-indexed private boundary
occurrences. -/
noncomputable def fullPrunedComponentCotreeDualRootBoundary
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (x : ↥((fullPrunedComponentCotreeDualForest
      axis hn2 hn3 hT assignment).roots)) :
    FullPrunedComponentPrivateBoundaryRoot axis hn2 hn3 hT assignment :=
  ⟨x.1.1, Classical.choose
    ((fullPrunedComponentCotreeDual_mem_roots_iff_boundary
      axis hn2 hn3 hT assignment x.1).mp x.2)⟩

theorem fullPrunedComponentCotreeDualRootBoundary_spec
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (x : ↥((fullPrunedComponentCotreeDualForest
      axis hn2 hn3 hT assignment).roots)) :
    x.1.2 = .inr (.inr (.inr
      (fullPrunedComponentCotreeDualRootBoundary
        axis hn2 hn3 hT assignment x).2)) :=
  Classical.choose_spec
    ((fullPrunedComponentCotreeDual_mem_roots_iff_boundary
      axis hn2 hn3 hT assignment x.1).mp x.2)

noncomputable def fullPrunedComponentCotreeDualRootEquiv
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    ↥((fullPrunedComponentCotreeDualForest
        axis hn2 hn3 hT assignment).roots) ≃
      FullPrunedComponentPrivateBoundaryRoot axis hn2 hn3 hT assignment := by
  classical
  refine
    { toFun := fullPrunedComponentCotreeDualRootBoundary
        axis hn2 hn3 hT assignment
      invFun := fun boundary =>
        ⟨⟨boundary.1, .inr (.inr (.inr boundary.2))⟩,
          (fullPrunedComponentCotreeDual_mem_roots_iff_boundary
            axis hn2 hn3 hT assignment _).mpr ⟨boundary.2, rfl⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq
      (fullPrunedComponentCotreeDualRootBoundary_spec
        axis hn2 hn3 hT assignment x).symm)
  · intro boundary
    have hspec := fullPrunedComponentCotreeDualRootBoundary_spec
      axis hn2 hn3 hT assignment
        ⟨⟨boundary.1, .inr (.inr (.inr boundary.2))⟩,
          (fullPrunedComponentCotreeDual_mem_roots_iff_boundary
            axis hn2 hn3 hT assignment _).mpr ⟨boundary.2, rfl⟩⟩
    exact Sigma.ext rfl (heq_of_eq (by
      exact Sum.inr.inj (Sum.inr.inj (Sum.inr.inj hspec.symm))))

/-- The outer port of a canonical forest root, derived from its unique private
boundary occurrence. -/
noncomputable def fullPrunedComponentCotreeDualRootPort
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    ↥((fullPrunedComponentCotreeDualForest
        axis hn2 hn3 hT assignment).roots) → GridCotreeOuterPort T :=
  fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment ∘
    fullPrunedComponentCotreeDualRootEquiv axis hn2 hn3 hT assignment

theorem fullPrunedComponentCotreeDualRootPort_injective_iff
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    Function.Injective
        (fullPrunedComponentCotreeDualRootPort axis hn2 hn3 hT assignment) ↔
      PortChoiceInjective axis hn2 hn3 hT assignment := by
  change Function.Injective
      (fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment ∘
        fullPrunedComponentCotreeDualRootEquiv axis hn2 hn3 hT assignment) ↔
    Function.Injective
      (fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment)
  constructor
  · intro h a b hab
    let e := fullPrunedComponentCotreeDualRootEquiv axis hn2 hn3 hT assignment
    have hpre :
        (fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment ∘ e)
            (e.symm a) =
          (fullPrunedComponentPrivateBoundaryRootPort axis hn2 hn3 hT assignment ∘ e)
            (e.symm b) := by
      simpa using hab
    have heq := h hpre
    simpa using congrArg e heq
  · intro h
    exact h.comp
      (fullPrunedComponentCotreeDualRootEquiv
        axis hn2 hn3 hT assignment).injective

/-- A root retained by the minimal hull is canonically an ambient cotree-dual
root. -/
noncomputable def fullPrunedComponentCotreeDualHullRootEmbedding
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    ↥((fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).roots) ↪
      ↥((fullPrunedComponentCotreeDualForest
        axis hn2 hn3 hT assignment).roots) where
  toFun x := ⟨x.1.1,
    ((fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment)
      |>.mem_ancestorHullForest_roots_iff
      (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment)
      x.1).mp x.2⟩
  inj' := by
    intro a b hab
    have hval : a.1.1 = b.1.1 := congrArg
      (fun x : ↥((fullPrunedComponentCotreeDualForest
        axis hn2 hn3 hT assignment).roots) => x.1) hab
    exact Subtype.ext (Subtype.ext hval)

/-- Root port classification restricted to exactly the roots reached by a
selected start chain. -/
noncomputable def fullPrunedComponentCotreeDualHullRootPort
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    ↥((fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).roots) → GridCotreeOuterPort T :=
  fullPrunedComponentCotreeDualRootPort axis hn2 hn3 hT assignment ∘
    fullPrunedComponentCotreeDualHullRootEmbedding axis hn2 hn3 hT assignment

/-- The finite, component-resolved part of the boundary-gap ledger.  This
contains no assertion that a cotree root exits the grid or that a dual merger
owns a primal resource. -/
structure ComponentResolvedBoundaryGapForestRealization
    (root : GridVertex n n)
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) where
  Carrier : Type
  [carrierFintype : Fintype Carrier]
  [carrierDecidableEq : DecidableEq Carrier]
  forest : ParentForest Carrier
  carrierComponent : Carrier → ContactRawComponent (T := T)
  parent_component : ∀ {a b}, forest.parent a = some b →
    carrierComponent a = carrierComponent b
  startLeaf : FullPrunedInwardCollision axis hn2 hn3 hT ↪
    ↥forest.leaves
  start_component : ∀ collision,
    carrierComponent (startLeaf collision).1 = assignment.component collision

noncomputable instance componentResolvedBoundaryGapForestRealizationCarrierFintype
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment) : Fintype realization.Carrier :=
  realization.carrierFintype

noncomputable instance componentResolvedBoundaryGapForestRealizationCarrierDecidableEq
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment) : DecidableEq realization.Carrier :=
  realization.carrierDecidableEq

/-- Canonical component-resolved realization built from the selected omitted
occurrence of every assignment. -/
noncomputable def fullPrunedComponentCotreeDualRealization
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment where
  Carrier := FullPrunedComponentCotreeDualHullCarrier axis hn2 hn3 hT assignment
  forest := fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment
  carrierComponent := fun x => x.1.1
  parent_component := by
    intro a b hparent
    have hambient := (ParentForest.ancestorHullParent_eq_some
      (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment)
      (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment) a b).1
        hparent
    simp only [fullPrunedComponentCotreeDualForest,
      Option.map_eq_some_iff] at hambient
    obtain ⟨b', _, hcomponent⟩ := hambient
    exact (Sigma.mk.inj_iff.mp hcomponent).1
  startLeaf :=
    (fullPrunedComponentCotreeDualHullLeafEquiv
      axis hn2 hn3 hT assignment).toEmbedding
  start_component := by
    intro collision
    change (((fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment).ancestorHullStart
      (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment) collision).1).1 = _
    rfl

namespace ComponentResolvedBoundaryGapForestRealization

variable {root : GridVertex n n}
  {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}

/-- All inward starts below a realized forest vertex. -/
noncomputable def descendantSources
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment) (vertex : realization.Carrier) :
    Finset (FullPrunedInwardCollision axis hn2 hn3 hT) :=
  Finset.univ.filter fun collision => Relation.ReflTransGen
    realization.forest.ParentStep (realization.startLeaf collision).1 vertex

/-- Set of raw source-component labels below a realized forest vertex. -/
noncomputable def descendantComponents
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment) (vertex : realization.Carrier) :
    Finset (ContactRawComponent (T := T)) :=
  (realization.descendantSources axis hn2 hn3 hT vertex).image assignment.component

/-- Component labels retained by an active branch slot. -/
noncomputable def mergerSlotDescendantComponents
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment) (slot : realization.forest.MergerSlot) :
    Finset (ContactRawComponent (T := T)) :=
  realization.descendantComponents axis hn2 hn3 hT slot.1

/-- Generic Euler accounting uses only the realized finite forest and its start
leaves; no geometric exit or owner is assumed. -/
theorem card_starts_le_card_roots_add_branchExcess
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment) :
    Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) ≤
      realization.forest.roots.card + realization.forest.branchExcess := by
  let := realization.carrierFintype
  let := realization.carrierDecidableEq
  calc
    Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) ≤
        Fintype.card ↥realization.forest.leaves :=
      Fintype.card_le_of_injective realization.startLeaf realization.startLeaf.injective
    _ = realization.forest.leaves.card := Fintype.card_coe _
    _ = realization.forest.roots.card + realization.forest.branchExcess :=
      realization.forest.card_leaves_eq_card_roots_add_branchExcess

end ComponentResolvedBoundaryGapForestRealization

/-- Roots whose chosen split port is already reserved by a canonical
first-stop exit. -/
abbrev ReservedBoundaryGapRoot {Carrier : Type*} [Fintype Carrier]
    [DecidableEq Carrier] (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T) :=
  {a : ↥forest.roots // rootPort a ∈ Set.range (exitEmbedding axis hn2 hT)}

/-- Roots whose chosen split port is not reserved by a canonical first-stop
exit.  This is the complementary root class, not an assumption that every root
has a fresh pointwise exit. -/
abbrev UnreservedBoundaryGapRoot {Carrier : Type*} [Fintype Carrier]
    [DecidableEq Carrier] (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T) :=
  {a : ↥forest.roots // rootPort a ∉ Set.range (exitEmbedding axis hn2 hT)}

/-- Internal-edge residual resources after canonical terminal-token edges have
been reserved. -/
abbrev BoundaryGapResidualInternalResource :=
  {e : ↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T))) //
    e ∉ Set.range (internalTreeEdgeTokenEmbedding
      (supportFinset (gridGraph n n \ T))
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT))}

/-- Free-component residual resources after canonical carrier representatives
have been reserved. -/
abbrev BoundaryGapResidualComponentResource :=
  {k : FreeFullVertexComponentResource (T := T) //
    k ∉ Set.range (carrierQuotientEmbedding
      (FullPrunedTokenCarrier axis hn2 hn3 hT))}

/-- Legacy conditional embedding, not an active payment theorem.  In the
component-split model duplicate root-port slots map to raw components provided
two facts survive pruning: active roots have
distinct component labels, and the component chosen for the representative of
each used port is exactly one of the already reserved carrier-quotient
representatives.  The latter equality prevents making an incompatible second
choice of one representative per port. -/
noncomputable def componentResolvedRootPortDebtEmbedding
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T)
    (rootComponent : ↥forest.roots → FreeFullVertexComponentResource (T := T))
    (hcomponent : Function.Injective rootComponent)
    (hreserved : Set.range (fun q : CarrierQuotient rootPort =>
        rootComponent (carrierRepresentative rootPort q)) =
      Set.range (carrierQuotientEmbedding
        (FullPrunedTokenCarrier axis hn2 hn3 hT))) :
    forest.RootPortDebtSlot rootPort ↪
      BoundaryGapResidualComponentResource axis hn2 hn3 hT :=
  (rootPortDebtSlotComponentEmbedding forest rootPort rootComponent
      hcomponent).trans
    { toFun := fun component => ⟨component.1, by
        intro hreservedComponent
        apply component.2
        have hrange := congrArg (fun s => component.1 ∈ s) hreserved
        exact hrange.mpr hreservedComponent⟩
      inj' := fun a b hab => by
        have hval : a.1 = b.1 := congrArg
          (fun x : BoundaryGapResidualComponentResource axis hn2 hn3 hT => x.1) hab
        exact Subtype.ext hval }

/-- A used active-root port for which the prescribed already-reserved
component has no root over that port.  This is the exact obstruction to making
the port representative agree with the existing carrier reservation. -/
abbrev ComponentResolvedRootPortRepresentativeException
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T)
    (rootComponent : ↥forest.roots → FreeFullVertexComponentResource (T := T))
    (reservedComponent : CarrierQuotient rootPort →
      FreeFullVertexComponentResource (T := T)) :=
  RootPortRepresentativeException forest rootPort rootComponent reservedComponent

/-- Active canonical-hull roots at the exceptional port.  These are the sound
provenance candidates when the ranked reserved component itself has no active
root in that port fiber. -/
abbrev ComponentResolvedRootPortRepresentativeProvenance
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T)
    (rootComponent : ↥forest.roots → FreeFullVertexComponentResource (T := T))
    (reservedComponent : CarrierQuotient rootPort →
      FreeFullVertexComponentResource (T := T))
    (exception : ComponentResolvedRootPortRepresentativeException forest
      rootPort rootComponent reservedComponent) :=
  RootPortRepresentativeProvenance forest rootPort rootComponent
    reservedComponent exception

/-- Residual-resource neighborhood of an exceptional prescribed component,
obtained by taking the union of the genuine candidate neighborhoods of all
active roots over that port. -/
noncomputable def componentResolvedRootPortRepresentativeExceptionNeighborhood
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T)
    (rootComponent : ↥forest.roots → FreeFullVertexComponentResource (T := T))
    (reservedComponent : CarrierQuotient rootPort →
      FreeFullVertexComponentResource (T := T))
    (provenanceCandidates : ↥forest.roots →
      Finset (FullPrunedResidualResource axis hn2 hn3 hT)) :=
  rootPortRepresentativeExceptionNeighborhood forest rootPort rootComponent
    reservedComponent provenanceCandidates

/-- Sound classification of the failed representative shortcut.  Exceptions
are not discarded or paid by their absent prescribed component; they are
routed jointly through active-root provenance candidates. -/
def ComponentResolvedRootPortRepresentativeExceptionHall
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T)
    (rootComponent : ↥forest.roots → FreeFullVertexComponentResource (T := T))
    (reservedComponent : CarrierQuotient rootPort →
      FreeFullVertexComponentResource (T := T))
    (provenanceCandidates : ↥forest.roots →
      Finset (FullPrunedResidualResource axis hn2 hn3 hT)) : Prop :=
  LocalizedHall
    (componentResolvedRootPortRepresentativeExceptionNeighborhood
      axis hn2 hn3 hT forest rootPort rootComponent reservedComponent
      provenanceCandidates)

theorem componentResolvedRootPortRepresentativeExceptionHall_iff_routing
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T)
    (rootComponent : ↥forest.roots → FreeFullVertexComponentResource (T := T))
    (reservedComponent : CarrierQuotient rootPort →
      FreeFullVertexComponentResource (T := T))
    (provenanceCandidates : ↥forest.roots →
      Finset (FullPrunedResidualResource axis hn2 hn3 hT)) :
    ComponentResolvedRootPortRepresentativeExceptionHall axis hn2 hn3 hT
        forest rootPort rootComponent reservedComponent provenanceCandidates ↔
      Nonempty (LocalizedRouting
        (componentResolvedRootPortRepresentativeExceptionNeighborhood
          axis hn2 hn3 hT forest rootPort rootComponent reservedComponent
          provenanceCandidates)) :=
  rootPortRepresentativeExceptionHall_iff_nonempty_routing forest rootPort
    rootComponent reservedComponent provenanceCandidates

/-- Sound representative-per-port quotient compatible with the existing full
pruned carrier quotient.  For each used port, `hcoverage` removes a root whose
component is the prescribed reserved component.  Thus all remaining duplicate
roots land in the genuine residual component pool.  `hrange` says these
prescribed components are exactly, not additionally to, the existing terminal
carrier reservations. -/
noncomputable def componentResolvedRootPortDebtResidualEmbedding
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T)
    (rootComponent : ↥forest.roots → FreeFullVertexComponentResource (T := T))
    (hcomponent : Function.Injective rootComponent)
    (reservedComponent : CarrierQuotient rootPort →
      FreeFullVertexComponentResource (T := T))
    (hcoverage : ∀ q, ∃ r : ↥forest.roots,
      carrierQuotientMk rootPort r = q ∧
        rootComponent r = reservedComponent q)
    (hrange : Set.range reservedComponent =
      Set.range (carrierQuotientEmbedding
        (FullPrunedTokenCarrier axis hn2 hn3 hT))) :
    forest.RootPortDebtSlot rootPort ↪
      BoundaryGapResidualComponentResource axis hn2 hn3 hT :=
  (rootPortDebtSlotResidualComponentEmbedding forest rootPort rootComponent
      hcomponent reservedComponent hcoverage).trans
    { toFun := fun component => ⟨component.1, by
        intro hreserved
        apply component.2
        have hmem := congrArg (fun s => component.1 ∈ s) hrange
        exact hmem.mpr hreserved⟩
      inj' := fun a b hab => by
        have hval : a.1 = b.1 := congrArg
          (fun x : BoundaryGapResidualComponentResource axis hn2 hn3 hT => x.1) hab
        exact Subtype.ext hval }

/-- Concrete raw-component labels on the active roots of a component-resolved
forest realization. -/
def ComponentResolvedBoundaryGapForestRealization.rootComponent
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment) :
    ↥realization.forest.roots → FreeFullVertexComponentResource (T := T) :=
  fun activeRoot => realization.carrierComponent activeRoot.1

/-- Legacy component-split form of duplicate-slot routing, conditional on the
stated injectivity and reservation hypotheses.  Global-core correction does
not generate or pay these duplicate slots componentwise. -/
noncomputable def ComponentResolvedBoundaryGapForestRealization.rootPortDebtEmbedding
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment)
    (rootPort : ↥realization.forest.roots → GridCotreeOuterPort T)
    (hcomponent : Function.Injective
      (realization.rootComponent (axis := axis) (hn2 := hn2) (hn3 := hn3)
        (hT := hT)))
    (hreserved : Set.range (fun q : CarrierQuotient rootPort =>
        realization.rootComponent (axis := axis) (hn2 := hn2) (hn3 := hn3)
          (hT := hT) (carrierRepresentative rootPort q)) =
      Set.range (carrierQuotientEmbedding
        (FullPrunedTokenCarrier axis hn2 hn3 hT))) :
    realization.forest.RootPortDebtSlot rootPort ↪
      BoundaryGapResidualComponentResource axis hn2 hn3 hT :=
  componentResolvedRootPortDebtEmbedding axis hn2 hn3 hT realization.forest
    rootPort
    (realization.rootComponent (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
    hcomponent hreserved

/-- Component-specific sound quotient using a prescribed existing reservation
per active-root port.  Its only additional existence requirement is exactly
that every port fiber contains a root with that reserved component. -/
noncomputable def ComponentResolvedBoundaryGapForestRealization.rootPortDebtResidualEmbedding
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment)
    (rootPort : ↥realization.forest.roots → GridCotreeOuterPort T)
    (hcomponent : Function.Injective
      (realization.rootComponent (axis := axis) (hn2 := hn2) (hn3 := hn3)
        (hT := hT)))
    (reservedComponent : CarrierQuotient rootPort →
      FreeFullVertexComponentResource (T := T))
    (hcoverage : ∀ q, ∃ r : ↥realization.forest.roots,
      carrierQuotientMk rootPort r = q ∧
        realization.rootComponent (axis := axis) (hn2 := hn2) (hn3 := hn3)
          (hT := hT) r = reservedComponent q)
    (hrange : Set.range reservedComponent =
      Set.range (carrierQuotientEmbedding
        (FullPrunedTokenCarrier axis hn2 hn3 hT))) :
    realization.forest.RootPortDebtSlot rootPort ↪
      BoundaryGapResidualComponentResource axis hn2 hn3 hT :=
  componentResolvedRootPortDebtResidualEmbedding axis hn2 hn3 hT
    realization.forest rootPort
    (realization.rootComponent (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
    hcomponent reservedComponent hcoverage hrange

/-- The genuine residual physical pool `U ⊕ J ⊕ K`.  Outer collisions are
source obligations and do not occur in this target. -/
abbrev BoundaryGapResidualPhysicalResource :=
  UnreservedCanonicalBoundaryPort axis hn2 hT ⊕
    (BoundaryGapResidualInternalResource axis hn2 hn3 hT ⊕
      BoundaryGapResidualComponentResource axis hn2 hn3 hT)

/-- Reservation-certified first-separator alternatives.  The three constructors
record respectively a boundary-cell exit, an internal separating edge, or a
free separating component.  Their subtype proofs put every candidate outside
the corresponding canonical reservation range. -/
abbrev CanonicalHullFirstSeparatingCandidate :=
  FirstSeparatingResource
    (UnreservedCanonicalBoundaryPort axis hn2 hT)
    (BoundaryGapResidualInternalResource axis hn2 hn3 hT)
    (BoundaryGapResidualComponentResource axis hn2 hn3 hT)

/-- Forget the geometric separator class while preserving its reservation
proof.  This is an equivalence because the physical residual pool has the same
three summands. -/
def canonicalHullFirstSeparatingCandidateEquiv :
    CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT ≃
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT where
  toFun
    | .inl cell => .inl cell
    | .inr (.inl edge) => .inr (.inl edge)
    | .inr (.inr component) => .inr (.inr component)
  invFun
    | .inl port => .inl port
    | .inr (.inl edge) => .inr (.inl edge)
    | .inr (.inr component) => .inr (.inr component)
  left_inv x := by rcases x with x | x <;> rcases x with x | x <;> rfl
  right_inv x := by rcases x with x | x <;> rcases x with x | x <;> rfl

/-! #### Equality of actual merger-slot separators -/

/-- The physical child selected for one branch-excess slot of the minimal
component-split hull. -/
noncomputable def canonicalHullMergerSlotChild
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot ↪
      FullPrunedComponentCotreeDualHullCarrier axis hn2 hn3 hT assignment :=
  ((fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
    |>.mergerSlotPhysicalChildEmbedding
      (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
      (fullPrunedComponentCotreeDualHull_nonphysicalChildren_card_le_one
        axis hn2 hn3 hT assignment)).trans
    { toFun := Subtype.val
      inj' := Subtype.val_injective }

/-- Raw component label retained by every component-split hull vertex. -/
def canonicalHullVertexComponent
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (vertex : FullPrunedComponentCotreeDualHullCarrier
      axis hn2 hn3 hT assignment) : ContactRawComponent (T := T) :=
  vertex.val.fst

/-- Raw component label retained by the selected child of a merger slot. -/
noncomputable def canonicalHullMergerSlotComponent
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    ContactRawComponent (T := T) :=
  canonicalHullVertexComponent axis hn2 hn3 hT
    (canonicalHullMergerSlotChild axis hn2 hn3 hT assignment slot)

/-- Selected inward sources below a canonical shared-hull vertex.  This is the
source API for the hull and does not use the sigma component copied onto the
carrier vertex. -/
noncomputable def canonicalHullDescendantSources
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (vertex : FullPrunedComponentCotreeDualHullCarrier
      axis hn2 hn3 hT assignment) :
    Finset (FullPrunedInwardCollision axis hn2 hn3 hT) :=
  (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment)
    |>.ancestorHullDescendantSources
      (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment) vertex

/-- Raw component labels of all selected inward sources below a canonical hull
vertex.  Distinct labels are retained and repeated labels are represented once. -/
noncomputable def canonicalHullDescendantComponents
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (vertex : FullPrunedComponentCotreeDualHullCarrier
      axis hn2 hn3 hT assignment) : Finset (ContactRawComponent (T := T)) :=
  (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment)
    |>.ancestorHullDescendantLabels
      (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment)
      assignment.component vertex

/-- Active branch slots retain the set of source-component labels descending
from their branch vertex, rather than one carrier component copied by `Sigma`. -/
noncomputable def canonicalHullMergerSlotDescendantComponents
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    Finset (ContactRawComponent (T := T)) :=
  (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment)
    |>.ancestorHullMergerSlotDescendantLabels
      (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment)
      assignment.component slot

theorem canonicalHullMergerSlotDescendantComponents_nonempty
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    (canonicalHullMergerSlotDescendantComponents
      axis hn2 hn3 hT assignment slot).Nonempty :=
  (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment)
    |>.ancestorHullMergerSlotDescendantLabels_nonempty
      (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment)
      assignment.component slot

/-- The component-split parent map never changes the sigma component label. -/
theorem fullPrunedComponentCotreeDualHull_parentStep_component_eq
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    {x y : FullPrunedComponentCotreeDualHullCarrier axis hn2 hn3 hT assignment}
    (hxy : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).ParentStep x y) :
    canonicalHullVertexComponent axis hn2 hn3 hT x =
      canonicalHullVertexComponent axis hn2 hn3 hT y := by
  change (fullPrunedComponentCotreeDualHullForest
    axis hn2 hn3 hT assignment).parent x = some y at hxy
  have hambient := (ParentForest.ancestorHullParent_eq_some
    (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment)
    (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment) x y).1 hxy
  simp only [fullPrunedComponentCotreeDualForest, Option.map_eq_some_iff] at hambient
  obtain ⟨next, _, hcarrier⟩ := hambient
  exact (Sigma.mk.inj_iff.mp hcarrier).1

/-- Component labels are consequently preserved along every upward hull
parent chain. -/
theorem fullPrunedComponentCotreeDualHull_reached_component_eq
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    {x y : FullPrunedComponentCotreeDualHullCarrier axis hn2 hn3 hT assignment}
    (hxy : Relation.ReflTransGen
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).ParentStep x y) :
    canonicalHullVertexComponent axis hn2 hn3 hT x =
      canonicalHullVertexComponent axis hn2 hn3 hT y := by
  induction hxy with
  | refl => rfl
  | tail hreach hstep ih =>
      exact ih.trans
        (fullPrunedComponentCotreeDualHull_parentStep_component_eq
          axis hn2 hn3 hT assignment hstep)

/-- Exact unresolved collision shape after port separation, cell-side
injectivity, and component nonalternation have handled all nonnested cases.
The two slots are genuinely distinct, retain the same raw component label, and
their selected physical children are comparable in the hull parent order. -/
structure CanonicalHullSameComponentNestedException
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (a b : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) : Prop where
  slots_ne : a ≠ b
  resource_eq : firstSeparating a = firstSeparating b
  component_eq : canonicalHullMergerSlotComponent axis hn2 hn3 hT assignment a =
    canonicalHullMergerSlotComponent axis hn2 hn3 hT assignment b
  component_resource : ∃ component,
    firstSeparating a = .inr (.inr component)
  nested : Relation.ReflTransGen
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).ParentStep
      (canonicalHullMergerSlotChild axis hn2 hn3 hT assignment a)
      (canonicalHullMergerSlotChild axis hn2 hn3 hT assignment b) ∨
    Relation.ReflTransGen
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).ParentStep
      (canonicalHullMergerSlotChild axis hn2 hn3 hT assignment b)
      (canonicalHullMergerSlotChild axis hn2 hn3 hT assignment a)

/-- Occurrence-resolved merger slots for a first-separator labelling.  One
minimum-rank slot in each physical-resource fiber retains the resource; every
further occurrence is kept as an explicit duplicate slot.  In particular this
does not silently identify nested occurrences of the same component. -/
abbrev CanonicalHullResolvedFirstSeparatingSlot
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (occurrenceRank :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot → Nat) :=
  CarrierQuotient firstSeparating ⊕
    RankedCarrierCollision firstSeparating occurrenceRank

/-- Resolve every merger slot by minimum occurrence rank in its actual
first-separator fiber. -/
noncomputable def canonicalHullResolveFirstSeparatingSlot
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (occurrenceRank :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot → Nat) :
    (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot ≃
      CanonicalHullResolvedFirstSeparatingSlot
        axis hn2 hn3 hT assignment firstSeparating occurrenceRank :=
  rankedCarrierQuotientCollisionEquiv firstSeparating occurrenceRank

/-- Labels for resolved first-separator occurrences.  The left summand names
the physical representative of a separator fiber.  The right summand names a
further occurrence in that fiber; it is an obligation label, not an additional
physical resource. -/
abbrev CanonicalHullResolvedFirstSeparatingLabel
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (occurrenceRank :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot → Nat) :=
  CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT ⊕
    RankedCarrierCollision firstSeparating occurrenceRank

/-- Additional occurrence debt in a free-component first-separator fiber. -/
abbrev CanonicalHullComponentFirstSeparatingDuplicateSlot
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (occurrenceRank :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot → Nat) :=
  {duplicate : RankedCarrierCollision firstSeparating occurrenceRank //
    ∃ component, firstSeparating duplicate.1 = .inr (.inr component)}

/-- Component duplicate debt retains its original merger-slot occurrence. -/
def canonicalHullComponentFirstSeparatingDuplicateSlotEmbedding
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (occurrenceRank :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot → Nat) :
    CanonicalHullComponentFirstSeparatingDuplicateSlot
        axis hn2 hn3 hT assignment firstSeparating occurrenceRank ↪
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot where
  toFun duplicate := duplicate.1.1
  inj' := fun _ _ hab => Subtype.ext (Subtype.ext hab)

/-- Canonical injective occurrence rank on the finite merger-slot type. -/
noncomputable def canonicalHullMergerSlotOccurrenceRank
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot → Nat :=
  fun slot => (Fintype.equivFin _ slot).val

theorem canonicalHullMergerSlotOccurrenceRank_injective
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    Function.Injective (canonicalHullMergerSlotOccurrenceRank
      axis hn2 hn3 hT assignment) := by
  intro a b hab
  apply (Fintype.equivFin _).injective
  apply Fin.ext
  exact hab

/-- Label a resolved first-separator slot.  Injectivity here records occurrence
identity only; the duplicate constructor does not create residual capacity. -/
def canonicalHullResolvedFirstSeparatingLabel
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (occurrenceRank :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot → Nat) :
    CanonicalHullResolvedFirstSeparatingSlot
        axis hn2 hn3 hT assignment firstSeparating occurrenceRank →
      CanonicalHullResolvedFirstSeparatingLabel
        axis hn2 hn3 hT assignment firstSeparating occurrenceRank
  | .inl resourceClass =>
      .inl (carrierQuotientEmbedding firstSeparating resourceClass)
  | .inr duplicate => .inr duplicate

/-- Resolved occurrence labels are injective.  This theorem deliberately has
no codomain in `BoundaryGapResidualPhysicalResource`. -/
theorem canonicalHullResolvedFirstSeparatingLabel_injective
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (occurrenceRank :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot → Nat) :
    Function.Injective (canonicalHullResolvedFirstSeparatingLabel
      axis hn2 hn3 hT assignment firstSeparating occurrenceRank) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl
      ((carrierQuotientEmbedding firstSeparating).injective (Sum.inl.inj hab))
  · cases hab
  · cases hab
  · exact congrArg Sum.inr (Sum.inr.inj hab)

/-- Every resolved occurrence remains an obligation against its concrete
physical separator.  Repeated occurrences therefore have the same singleton
neighborhood; their occurrence labels are never counted as resources. -/
noncomputable def canonicalHullResolvedFirstSeparatingNeighborhood
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (occurrenceRank :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot → Nat)
    (slot : CanonicalHullResolvedFirstSeparatingSlot
      axis hn2 hn3 hT assignment firstSeparating occurrenceRank) :
    Finset (BoundaryGapResidualPhysicalResource axis hn2 hn3 hT) :=
  match slot with
  | .inl resourceClass =>
      {canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT
        (carrierQuotientEmbedding firstSeparating resourceClass)}
  | .inr duplicate =>
      {canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT
        (firstSeparating duplicate.1)}

/-- A same-component nested collision cannot disappear under occurrence
resolution.  Exactly one physical representative is retained in its separator
fiber, so at least one of the two exceptional slots is an additional ranked
duplicate.  Its rank has a strictly earlier occurrence with the same actual
separator. -/
theorem CanonicalHullSameComponentNestedException.exists_rankedDuplicate
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT}
    {a b : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot}
    (exception : CanonicalHullSameComponentNestedException
      axis hn2 hn3 hT assignment firstSeparating a b)
    (occurrenceRank :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot → Nat)
    (hrank : Function.Injective occurrenceRank) :
    ∃ duplicate : CanonicalHullComponentFirstSeparatingDuplicateSlot
        axis hn2 hn3 hT assignment firstSeparating occurrenceRank,
      (duplicate.1.1 = a ∨ duplicate.1.1 = b) ∧
        ∃ earlier,
          firstSeparating earlier = firstSeparating duplicate.1.1 ∧
            occurrenceRank earlier < occurrenceRank duplicate.1.1 := by
  obtain ⟨component, hcomponent⟩ := exception.component_resource
  let representative := rankedCarrierRepresentative firstSeparating occurrenceRank
  by_cases ha : a = representative (carrierQuotientMk firstSeparating a)
  · have hb : b ≠ representative (carrierQuotientMk firstSeparating b) := by
      intro hb
      apply exception.slots_ne
      calc
        a = representative (carrierQuotientMk firstSeparating a) := ha
        _ = representative (carrierQuotientMk firstSeparating b) := by
          congr 1
          exact Quotient.sound exception.resource_eq
        _ = b := hb.symm
    have hbcomponent : firstSeparating b = .inr (.inr component) :=
      exception.resource_eq.symm.trans hcomponent
    refine ⟨⟨⟨b, hb⟩, ⟨component, hbcomponent⟩⟩, Or.inr rfl, ?_⟩
    exact (mem_rankedCarrierCollision_iff_exists_lt
      firstSeparating occurrenceRank hrank b).mp hb
  · refine ⟨⟨⟨a, ha⟩, ⟨component, hcomponent⟩⟩, Or.inl rfl, ?_⟩
    exact (mem_rankedCarrierCollision_iff_exists_lt
      firstSeparating occurrenceRank hrank a).mp ha

/-- Canonical-rank specialization: every nested same-component exception
unconditionally contributes one additional component-separator occurrence
slot, together with an earlier equal-separator occurrence. -/
theorem CanonicalHullSameComponentNestedException.exists_duplicate
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT}
    {a b : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot}
    (exception : CanonicalHullSameComponentNestedException
      axis hn2 hn3 hT assignment firstSeparating a b) :
    ∃ duplicate : CanonicalHullComponentFirstSeparatingDuplicateSlot
        axis hn2 hn3 hT assignment firstSeparating
          (canonicalHullMergerSlotOccurrenceRank axis hn2 hn3 hT assignment),
      (duplicate.1.1 = a ∨ duplicate.1.1 = b) ∧
        ∃ earlier,
          firstSeparating earlier = firstSeparating duplicate.1.1 ∧
            canonicalHullMergerSlotOccurrenceRank axis hn2 hn3 hT assignment earlier <
              canonicalHullMergerSlotOccurrenceRank axis hn2 hn3 hT assignment
                duplicate.1.1 :=
  exception.exists_rankedDuplicate axis hn2 hn3 hT
    (canonicalHullMergerSlotOccurrenceRank axis hn2 hn3 hT assignment)
    (canonicalHullMergerSlotOccurrenceRank_injective axis hn2 hn3 hT assignment)

/-- Equality of actual first-separating resources is injective except for the
exact same-component nested case.  `hport` is the port/corner-separation input,
`hedge` is the supported-cell-side injectivity input, `hcomponent` identifies a
free resource with its component-split hull label, and `hnonalternating` is the
component-nonalternation conclusion away from nested chains. -/
theorem canonicalHull_firstSeparating_eq_slot_or_sameComponentNested
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating :
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (hport : ∀ {a b p}, firstSeparating a = .inl p →
      firstSeparating b = .inl p → a = b)
    (hedge : ∀ {a b e}, firstSeparating a = .inr (.inl e) →
      firstSeparating b = .inr (.inl e) → a = b)
    (hcomponent : ∀ {slot component},
      firstSeparating slot = .inr (.inr component) →
        canonicalHullMergerSlotComponent axis hn2 hn3 hT assignment slot =
          component.1)
    (hnonalternating : ∀ {a b},
      canonicalHullMergerSlotComponent axis hn2 hn3 hT assignment a =
        canonicalHullMergerSlotComponent axis hn2 hn3 hT assignment b →
      (¬Relation.ReflTransGen
          (fullPrunedComponentCotreeDualHullForest
            axis hn2 hn3 hT assignment).ParentStep
          (canonicalHullMergerSlotChild axis hn2 hn3 hT assignment a)
          (canonicalHullMergerSlotChild axis hn2 hn3 hT assignment b)) →
      (¬Relation.ReflTransGen
          (fullPrunedComponentCotreeDualHullForest
            axis hn2 hn3 hT assignment).ParentStep
          (canonicalHullMergerSlotChild axis hn2 hn3 hT assignment b)
          (canonicalHullMergerSlotChild axis hn2 hn3 hT assignment a)) →
      a = b)
    {a b : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot}
    (heq : firstSeparating a = firstSeparating b) :
    a = b ∨ CanonicalHullSameComponentNestedException
      axis hn2 hn3 hT assignment firstSeparating a b := by
  rcases ha : firstSeparating a with p | e | component
  · left
    exact hport ha (heq ▸ ha)
  · left
    exact hedge ha (heq ▸ ha)
  · have hb : firstSeparating b = .inr (.inr component) := heq.symm.trans ha
    have hlabel : canonicalHullMergerSlotComponent axis hn2 hn3 hT assignment a =
        canonicalHullMergerSlotComponent axis hn2 hn3 hT assignment b :=
      (hcomponent ha).trans (hcomponent hb).symm
    by_cases hab : a = b
    · exact Or.inl hab
    · right
      refine ⟨hab, heq, hlabel, ⟨component, ha⟩, ?_⟩
      by_contra hnested
      push Not at hnested
      exact hab (hnonalternating hlabel hnested.1 hnested.2)

/-- Exact local geometry still required to replace a cotree-dual hull vertex by
a reservation-certified physical separator.  The observation records the
source-labelled parent-chain position.  A bounded face also records the
unconditional supported side and its raw internal-edge/cotree-continuation
classification.  No first-owner or residual existence is inferred from it. -/
inductive CanonicalHullSeparatingObservation
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x}) : Type where
  | selectedStart
      (collision : FullPrunedInwardCollision axis hn2 hn3 hT)
      (component : FreeFullVertexComponentResource (T := T))
  | boundedCell
      (row col : Fin (n - 1))
      (raw : GridCellSupportedSideRawResource T)
  | cotreeOccurrence (transition : LabelledCotreeTransition T)
  | boundaryPort (port : GridCotreeOuterPort T)

/-- Inspect any source-labelled position of the canonical parent chain. -/
noncomputable def canonicalHullSeparatingObservationAt
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x})
    (vertex : FullPrunedComponentCotreeDualHullCarrier
      axis hn2 hn3 hT assignment) :
    CanonicalHullSeparatingObservation axis hn2 hn3 hT assignment source := by
  rcases vertex.1 with ⟨component, vertex⟩
  rcases vertex with selected | core
  · exact .selectedStart selected.1 component
  · rcases core with occurrence | face
    · exact .cotreeOccurrence
        (fullPrunedComponentCotreeDualEdgeTransition
          axis hn2 hn3 hT assignment occurrence)
    · rcases face with bounded | boundary
      · rcases bounded with ⟨face, hout⟩
        cases face with
        | out => exact False.elim (hout rfl)
        | cell row col =>
            exact .boundedCell row col
              (gridTreeCellSupportedSideRawResource T hT row col)
      · exact .boundaryPort
          (BoundaryTransitionOccurrence.outerPort
            (fullPrunedComponentCotreeDualEdgeTransition
              axis hn2 hn3 hT assignment) hn2 hn2 boundary)

/-- Inspect the concrete physical-hull constructor at the start of a separator
walk.  Bounded faces use `GridCellSupportedSideRawResource`; occurrence vertices
retain the selected cotree transition; start leaves retain their collision and
component; private outer vertices retain their exact physical port. -/
noncomputable def canonicalHullSeparatingObservation
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x}) :
    CanonicalHullSeparatingObservation axis hn2 hn3 hT assignment source :=
  canonicalHullSeparatingObservationAt axis hn2 hn3 hT assignment source source.1

/-- Precisely the observations through which the first-separator walk passes.
The proof on a retained edge says that the edge is already reserved. -/
inductive CanonicalHullSeparatingObservation.Continues
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x}} :
    CanonicalHullSeparatingObservation axis hn2 hn3 hT assignment source → Prop where
  | selectedStart collision component : Continues (.selectedStart collision component)
  | cotreeOccurrence transition : Continues (.cotreeOccurrence transition)
  | boundedCotree row col transition : Continues (.boundedCell row col (.inr transition))
  | boundedReserved row col edge
      (reserved : edge ∈ Set.range (internalTreeEdgeTokenEmbedding
        (supportFinset (gridGraph n n \ T))
        (terminalTreeEdgeEmbedding axis hn2 hn3 hT))) :
      Continues (.boundedCell row col (.inl edge))

/-- A path generated only by the actual parent map, with every vertex before
the endpoint certified to be a continuation observation. -/
inductive CanonicalHullFirstSeparatingContinuationPath
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x}) :
    FullPrunedComponentCotreeDualHullCarrier axis hn2 hn3 hT assignment → Type where
  | refl : CanonicalHullFirstSeparatingContinuationPath assignment source source.1
  | parent {vertex parent}
      (path : CanonicalHullFirstSeparatingContinuationPath assignment source vertex)
      (continues : (canonicalHullSeparatingObservationAt
        axis hn2 hn3 hT assignment source vertex).Continues)
      (hparent : (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).parent vertex = some parent) :
      CanonicalHullFirstSeparatingContinuationPath assignment source parent

/-- Live state of the actual first-separator continuation.  Unlike the former
remainder, its observation is tied to its endpoint and its path certifies that
only canonical parents, never unrelated choices, were followed. -/
structure CanonicalHullFirstSeparatingGeometryRemaining
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x}) where
  vertex : FullPrunedComponentCotreeDualHullCarrier axis hn2 hn3 hT assignment
  path : CanonicalHullFirstSeparatingContinuationPath
    axis hn2 hn3 hT assignment source vertex
  observation : CanonicalHullSeparatingObservation
    axis hn2 hn3 hT assignment source
  observation_eq : observation = canonicalHullSeparatingObservationAt
    axis hn2 hn3 hT assignment source vertex

/-- A continuation path is, after forgetting its no-earlier-stop certificates,
an ordinary parent-chain reachability proof. -/
theorem CanonicalHullFirstSeparatingContinuationPath.reached
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x}}
    {terminal : FullPrunedComponentCotreeDualHullCarrier
      axis hn2 hn3 hT assignment}
    (path : CanonicalHullFirstSeparatingContinuationPath
      axis hn2 hn3 hT assignment source terminal) :
    Relation.ReflTransGen
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).ParentStep source.1 terminal := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | parent path _ hparent ih => exact ih.tail hparent

/-- Exact exceptional outcome of the canonical hull walk.  The endpoint is the
first non-continuation observation and is the source of the reserved-port
obligation. -/
structure CanonicalHullFirstSeparatingRemainingCase
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x}) where
  terminal : FullPrunedComponentCotreeDualHullCarrier axis hn2 hn3 hT assignment
  path : CanonicalHullFirstSeparatingContinuationPath
    axis hn2 hn3 hT assignment source terminal
  port : GridCotreeOuterPort T
  observation : canonicalHullSeparatingObservationAt
    axis hn2 hn3 hT assignment source terminal = .boundaryPort port
  reserved : port ∈ Set.range (exitEmbedding axis hn2 hT)

theorem CanonicalHullFirstSeparatingRemainingCase.reached
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x}}
    (remaining : CanonicalHullFirstSeparatingRemainingCase
      axis hn2 hn3 hT assignment source) :
    Relation.ReflTransGen
      (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).ParentStep source.1 remaining.terminal :=
  remaining.path.reached

/-- A non-boundary point of the minimal hull has a parent.  Connectivity rules
out bounded roots; restriction to the ancestor hull introduces no new root. -/
theorem canonicalHull_parent_exists_of_observation_ne_boundary
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x})
    (vertex : FullPrunedComponentCotreeDualHullCarrier
      axis hn2 hn3 hT assignment)
    (hboundary : ∀ port, canonicalHullSeparatingObservationAt
      axis hn2 hn3 hT assignment source vertex ≠ .boundaryPort port) :
    ∃ parent, (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).parent vertex = some parent := by
  classical
  by_contra hparent
  push Not at hparent
  have hnone : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).parent vertex = none := by
    cases h : (fullPrunedComponentCotreeDualHullForest
        axis hn2 hn3 hT assignment).parent vertex with
    | none => rfl
    | some parent => exact (hparent parent h).elim
  have hambientNone : (fullPrunedComponentCotreeDualForest
      axis hn2 hn3 hT assignment).parent vertex.1 = none :=
    ((fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment)
      |>.ancestorHullForest_parent_eq_none_iff
        (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment)
        vertex).mp hnone
  have hroot : vertex.1 ∈ (fullPrunedComponentCotreeDualForest
      axis hn2 hn3 hT assignment).roots := by
    simpa [ParentForest.roots] using hambientNone
  obtain ⟨boundary, hvertex⟩ :=
    (fullPrunedComponentCotreeDual_mem_roots_iff_boundary
      axis hn2 hn3 hT assignment vertex.1).mp hroot
  rcases vertex with ⟨⟨component, v⟩, active⟩
  change v = .inr (.inr (.inr boundary)) at hvertex
  let target : FullPrunedComponentCotreeDualHullCarrier
      axis hn2 hn3 hT assignment :=
    ⟨⟨component, .inr (.inr (.inr boundary))⟩, by
      rw [← hvertex]
      exact active⟩
  have heq : (⟨⟨component, v⟩, active⟩ :
      FullPrunedComponentCotreeDualHullCarrier axis hn2 hn3 hT assignment) =
      target := Subtype.ext (Sigma.ext rfl (heq_of_eq hvertex))
  have hobs := congrArg
    (canonicalHullSeparatingObservationAt axis hn2 hn3 hT assignment source) heq
  apply hboundary
    (BoundaryTransitionOccurrence.outerPort
      (fullPrunedComponentCotreeDualEdgeTransition
        axis hn2 hn3 hT assignment) hn2 hn2 boundary)
  exact hobs.trans (by rfl)

/-- A source-indexed first-separator result.  Unlike the former bare candidate
function, this type does not claim that a residual physical resource exists. -/
inductive CanonicalHullFirstSeparatingResult
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x}) where
  | residual (candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
  | remaining (exception : CanonicalHullFirstSeparatingRemainingCase
      axis hn2 hn3 hT assignment source)

/-- Correctness certificate for one result of the canonical hull walk.  A
residual is the first unreserved internal edge or boundary port on the path;
the sole nonresidual result is the exact reserved boundary terminal. -/
inductive CanonicalHullFirstSeparatingResult.IsGeometric
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x}) :
    CanonicalHullFirstSeparatingResult axis hn2 hn3 hT assignment source → Prop where
  | residualBoundary (terminal) (path : CanonicalHullFirstSeparatingContinuationPath
      axis hn2 hn3 hT assignment source terminal) (port : GridCotreeOuterPort T)
      (hobservation : canonicalHullSeparatingObservationAt
        axis hn2 hn3 hT assignment source terminal = .boundaryPort port)
      (hunreserved : port ∉ Set.range (exitEmbedding axis hn2 hT)) :
      IsGeometric assignment source (.residual (.inl ⟨port, hunreserved⟩))
  | residualInternal (terminal) (path : CanonicalHullFirstSeparatingContinuationPath
      axis hn2 hn3 hT assignment source terminal) (row col) (edge)
      (hobservation : canonicalHullSeparatingObservationAt
        axis hn2 hn3 hT assignment source terminal = .boundedCell row col (.inl edge))
      (hunreserved : edge ∉ Set.range (internalTreeEdgeTokenEmbedding
        (supportFinset (gridGraph n n \ T))
        (terminalTreeEdgeEmbedding axis hn2 hn3 hT))) :
      IsGeometric assignment source (.residual (.inr (.inl ⟨edge, hunreserved⟩)))
  | reservedBoundary (remaining : CanonicalHullFirstSeparatingRemainingCase
      axis hn2 hn3 hT assignment source) :
      IsGeometric assignment source (.remaining remaining)

/-- A classification is no longer an arbitrary function.  Every returned value
comes with a derivation from the actual canonical hull observation. -/
structure CanonicalHullFirstSeparatingClassification
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) : Type where
  result : ∀ source : {x : FullPrunedComponentCotreeDualHullCarrier
      axis hn2 hn3 hT assignment //
    FullPrunedComponentCotreeDualHullCarrier.IsPhysical
      (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x},
    CanonicalHullFirstSeparatingResult axis hn2 hn3 hT assignment source
  geometric : ∀ source, CanonicalHullFirstSeparatingResult.IsGeometric
    axis hn2 hn3 hT assignment source (result source)

instance {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root} :
    CoeFun (CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment) (fun _ => ∀ source,
        CanonicalHullFirstSeparatingResult axis hn2 hn3 hT assignment source) :=
  ⟨CanonicalHullFirstSeparatingClassification.result⟩

/-- Continue one live state.  Stops are exactly an unreserved supported edge or
boundary port and a reserved boundary terminal; every other case takes the
unique parent. -/
noncomputable def canonicalHullFirstSeparatingResult.go
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x})
    (state : CanonicalHullFirstSeparatingGeometryRemaining
      axis hn2 hn3 hT assignment source) :
    {result : CanonicalHullFirstSeparatingResult axis hn2 hn3 hT assignment source //
      CanonicalHullFirstSeparatingResult.IsGeometric
        axis hn2 hn3 hT assignment source result} := by
  let forest := fullPrunedComponentCotreeDualHullForest
    axis hn2 hn3 hT assignment
  let next
      (continues : (canonicalHullSeparatingObservationAt
        axis hn2 hn3 hT assignment source state.vertex).Continues)
      (hboundary : ∀ port, canonicalHullSeparatingObservationAt
        axis hn2 hn3 hT assignment source state.vertex ≠ .boundaryPort port) :
      {nextState : CanonicalHullFirstSeparatingGeometryRemaining
          axis hn2 hn3 hT assignment source //
        (fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).rank nextState.vertex <
          (fullPrunedComponentCotreeDualHullForest
            axis hn2 hn3 hT assignment).rank state.vertex} := by
    cases hparent : forest.parent state.vertex with
    | some parent =>
        refine ⟨
          { vertex := parent
            path := .parent state.path continues (by simpa [forest] using hparent)
            observation := canonicalHullSeparatingObservationAt
              axis hn2 hn3 hT assignment source parent
            observation_eq := rfl }, ?_⟩
        exact (fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).rank_parent (by simpa [forest] using hparent)
    | none =>
        exfalso
        obtain ⟨parent, hsome⟩ :=
          canonicalHull_parent_exists_of_observation_ne_boundary
            axis hn2 hn3 hT assignment source state.vertex hboundary
        rw [show (fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).parent state.vertex = none by
            simpa [forest] using hparent] at hsome
        cases hsome
  exact match hobs : canonicalHullSeparatingObservationAt
      axis hn2 hn3 hT assignment source state.vertex with
  | .boundaryPort port =>
      if hreserved : port ∈ Set.range (exitEmbedding axis hn2 hT) then
        let remaining : CanonicalHullFirstSeparatingRemainingCase
            axis hn2 hn3 hT assignment source :=
          { terminal := state.vertex
            path := state.path
            port := port
            observation := hobs
            reserved := hreserved }
        ⟨.remaining remaining, .reservedBoundary remaining⟩
      else ⟨.residual (.inl ⟨port, hreserved⟩),
        .residualBoundary state.vertex state.path port hobs hreserved⟩
  | .boundedCell row col (.inl edge) =>
      if hreserved : edge ∈ Set.range (internalTreeEdgeTokenEmbedding
          (supportFinset (gridGraph n n \ T))
          (terminalTreeEdgeEmbedding axis hn2 hn3 hT)) then
        canonicalHullFirstSeparatingResult.go assignment source
          (next (hobs.symm ▸ .boundedReserved row col edge hreserved)
            (by intro port h; rw [hobs] at h; cases h)).1
      else ⟨.residual (.inr (.inl ⟨edge, hreserved⟩)),
        .residualInternal state.vertex state.path row col edge hobs hreserved⟩
  | .boundedCell row col (.inr transition) =>
      canonicalHullFirstSeparatingResult.go assignment source
        (next (hobs.symm ▸ .boundedCotree row col transition)
          (by intro port h; rw [hobs] at h; cases h)).1
  | .selectedStart collision component =>
      canonicalHullFirstSeparatingResult.go assignment source
        (next (hobs.symm ▸ .selectedStart collision component)
          (by intro port h; rw [hobs] at h; cases h)).1
  | .cotreeOccurrence transition =>
      canonicalHullFirstSeparatingResult.go assignment source
        (next (hobs.symm ▸ .cotreeOccurrence transition)
          (by intro port h; rw [hobs] at h; cases h)).1
termination_by (fullPrunedComponentCotreeDualHullForest
  axis hn2 hn3 hT assignment).rank state.vertex
decreasing_by
  · exact (next (hobs.symm ▸ .boundedReserved row col edge hreserved)
      (by intro port h; rw [hobs] at h; cases h)).2
  · exact (next (hobs.symm ▸ .boundedCotree row col transition)
      (by intro port h; rw [hobs] at h; cases h)).2
  · exact (next (hobs.symm ▸ .selectedStart collision component)
      (by intro port h; rw [hobs] at h; cases h)).2
  · exact (next (hobs.symm ▸ .cotreeOccurrence transition)
      (by intro port h; rw [hobs] at h; cases h)).2

/-- Result computed by the complete canonical parent-chain walk. -/
noncomputable def canonicalHullFirstSeparatingResult
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x}) :
    CanonicalHullFirstSeparatingResult axis hn2 hn3 hT assignment source :=
  (canonicalHullFirstSeparatingResult.go axis hn2 hn3 hT assignment source
    { vertex := source.1
      path := .refl
      observation := canonicalHullSeparatingObservation
        axis hn2 hn3 hT assignment source
      observation_eq := rfl }).1

/-- Unconditional canonical hull classification.  A private boundary
constructor is classified immediately.  Every other constructor returns its
exact supported-side/transition/component observation as the remaining
geometric case; in particular no residual candidate is chosen before
first-ownership and nonreservation have been proved. -/
noncomputable def canonicalHullFirstSeparatingClassification
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    CanonicalHullFirstSeparatingClassification axis hn2 hn3 hT assignment where
  result := canonicalHullFirstSeparatingResult axis hn2 hn3 hT assignment
  geometric source := (canonicalHullFirstSeparatingResult.go
    axis hn2 hn3 hT assignment source
      { vertex := source.1
        path := .refl
        observation := canonicalHullSeparatingObservation
          axis hn2 hn3 hT assignment source
        observation_eq := rfl }).2

/-- A candidate is geometrically available to a merger slot exactly when the
canonical inspection of that slot's physical child returns it. -/
def CanonicalActiveBranchGeometricFirstSeparator
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot)
    (candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT) : Prop :=
  let child := (fullPrunedComponentCotreeDualHullForest
    axis hn2 hn3 hT assignment).mergerSlotPhysicalChildEmbedding
      (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
      (fullPrunedComponentCotreeDualHull_nonphysicalChildren_card_le_one
        axis hn2 hn3 hT assignment) slot
  canonicalHullFirstSeparatingClassification axis hn2 hn3 hT assignment child =
    .residual candidate

/-- Exact subtype of merger slots whose complete canonical walk terminates at a
reserved boundary port rather than a residual separator. -/
abbrev CanonicalActiveBranchFirstSeparatorUnresolved
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  {slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot //
    ∀ candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT,
      ¬CanonicalActiveBranchGeometricFirstSeparator
        axis hn2 hn3 hT assignment slot candidate}

/-- Every merger slot is either classified by its actual canonical physical
child or belongs to the exact unresolved subtype. -/
theorem exists_geometricFirstSeparator_or_unresolved
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    (∃ candidate, CanonicalActiveBranchGeometricFirstSeparator
      axis hn2 hn3 hT assignment slot candidate) ∨
      ∃ unresolved : CanonicalActiveBranchFirstSeparatorUnresolved
        axis hn2 hn3 hT assignment, unresolved.1 = slot := by
  classical
  by_cases h : ∃ candidate, CanonicalActiveBranchGeometricFirstSeparator
      axis hn2 hn3 hT assignment slot candidate
  · exact Or.inl h
  · exact Or.inr ⟨⟨slot, by simpa only [not_exists] using h⟩, rfl⟩

/-- Two slots share an edge or component separator.  Boundary-port equality is
kept separate because its only possible duplication is the corner case. -/
def CanonicalActiveBranchesShareInternalCarrier
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (a b : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) : Prop :=
  (∃ edge, CanonicalActiveBranchGeometricFirstSeparator
      axis hn2 hn3 hT assignment a (.inr (.inl edge)) ∧
    CanonicalActiveBranchGeometricFirstSeparator
      axis hn2 hn3 hT assignment b (.inr (.inl edge))) ∨
  (∃ component, CanonicalActiveBranchGeometricFirstSeparator
      axis hn2 hn3 hT assignment a (.inr (.inr component)) ∧
    CanonicalActiveBranchGeometricFirstSeparator
      axis hn2 hn3 hT assignment b (.inr (.inr component)))

/-- Injectivity reduces to the intended geometric argument: equality of the
coordinate resource gives either a common edge/component or a common boundary
port; C4 separates the former and corner outer-port separation handles the
latter.  These two topological implications remain the genuine proof goals. -/
theorem canonicalActiveBranchGeometricFirstSeparator_injective
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (separator : (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) →
        CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (hcoordinate : ∀ {a b}, separator a = separator b →
      CanonicalActiveBranchesShareInternalCarrier
        axis hn2 hn3 hT assignment a b ∨
      ∃ port, CanonicalActiveBranchGeometricFirstSeparator
          axis hn2 hn3 hT assignment a (.inl port) ∧
        CanonicalActiveBranchGeometricFirstSeparator
          axis hn2 hn3 hT assignment b (.inl port))
    (hC4 : ∀ {a b}, CanonicalActiveBranchesShareInternalCarrier
      axis hn2 hn3 hT assignment a b → a = b)
    (hcorner : ∀ {a b port},
      CanonicalActiveBranchGeometricFirstSeparator
          axis hn2 hn3 hT assignment a (.inl port) →
      CanonicalActiveBranchGeometricFirstSeparator
          axis hn2 hn3 hT assignment b (.inl port) → a = b) :
    Function.Injective separator := by
  intro a b hab
  rcases hcoordinate hab with hcommon | ⟨port, ha, hb⟩
  · exact hC4 hcommon
  · exact hcorner ha hb

/-- The `MinimalAncestorHullRouting` singleton neighborhood, realized in the
actual residual physical pool. -/
noncomputable def canonicalActiveBranchNeighborhood
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    Finset (BoundaryGapResidualPhysicalResource axis hn2 hn3 hT) :=
  let child := (fullPrunedComponentCotreeDualHullForest
    axis hn2 hn3 hT assignment).mergerSlotPhysicalChildEmbedding
      (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
      (fullPrunedComponentCotreeDualHull_nonphysicalChildren_card_le_one
        axis hn2 hn3 hT assignment) slot
  match firstSeparating child with
  | .residual candidate =>
      {canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate}
  | .remaining _ => ∅

/-- Exact canonical active-branch Hall statement.  It is Hall for the realized
first-separator neighborhoods of the concrete minimal component-split hull. -/
def CanonicalActiveBranchHall
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment) : Prop :=
  LocalizedHall
    (canonicalActiveBranchNeighborhood axis hn2 hn3 hT assignment firstSeparating)

/-- `CanonicalActiveBranchHall` is equivalent, not merely sufficient, to the
existence of a genuine branch-owner embedding selecting an allowed realized
first separator for every merger slot. -/
theorem canonicalActiveBranchHall_iff_exists_branchOwner
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment) :
    CanonicalActiveBranchHall axis hn2 hn3 hT assignment firstSeparating ↔
      ∃ branchOwner :
          (fullPrunedComponentCotreeDualHullForest
            axis hn2 hn3 hT assignment).MergerSlot ↪
            BoundaryGapResidualPhysicalResource axis hn2 hn3 hT,
        ∀ slot, branchOwner slot ∈
          canonicalActiveBranchNeighborhood axis hn2 hn3 hT assignment
            firstSeparating slot := by
  exact localizedHall_iff_exists_embedding _

/-- Canonical branch ownership extracted from the proved Hall inequalities. -/
noncomputable def canonicalActiveBranchOwnerOfHall
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (hHall : CanonicalActiveBranchHall axis hn2 hn3 hT assignment
      firstSeparating) :
    (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT :=
  Classical.choose
    ((canonicalActiveBranchHall_iff_exists_branchOwner
      axis hn2 hn3 hT assignment firstSeparating).mp hHall)

theorem canonicalActiveBranchOwnerOfHall_mem_neighborhood
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (hHall : CanonicalActiveBranchHall axis hn2 hn3 hT assignment
      firstSeparating)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    canonicalActiveBranchOwnerOfHall axis hn2 hn3 hT assignment
        firstSeparating hHall slot ∈
      canonicalActiveBranchNeighborhood axis hn2 hn3 hT assignment
        firstSeparating slot :=
  Classical.choose_spec
    ((canonicalActiveBranchHall_iff_exists_branchOwner
      axis hn2 hn3 hT assignment firstSeparating).mp hHall) slot

/-- Used physical ports split by whether the canonical exit reservation already
occupies them.  Unlike `ReservedBoundaryGapRoot`, these types contain one copy
of a physical port, not one copy of every root occurrence above it. -/
abbrev ReservedBoundaryGapUsedRootPort {Carrier : Type*} [Fintype Carrier]
    [DecidableEq Carrier] (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T) :=
  {p : ↥(forest.usedRootPorts rootPort) //
    p.1 ∈ Set.range (exitEmbedding axis hn2 hT)}

abbrev UnreservedBoundaryGapUsedRootPort {Carrier : Type*} [Fintype Carrier]
    [DecidableEq Carrier] (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T) :=
  {p : ↥(forest.usedRootPorts rootPort) //
    p.1 ∉ Set.range (exitEmbedding axis hn2 hT)}

/-- Automatic duplicate-root payment is disabled.  Component-indexed sigma
copies are provenance, not independent physical resources; duplicate roots are
therefore always residual sources. -/
def ComponentResolvedBoundaryGapForestRealization.RootPortDebtCompatible
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment)
    (_rootPort : ↥realization.forest.roots → GridCotreeOuterPort T) : Prop :=
  False

/-- There are no automatically compatible duplicate slots. -/
abbrev CompatibleBoundaryGapRootPortDebtSlot
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment)
    (rootPort : ↥realization.forest.roots → GridCotreeOuterPort T) :=
  {_slot : realization.forest.RootPortDebtSlot rootPort //
    realization.RootPortDebtCompatible axis hn2 hn3 hT rootPort}

/-- The only duplicate slots for which a residual routing remains to be
supplied. -/
abbrev IncompatibleBoundaryGapRootPortDebtSlot
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment)
    (rootPort : ↥realization.forest.roots → GridCotreeOuterPort T) :=
  {_slot : realization.forest.RootPortDebtSlot rootPort //
    ¬realization.RootPortDebtCompatible axis hn2 hn3 hT rootPort}

/-- An unreserved used physical port is itself the boundary resource. -/
def unreservedBoundaryGapUsedRootPortEmbedding
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T) :
    UnreservedBoundaryGapUsedRootPort axis hn2 hT forest rootPort ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT where
  toFun p := .inl ⟨p.1.1, p.2⟩
  inj' := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : BoundaryGapResidualPhysicalResource axis hn2 hn3 hT =>
      match r with | .inl x => x.1 | .inr _ => p.1.1) hpq

/-- Vacuous embedding for the disabled automatic duplicate class. -/
noncomputable def compatibleBoundaryGapRootPortDebtEmbedding
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment)
    (rootPort : ↥realization.forest.roots → GridCotreeOuterPort T) :
    CompatibleBoundaryGapRootPortDebtSlot axis hn2 hn3 hT realization rootPort ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT where
  toFun slot := False.elim slot.2
  inj' := fun slot => False.elim slot.2

/-- The genuinely unresolved grouped routing data.  Unreserved used ports and
compatible duplicate slots are deliberately absent: their canonical maps are
defined above.  The final field records injectivity within every class and all
cross-image disjointness in one statement. -/
structure ComponentResolvedBoundaryGapPartialGroupedResidualRouting
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment)
    (rootPort : ↥realization.forest.roots → GridCotreeOuterPort T) where
  reservedUsedPortRouting :
    ReservedBoundaryGapUsedRootPort axis hn2 hT realization.forest rootPort ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  incompatibleDuplicateRouting :
    IncompatibleBoundaryGapRootPortDebtSlot axis hn2 hn3 hT realization rootPort ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  mergerSlotRouting : realization.forest.MergerSlot ↪
    BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  outerCollisionRouting : FullPrunedOuterCollision axis hn2 hn3 hT ↪
    BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  image_disjoint : Function.Injective (fun source :
      (UnreservedBoundaryGapUsedRootPort axis hn2 hT realization.forest rootPort ⊕
        (CompatibleBoundaryGapRootPortDebtSlot axis hn2 hn3 hT realization rootPort ⊕
          (ReservedBoundaryGapUsedRootPort axis hn2 hT realization.forest rootPort ⊕
            (IncompatibleBoundaryGapRootPortDebtSlot axis hn2 hn3 hT realization rootPort ⊕
              (realization.forest.MergerSlot ⊕
                FullPrunedOuterCollision axis hn2 hn3 hT))))) =>
    match source with
    | .inl p => unreservedBoundaryGapUsedRootPortEmbedding
        axis hn2 hn3 hT realization.forest rootPort p
    | .inr (.inl d) => compatibleBoundaryGapRootPortDebtEmbedding
        axis hn2 hn3 hT realization rootPort d
    | .inr (.inr (.inl p)) => reservedUsedPortRouting p
    | .inr (.inr (.inr (.inl d))) => incompatibleDuplicateRouting d
    | .inr (.inr (.inr (.inr (.inl m)))) => mergerSlotRouting m
    | .inr (.inr (.inr (.inr (.inr o)))) => outerCollisionRouting o)

private abbrev BoundaryGapCompletedGroupedSource
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment)
    (rootPort : ↥realization.forest.roots → GridCotreeOuterPort T) :=
  UnreservedBoundaryGapUsedRootPort axis hn2 hT realization.forest rootPort ⊕
    (CompatibleBoundaryGapRootPortDebtSlot axis hn2 hn3 hT realization rootPort ⊕
      (ReservedBoundaryGapUsedRootPort axis hn2 hT realization.forest rootPort ⊕
        (IncompatibleBoundaryGapRootPortDebtSlot axis hn2 hn3 hT realization rootPort ⊕
          (realization.forest.MergerSlot ⊕
            FullPrunedOuterCollision axis hn2 hn3 hT))))

private def boundaryGapCompletedGroupedSourceForget
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment)
    (rootPort : ↥realization.forest.roots → GridCotreeOuterPort T) :
    BoundaryGapCompletedGroupedSource axis hn2 hn3 hT realization rootPort →
      (↥(realization.forest.usedRootPorts rootPort) ⊕
        (realization.forest.RootPortDebtSlot rootPort ⊕
          (realization.forest.MergerSlot ⊕
            FullPrunedOuterCollision axis hn2 hn3 hT)))
  | .inl p => .inl p.1
  | .inr (.inl d) => .inr (.inl d.1)
  | .inr (.inr (.inl p)) => .inl p.1
  | .inr (.inr (.inr (.inl d))) => .inr (.inl d.1)
  | .inr (.inr (.inr (.inr (.inl m)))) => .inr (.inr (.inl m))
  | .inr (.inr (.inr (.inr (.inr o)))) => .inr (.inr (.inr o))

private noncomputable def boundaryGapCompletedGroupedSourceClassify
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment)
    (rootPort : ↥realization.forest.roots → GridCotreeOuterPort T) :
    (↥(realization.forest.usedRootPorts rootPort) ⊕
      (realization.forest.RootPortDebtSlot rootPort ⊕
        (realization.forest.MergerSlot ⊕
          FullPrunedOuterCollision axis hn2 hn3 hT))) →
      BoundaryGapCompletedGroupedSource axis hn2 hn3 hT realization rootPort
  | .inl p => if hp : p.1 ∈ Set.range (exitEmbedding axis hn2 hT)
      then .inr (.inr (.inl ⟨p, hp⟩)) else .inl ⟨p, hp⟩
  | .inr (.inl d) =>
      if hd : realization.RootPortDebtCompatible axis hn2 hn3 hT rootPort
      then .inr (.inl ⟨d, hd⟩) else .inr (.inr (.inr (.inl ⟨d, hd⟩)))
  | .inr (.inr (.inl m)) => .inr (.inr (.inr (.inr (.inl m))))
  | .inr (.inr (.inr o)) => .inr (.inr (.inr (.inr (.inr o))))

/-- Split used ports and duplicate slots into the solved and unresolved sum
tags.  Forgetting those tags is a left inverse, so no injectivity assumption on
the root-port map is involved. -/
private noncomputable def boundaryGapCompletedGroupedSourceEmbedding
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment)
    (rootPort : ↥realization.forest.roots → GridCotreeOuterPort T) :
    (↥(realization.forest.usedRootPorts rootPort) ⊕
      (realization.forest.RootPortDebtSlot rootPort ⊕
        (realization.forest.MergerSlot ⊕
          FullPrunedOuterCollision axis hn2 hn3 hT))) ↪
      BoundaryGapCompletedGroupedSource axis hn2 hn3 hT realization rootPort where
  toFun := boundaryGapCompletedGroupedSourceClassify axis hn2 hn3 hT realization rootPort
  inj' := by
    intro a b hab
    have hleft : ∀ x,
        boundaryGapCompletedGroupedSourceForget axis hn2 hn3 hT realization rootPort
            (boundaryGapCompletedGroupedSourceClassify axis hn2 hn3 hT
              realization rootPort x) = x := by
      intro x
      rcases x with p | d
      · simp only [boundaryGapCompletedGroupedSourceClassify]
        split_ifs <;> rfl
      · rcases d with d | tail
        · simp only [boundaryGapCompletedGroupedSourceClassify]
          split_ifs <;> rfl
        · rcases tail with m | o <;> rfl
    calc
      a = boundaryGapCompletedGroupedSourceForget axis hn2 hn3 hT realization rootPort
          (boundaryGapCompletedGroupedSourceClassify axis hn2 hn3 hT
            realization rootPort a) := (hleft a).symm
      _ = boundaryGapCompletedGroupedSourceForget axis hn2 hn3 hT realization rootPort
          (boundaryGapCompletedGroupedSourceClassify axis hn2 hn3 hT
            realization rootPort b) := congrArg _ hab
      _ = b := hleft b

/-- Legacy quotient-root version of the component-split boundary-gap ledger.
A used physical port is
counted once.  Every additional occurrence root over that port is an explicit
debt slot, and debt, merger slots, and outer demands are paid from the same
residual physical pool.  This structure remains for compatibility with the
component-local geometry API; the active canonical grouped ledger below uses
the global shared hull. -/
structure ComponentResolvedBoundaryGapGroupedLedger
    (root : GridVertex n n)
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    extends ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment where
  rootPort : ↥forest.roots → GridCotreeOuterPort T
  residualRouting :
    (↥(forest.usedRootPorts rootPort) ⊕
      (forest.RootPortDebtSlot rootPort ⊕
        (forest.MergerSlot ⊕ FullPrunedOuterCollision axis hn2 hn3 hT))) ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT

namespace ComponentResolvedBoundaryGapPartialGroupedResidualRouting

/-- Insert the two canonical routes into the partial package. -/
noncomputable def completedRouting
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment}
    {rootPort : ↥realization.forest.roots → GridCotreeOuterPort T}
    (routing : ComponentResolvedBoundaryGapPartialGroupedResidualRouting
      axis hn2 hn3 hT realization rootPort) :
    (↥(realization.forest.usedRootPorts rootPort) ⊕
      (realization.forest.RootPortDebtSlot rootPort ⊕
        (realization.forest.MergerSlot ⊕
          FullPrunedOuterCollision axis hn2 hn3 hT))) ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT :=
  (boundaryGapCompletedGroupedSourceEmbedding axis hn2 hn3 hT
      realization rootPort).trans
    { toFun := fun source =>
        match source with
        | .inl p => unreservedBoundaryGapUsedRootPortEmbedding
            axis hn2 hn3 hT realization.forest rootPort p
        | .inr (.inl d) => compatibleBoundaryGapRootPortDebtEmbedding
            axis hn2 hn3 hT realization rootPort d
        | .inr (.inr (.inl p)) => routing.reservedUsedPortRouting p
        | .inr (.inr (.inr (.inl d))) => routing.incompatibleDuplicateRouting d
        | .inr (.inr (.inr (.inr (.inl m)))) => routing.mergerSlotRouting m
        | .inr (.inr (.inr (.inr (.inr o)))) => routing.outerCollisionRouting o
      inj' := routing.image_disjoint }

noncomputable def toGroupedLedger
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {realization : ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment}
    {rootPort : ↥realization.forest.roots → GridCotreeOuterPort T}
    (routing : ComponentResolvedBoundaryGapPartialGroupedResidualRouting
      axis hn2 hn3 hT realization rootPort) :
    ComponentResolvedBoundaryGapGroupedLedger axis hn2 hn3 hT root assignment where
  toComponentResolvedBoundaryGapForestRealization := realization
  rootPort := rootPort
  residualRouting := routing.completedRouting axis hn2 hn3 hT

end ComponentResolvedBoundaryGapPartialGroupedResidualRouting

/-- The partial grouped residual package specialized to the canonical minimal
hull.  Its only supplied routes are the four genuinely unresolved classes. -/
abbrev FullPrunedComponentCotreeDualHullPartialGroupedResidualRouting
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  ComponentResolvedBoundaryGapPartialGroupedResidualRouting axis hn2 hn3 hT
    (fullPrunedComponentCotreeDualRealization axis hn2 hn3 hT assignment)
    (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment)

/-- Legacy completion of the component-split minimal-hull grouped ledger.  New
canonical accounting must use `FullPrunedSharedCotreeDualHullGroupedLedger`. -/
noncomputable def legacyFullPrunedComponentCotreeDualHullGroupedLedger
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (routing : FullPrunedComponentCotreeDualHullPartialGroupedResidualRouting
      axis hn2 hn3 hT assignment) :
    ComponentResolvedBoundaryGapGroupedLedger axis hn2 hn3 hT root assignment :=
  routing.toGroupedLedger axis hn2 hn3 hT

/-- Active grouped ledger on the global shared cotree-dual hull. Its source
identity is exactly `usedPorts ⊕ branchExcess`; outer collisions are
additional residual demands rather than vertices of the inward start hull. -/
structure FullPrunedSharedCotreeDualHullGroupedLedger
    (root : GridVertex n n)
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) where
  residualRouting :
    (↥((fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment).usedRootPorts
          (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment)) ⊕
      ((fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment).MergerSlot ⊕
        FullPrunedOuterCollision axis hn2 hn3 hT)) ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT

namespace FullPrunedSharedCotreeDualHullGroupedLedger

/-- Exact active inward-source identity, stated in the grouped-ledger API. -/
theorem card_inward_eq_usedPorts_add_branchExcess
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (_ledger : FullPrunedSharedCotreeDualHullGroupedLedger
      axis hn2 hn3 hT root assignment) :
    Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) =
      ((fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment).usedRootPorts
        (fullPrunedSharedCotreeDualHullRootPort
          axis hn2 hn3 hT assignment)).card +
      (fullPrunedSharedCotreeDualHullForest
        axis hn2 hn3 hT assignment).branchExcess :=
  fullPrunedSharedCotreeDualHull_card_starts_eq_grouped
    axis hn2 hn3 hT assignment

/-- The active shared grouped routing gives the residual collision bound. -/
theorem card_inward_add_outer_le_residual
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (ledger : FullPrunedSharedCotreeDualHullGroupedLedger
      axis hn2 hn3 hT root assignment) :
    Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) +
      Fintype.card (FullPrunedOuterCollision axis hn2 hn3 hT) ≤
      Fintype.card (UnreservedCanonicalBoundaryPort axis hn2 hT) +
        Fintype.card (BoundaryGapResidualInternalResource axis hn2 hn3 hT) +
          Fintype.card (BoundaryGapResidualComponentResource axis hn2 hn3 hT) := by
  have hroute := Fintype.card_le_of_injective
    ledger.residualRouting ledger.residualRouting.injective
  simp only [Fintype.card_sum, Fintype.card_coe,
    ParentForest.card_mergerSlot] at hroute
  have hstarts := ledger.card_inward_eq_usedPorts_add_branchExcess
    axis hn2 hn3 hT
  omega

end FullPrunedSharedCotreeDualHullGroupedLedger

/-! #### Active shared-hull grouped residual Hall -/

/-- The source of the active shared-hull grouped ledger, before the automatic
unreserved-port route is installed. -/
abbrev FullPrunedSharedCotreeDualHullGroupedSource
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  let forest := fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment
  let rootPort := fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment
  ↥(forest.usedRootPorts rootPort) ⊕
    (forest.MergerSlot ⊕ FullPrunedOuterCollision axis hn2 hn3 hT)

/-- The active residual source. Used ports are split physically: unreserved
ports have a canonical route, while reserved ports, merger slots of the global
shared hull, and outer collisions remain Hall demands. -/
abbrev SharedCanonicalGroupedResidualSource
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  let forest := fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment
  let rootPort := fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment
  ReservedBoundaryGapUsedRootPort axis hn2 hT forest rootPort ⊕
    (forest.MergerSlot ⊕ FullPrunedOuterCollision axis hn2 hn3 hT)

/-- The unreserved used-port part of the shared hull is routed to its own
physical boundary resource before Hall is invoked. -/
def sharedCanonicalGroupedAutomaticEmbedding
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    UnreservedBoundaryGapUsedRootPort axis hn2 hT
        (fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment)
        (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment) ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT :=
  unreservedBoundaryGapUsedRootPortEmbedding axis hn2 hn3 hT _ _

/-- A proof-carrying physical first-separator neighborhood.  Its freshness
proof is exactly what permits a Hall choice to be combined with the automatic
unreserved-port embedding. -/
structure PhysicalFirstSeparatorNeighborhood
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) where
  resources : Finset (BoundaryGapResidualPhysicalResource axis hn2 hn3 hT)
  fresh : ∀ resource ∈ resources,
    resource ∉ Set.range
      (sharedCanonicalGroupedAutomaticEmbedding axis hn2 hn3 hT assignment)

/-- Proof-carrying physical neighborhoods for all nonautomatic shared-hull
sources.  In particular, merger slots belong to the global shared hull, not a
component-split copy. -/
structure SharedCanonicalGroupedPhysicalNeighborhoods
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) where
  reservedUsedPort : ReservedBoundaryGapUsedRootPort axis hn2 hT
      (fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment)
      (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment) →
    PhysicalFirstSeparatorNeighborhood axis hn2 hn3 hT assignment
  mergerSlot :
      (fullPrunedSharedCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot →
    PhysicalFirstSeparatorNeighborhood axis hn2 hn3 hT assignment
  outerCollision : FullPrunedOuterCollision axis hn2 hn3 hT →
    PhysicalFirstSeparatorNeighborhood axis hn2 hn3 hT assignment

/-- The physical neighborhood of an active shared-hull residual source. -/
def sharedCanonicalGroupedResidualNeighborhood
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment) :
    SharedCanonicalGroupedResidualSource axis hn2 hn3 hT assignment →
      Finset (BoundaryGapResidualPhysicalResource axis hn2 hn3 hT)
  | .inl port => (neighborhoods.reservedUsedPort port).resources
  | .inr (.inl slot) => (neighborhoods.mergerSlot slot).resources
  | .inr (.inr collision) => (neighborhoods.outerCollision collision).resources

/-- Physical merger resources refined to one descendant-component fiber.  The
partial classifier is supplied by the downstream geometric walk; `none` permits
resources that carry no raw-component provenance. Filtering, rather than
choosing a component for the whole sector, handles genuinely shared sectors. -/
def sharedCanonicalMergerComponentNeighborhood
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment)
    (resourceComponent : BoundaryGapResidualPhysicalResource axis hn2 hn3 hT →
      Option (ContactRawComponent (T := T)))
    (obligation : FullPrunedSharedCotreeDualHullMergerComponentObligation
      axis hn2 hn3 hT assignment) :
    Finset (BoundaryGapResidualPhysicalResource axis hn2 hn3 hT) :=
  (neighborhoods.mergerSlot obligation.1).resources.filter fun resource =>
    resourceComponent resource = some
      (fullPrunedSharedCotreeDualHullMergerObligationComponent
        axis hn2 hn3 hT obligation)

/-- Membership in a refined downstream neighborhood preserves its raw
component by construction. -/
theorem sharedCanonicalMergerComponentNeighborhood_component
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment)
    (resourceComponent : BoundaryGapResidualPhysicalResource axis hn2 hn3 hT →
      Option (ContactRawComponent (T := T)))
    (obligation : FullPrunedSharedCotreeDualHullMergerComponentObligation
      axis hn2 hn3 hT assignment) {resource}
    (hresource : resource ∈ sharedCanonicalMergerComponentNeighborhood
      axis hn2 hn3 hT neighborhoods resourceComponent obligation) :
    resourceComponent resource = some
      (fullPrunedSharedCotreeDualHullMergerObligationComponent
        axis hn2 hn3 hT obligation) := by
  exact (Finset.mem_filter.mp hresource).2

theorem sharedCanonicalGroupedResidualNeighborhood_fresh
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment)
    (source : SharedCanonicalGroupedResidualSource axis hn2 hn3 hT assignment)
    {resource : BoundaryGapResidualPhysicalResource axis hn2 hn3 hT}
    (hresource : resource ∈ sharedCanonicalGroupedResidualNeighborhood
      axis hn2 hn3 hT neighborhoods source) :
    resource ∉ Set.range
      (sharedCanonicalGroupedAutomaticEmbedding axis hn2 hn3 hT assignment) := by
  rcases source with port | slot | collision
  · exact (neighborhoods.reservedUsedPort port).fresh resource hresource
  · exact (neighborhoods.mergerSlot slot).fresh resource hresource
  · exact (neighborhoods.outerCollision collision).fresh resource hresource

/-- Hall's condition for the active global shared-hull residual source. -/
def SharedCanonicalGroupedResidualHall
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment) : Prop :=
  LocalizedHall (sharedCanonicalGroupedResidualNeighborhood
    axis hn2 hn3 hT neighborhoods)

abbrev SharedCanonicalPartialGroupedResidualRouting
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment) :=
  LocalizedRouting (sharedCanonicalGroupedResidualNeighborhood
    axis hn2 hn3 hT neighborhoods)

theorem sharedCanonicalGroupedResidualHall_iff_nonempty_routing
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment) :
    SharedCanonicalGroupedResidualHall axis hn2 hn3 hT neighborhoods ↔
      Nonempty (SharedCanonicalPartialGroupedResidualRouting
        axis hn2 hn3 hT neighborhoods) :=
  localizedHall_iff_nonempty_routing _

private noncomputable def sharedCanonicalGroupedSourceClassify
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    FullPrunedSharedCotreeDualHullGroupedSource axis hn2 hn3 hT assignment →
      (UnreservedBoundaryGapUsedRootPort axis hn2 hT
          (fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment)
          (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment) ⊕
        SharedCanonicalGroupedResidualSource axis hn2 hn3 hT assignment)
  | .inl port => if hport : port.1 ∈ Set.range (exitEmbedding axis hn2 hT)
      then .inr (.inl ⟨port, hport⟩) else .inl ⟨port, hport⟩
  | .inr tail => .inr (.inr tail)

private noncomputable def sharedCanonicalGroupedSourceForget
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    (UnreservedBoundaryGapUsedRootPort axis hn2 hT
        (fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment)
        (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment) ⊕
      SharedCanonicalGroupedResidualSource axis hn2 hn3 hT assignment) →
      FullPrunedSharedCotreeDualHullGroupedSource axis hn2 hn3 hT assignment
  | .inl port => .inl port.1
  | .inr (.inl port) => .inl port.1
  | .inr (.inr tail) => .inr tail

private noncomputable def sharedCanonicalGroupedSourceEmbedding
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    FullPrunedSharedCotreeDualHullGroupedSource axis hn2 hn3 hT assignment ↪
      (UnreservedBoundaryGapUsedRootPort axis hn2 hT
          (fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment)
          (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment) ⊕
        SharedCanonicalGroupedResidualSource axis hn2 hn3 hT assignment) where
  toFun := sharedCanonicalGroupedSourceClassify axis hn2 hn3 hT assignment
  inj' := by
    intro a b hab
    have hleft : ∀ x,
        sharedCanonicalGroupedSourceForget axis hn2 hn3 hT assignment
            (sharedCanonicalGroupedSourceClassify axis hn2 hn3 hT assignment x) = x := by
      intro x
      rcases x with port | tail
      · simp only [sharedCanonicalGroupedSourceClassify]
        split_ifs <;> rfl
      · rfl
    rw [← hleft a, ← hleft b, hab]

/-- Install the automatic unreserved-port route beside a Hall routing. -/
noncomputable def sharedCanonicalGroupedCompletedEmbedding
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment}
    (routing : SharedCanonicalPartialGroupedResidualRouting
      axis hn2 hn3 hT neighborhoods) :
    FullPrunedSharedCotreeDualHullGroupedSource axis hn2 hn3 hT assignment ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT :=
  (sharedCanonicalGroupedSourceEmbedding axis hn2 hn3 hT assignment).trans
    { toFun := fun source => match source with
        | .inl port => sharedCanonicalGroupedAutomaticEmbedding
            axis hn2 hn3 hT assignment port
        | .inr residual => routing residual
      inj' := by
        intro a b hab
        rcases a with a | a
        · rcases b with b | b
          · exact congrArg Sum.inl
              ((sharedCanonicalGroupedAutomaticEmbedding
                axis hn2 hn3 hT assignment).injective hab)
          · exact False.elim
              ((sharedCanonicalGroupedResidualNeighborhood_fresh
                axis hn2 hn3 hT neighborhoods b (routing.mem_neighborhood b))
                  ⟨a, hab⟩)
        · rcases b with b | b
          · exact False.elim
              ((sharedCanonicalGroupedResidualNeighborhood_fresh
                axis hn2 hn3 hT neighborhoods a (routing.mem_neighborhood a))
                  ⟨b, hab.symm⟩)
          · exact congrArg Sum.inr (routing.toEmbedding.injective hab) }

/-- A completion records that the active shared ledger is precisely the
automatic unreserved-port route plus one neighborhood-respecting Hall route. -/
structure FullPrunedSharedCotreeDualHullGroupedLedgerCompletion
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment) where
  residualRouting : SharedCanonicalPartialGroupedResidualRouting
    axis hn2 hn3 hT neighborhoods
  ledger : FullPrunedSharedCotreeDualHullGroupedLedger
    axis hn2 hn3 hT root assignment
  ledger_eq : ledger.residualRouting =
    sharedCanonicalGroupedCompletedEmbedding axis hn2 hn3 hT residualRouting

noncomputable def SharedCanonicalPartialGroupedResidualRouting.toCompletion
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment}
    (routing : SharedCanonicalPartialGroupedResidualRouting
      axis hn2 hn3 hT neighborhoods) :
    FullPrunedSharedCotreeDualHullGroupedLedgerCompletion
      axis hn2 hn3 hT neighborhoods where
  residualRouting := routing
  ledger := { residualRouting :=
    sharedCanonicalGroupedCompletedEmbedding axis hn2 hn3 hT routing }
  ledger_eq := rfl

/-- Active Hall is exactly completion of the global shared-hull grouped ledger;
no component-split realization or matching field occurs in either side. -/
theorem sharedCanonicalGroupedResidualHall_iff_nonempty_ledgerCompletion
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment) :
    SharedCanonicalGroupedResidualHall axis hn2 hn3 hT neighborhoods ↔
      Nonempty (FullPrunedSharedCotreeDualHullGroupedLedgerCompletion
        axis hn2 hn3 hT neighborhoods) := by
  rw [sharedCanonicalGroupedResidualHall_iff_nonempty_routing]
  constructor
  · rintro ⟨routing⟩
    exact ⟨routing.toCompletion axis hn2 hn3 hT⟩
  · rintro ⟨completion⟩
    exact ⟨completion.residualRouting⟩

/-- The Hall completion supplies the active residual collision bound. -/
theorem sharedCanonicalGroupedResidualHall_residualBound
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment)
    (hHall : SharedCanonicalGroupedResidualHall axis hn2 hn3 hT neighborhoods) :
    Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) +
        Fintype.card (FullPrunedOuterCollision axis hn2 hn3 hT) ≤
      Fintype.card (UnreservedCanonicalBoundaryPort axis hn2 hT) +
        Fintype.card (BoundaryGapResidualInternalResource axis hn2 hn3 hT) +
          Fintype.card (BoundaryGapResidualComponentResource axis hn2 hn3 hT) := by
  obtain ⟨completion⟩ :=
    (sharedCanonicalGroupedResidualHall_iff_nonempty_ledgerCompletion
      axis hn2 hn3 hT neighborhoods).mp hHall
  exact completion.ledger.card_inward_add_outer_le_residual axis hn2 hn3 hT

/-- The finite residual bound supplied by the shared grouped Hall condition is
exactly the capacity needed by the port-aware quotient routing.  The
inward/outer germ partition recovers every ranked collision, and changing from
ranked to arbitrary carrier representatives does not change cardinality. -/
theorem sharedCanonicalGroupedResidualHall_canonicalExpandedJointCollisionRouting
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment)
    (hHall : SharedCanonicalGroupedResidualHall axis hn2 hn3 hT neighborhoods) :
    CanonicalExpandedJointCollisionRouting axis hn2 hn3 hT := by
  rw [CanonicalExpandedJointCollisionRouting,
    nonempty_portAwarePhysicalTreeTokenQuotientRouting_iff_card_le]
  have hbound := sharedCanonicalGroupedResidualHall_residualBound
    axis hn2 hn3 hT neighborhoods hHall
  have hcollision :
      Nat.card (CarrierCollision
          (FullPrunedTokenCarrier axis hn2 hn3 hT)) =
        Nat.card (FullPrunedInwardCollision axis hn2 hn3 hT) +
          Nat.card (FullPrunedOuterCollision axis hn2 hn3 hT) := by
    have hr := card_rankedCarrierCollision_eq_card_carrierCollision
      (FullPrunedTokenCarrier axis hn2 hn3 hT)
      (fullPrunedTokenRank axis hn2 hn3 hT)
    have hp := card_fullPrunedOrderedCollision_eq_inward_add_outer
      axis hn2 hn3 hT
    simpa only [Fintype.card_eq_nat_card] using hr.symm.trans hp
  simpa only [Fintype.card_eq_nat_card, hcollision, Nat.add_assoc] using hbound

noncomputable instance componentResolvedBoundaryGapGroupedLedgerCarrierFintype
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (ledger : ComponentResolvedBoundaryGapGroupedLedger
      axis hn2 hn3 hT root assignment) : Fintype ledger.Carrier :=
  ledger.carrierFintype

noncomputable instance componentResolvedBoundaryGapGroupedLedgerCarrierDecidableEq
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (ledger : ComponentResolvedBoundaryGapGroupedLedger
      axis hn2 hn3 hT root assignment) : DecidableEq ledger.Carrier :=
  ledger.carrierDecidableEq

namespace ComponentResolvedBoundaryGapGroupedLedger

variable {root : GridVertex n n}
  {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}

/-- Exact Euler formula exposed by the grouped ledger. -/
theorem card_leaves_eq_used_ports_add_debt_add_branchExcess
    (ledger : ComponentResolvedBoundaryGapGroupedLedger
      axis hn2 hn3 hT root assignment) :
    ledger.forest.leaves.card =
      (ledger.forest.usedRootPorts ledger.rootPort).card +
        ledger.forest.rootPortDebt ledger.rootPort +
          ledger.forest.branchExcess :=
  ledger.forest.card_leaves_eq_usedRootPorts_add_debt_add_branchExcess
    ledger.rootPort

/-- The grouped quotient ledger implies the same residual collision bound as a
pointwise root routing, but repeated ports are charged as debt rather than
being treated as fresh ports. -/
theorem card_inward_add_outer_le_residual
    (ledger : ComponentResolvedBoundaryGapGroupedLedger
      axis hn2 hn3 hT root assignment) :
    Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) +
      Fintype.card (FullPrunedOuterCollision axis hn2 hn3 hT) ≤
      Fintype.card (UnreservedCanonicalBoundaryPort axis hn2 hT) +
        Fintype.card (BoundaryGapResidualInternalResource axis hn2 hn3 hT) +
          Fintype.card (BoundaryGapResidualComponentResource axis hn2 hn3 hT) := by
  have hstarts :=
    ComponentResolvedBoundaryGapForestRealization.card_starts_le_card_roots_add_branchExcess
      axis hn2 hn3 hT ledger.toComponentResolvedBoundaryGapForestRealization
  have hroots := ledger.forest.card_usedRootPorts_add_rootPortDebt ledger.rootPort
  have hroute := Fintype.card_le_of_injective
    ledger.residualRouting ledger.residualRouting.injective
  simp only [Fintype.card_sum, Fintype.card_coe,
    ParentForest.card_rootPortDebtSlot, ParentForest.card_mergerSlot] at hroute
  omega

end ComponentResolvedBoundaryGapGroupedLedger

/-- Legacy conditional geometry package for component-split grouped accounting.
Its fields demand a joint residual embedding; global-core correction does not
derive one by paying copied roots or branch slots separately. -/
structure ComponentResolvedBoundaryGapForestGeometry
    (root : GridVertex n n)
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) where
  unreservedRootEmbedding :
    UnreservedBoundaryGapRoot axis hn2 hT
        (fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
        (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment) ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  reservedInwardRootRouting :
    ReservedBoundaryGapRoot axis hn2 hT
        (fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
        (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment) ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  branchOwner :
    (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot ↪
    BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  outerCollisionRouting : FullPrunedOuterCollision axis hn2 hn3 hT ↪
    BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  unreserved_reserved_disjoint : ∀ a b,
    unreservedRootEmbedding a ≠ reservedInwardRootRouting b
  unreserved_branch_disjoint : ∀ a b,
    unreservedRootEmbedding a ≠ branchOwner b
  unreserved_outer_disjoint : ∀ a b,
    unreservedRootEmbedding a ≠ outerCollisionRouting b
  reserved_branch_disjoint : ∀ a b,
    reservedInwardRootRouting a ≠ branchOwner b
  reserved_outer_disjoint : ∀ a b,
    reservedInwardRootRouting a ≠ outerCollisionRouting b
  branch_outer_disjoint : ∀ a b,
    branchOwner a ≠ outerCollisionRouting b

/-- A completed ledger stores the root partition and the four jointly disjoint
residual assignments. -/
structure ComponentResolvedBoundaryGapForestLedger
    (root : GridVertex n n)
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    extends ComponentResolvedBoundaryGapForestRealization
      axis hn2 hn3 hT root assignment where
  rootPort : ↥forest.roots → GridCotreeOuterPort T
  unreservedRootEmbedding :
    UnreservedBoundaryGapRoot axis hn2 hT forest rootPort ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  reservedInwardRootRouting :
    ReservedBoundaryGapRoot axis hn2 hT forest rootPort ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  branchOwner : forest.MergerSlot ↪
    BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  outerCollisionRouting : FullPrunedOuterCollision axis hn2 hn3 hT ↪
    BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  unreserved_reserved_disjoint : ∀ a b,
    unreservedRootEmbedding a ≠ reservedInwardRootRouting b
  unreserved_branch_disjoint : ∀ a b,
    unreservedRootEmbedding a ≠ branchOwner b
  unreserved_outer_disjoint : ∀ a b,
    unreservedRootEmbedding a ≠ outerCollisionRouting b
  reserved_branch_disjoint : ∀ a b,
    reservedInwardRootRouting a ≠ branchOwner b
  reserved_outer_disjoint : ∀ a b,
    reservedInwardRootRouting a ≠ outerCollisionRouting b
  branch_outer_disjoint : ∀ a b,
    branchOwner a ≠ outerCollisionRouting b

/-- Supplying the geometry maps completes the canonical realization; its root
ports are fixed by root classification. -/
noncomputable def ComponentResolvedBoundaryGapForestGeometry.toLedger
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (geometry : ComponentResolvedBoundaryGapForestGeometry
      axis hn2 hn3 hT root assignment) :
    ComponentResolvedBoundaryGapForestLedger axis hn2 hn3 hT root assignment where
  toComponentResolvedBoundaryGapForestRealization :=
    fullPrunedComponentCotreeDualRealization axis hn2 hn3 hT assignment
  rootPort := fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
  unreservedRootEmbedding := geometry.unreservedRootEmbedding
  reservedInwardRootRouting := geometry.reservedInwardRootRouting
  branchOwner := geometry.branchOwner
  outerCollisionRouting := geometry.outerCollisionRouting
  unreserved_reserved_disjoint := geometry.unreserved_reserved_disjoint
  unreserved_branch_disjoint := geometry.unreserved_branch_disjoint
  unreserved_outer_disjoint := geometry.unreserved_outer_disjoint
  reserved_branch_disjoint := geometry.reserved_branch_disjoint
  reserved_outer_disjoint := geometry.reserved_outer_disjoint
  branch_outer_disjoint := geometry.branch_outer_disjoint

noncomputable instance componentResolvedBoundaryGapForestLedgerCarrierFintype
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (ledger : ComponentResolvedBoundaryGapForestLedger
      axis hn2 hn3 hT root assignment) : Fintype ledger.Carrier :=
  ledger.carrierFintype

noncomputable instance componentResolvedBoundaryGapForestLedgerCarrierDecidableEq
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (ledger : ComponentResolvedBoundaryGapForestLedger
      axis hn2 hn3 hT root assignment) : DecidableEq ledger.Carrier :=
  ledger.carrierDecidableEq

namespace ComponentResolvedBoundaryGapForestLedger

variable {root : GridVertex n n}
  {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}

/-- Exact Euler accounting before applying the two geometric injections. -/
theorem card_starts_le_card_roots_add_branchExcess
    (ledger : ComponentResolvedBoundaryGapForestLedger
      axis hn2 hn3 hT root assignment) :
    Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) ≤
      ledger.forest.roots.card + ledger.forest.branchExcess := by
  exact ComponentResolvedBoundaryGapForestRealization.card_starts_le_card_roots_add_branchExcess
    axis hn2 hn3 hT ledger.toComponentResolvedBoundaryGapForestRealization

/-- The root-port predicate gives an exact complementary partition.  It does
not itself route either class. -/
theorem card_roots_eq_unreserved_add_reserved
    (ledger : ComponentResolvedBoundaryGapForestLedger
      axis hn2 hn3 hT root assignment) :
    ledger.forest.roots.card =
      Fintype.card (UnreservedBoundaryGapRoot axis hn2 hT
        ledger.forest ledger.rootPort) +
      Fintype.card (ReservedBoundaryGapRoot axis hn2 hT
        ledger.forest ledger.rootPort) := by
  let := ledger.carrierFintype
  let := ledger.carrierDecidableEq
  classical
  have hcompl := Fintype.card_subtype_compl
    (fun a : ↥ledger.forest.roots =>
      ledger.rootPort a ∈ Set.range (exitEmbedding axis hn2 hT))
  have hle : Fintype.card {a : ↥ledger.forest.roots //
      ledger.rootPort a ∈ Set.range (exitEmbedding axis hn2 hT)} ≤
      Fintype.card ↥ledger.forest.roots := Fintype.card_subtype_le _
  rw [← Fintype.card_coe]
  change Fintype.card ↥ledger.forest.roots =
    Fintype.card {a : ↥ledger.forest.roots //
      ledger.rootPort a ∉ Set.range (exitEmbedding axis hn2 hT)} +
    Fintype.card {a : ↥ledger.forest.roots //
      ledger.rootPort a ∈ Set.range (exitEmbedding axis hn2 hT)}
  rw [Nat.add_comm, hcompl]
  exact (Nat.add_sub_of_le hle).symm

/-- Joint residual routing; injectivity records all required disjointness. -/
noncomputable def residualRouting
    (ledger : ComponentResolvedBoundaryGapForestLedger
      axis hn2 hn3 hT root assignment) :
    (UnreservedBoundaryGapRoot axis hn2 hT ledger.forest ledger.rootPort ⊕
      (ReservedBoundaryGapRoot axis hn2 hT ledger.forest ledger.rootPort ⊕
        (ledger.forest.MergerSlot ⊕
          FullPrunedOuterCollision axis hn2 hn3 hT))) ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT where
  toFun
    | .inl a => ledger.unreservedRootEmbedding a
    | .inr (.inl a) => ledger.reservedInwardRootRouting a
    | .inr (.inr (.inl a)) => ledger.branchOwner a
    | .inr (.inr (.inr a)) => ledger.outerCollisionRouting a
  inj' := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (ledger.unreservedRootEmbedding.injective hab)
    · rcases b with b | b
      · exact False.elim (ledger.unreserved_reserved_disjoint a b hab)
      · rcases b with b | b
        · exact False.elim (ledger.unreserved_branch_disjoint a b hab)
        · exact False.elim (ledger.unreserved_outer_disjoint a b hab)
    · rcases a with a | a
      · exact False.elim (ledger.unreserved_reserved_disjoint b a hab.symm)
      · rcases a with a | a
        · exact False.elim (ledger.unreserved_branch_disjoint b a hab.symm)
        · exact False.elim (ledger.unreserved_outer_disjoint b a hab.symm)
    · rcases a with a | a <;> rcases b with b | b
      · exact congrArg (Sum.inr ∘ Sum.inl)
          (ledger.reservedInwardRootRouting.injective hab)
      · rcases b with b | b
        · exact False.elim (ledger.reserved_branch_disjoint a b hab)
        · exact False.elim (ledger.reserved_outer_disjoint a b hab)
      · rcases a with a | a
        · exact False.elim (ledger.reserved_branch_disjoint b a hab.symm)
        · exact False.elim (ledger.reserved_outer_disjoint b a hab.symm)
      · rcases a with a | a <;> rcases b with b | b
        · exact congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl)
            (ledger.branchOwner.injective hab)
        · exact False.elim (ledger.branch_outer_disjoint a b hab)
        · exact False.elim (ledger.branch_outer_disjoint b a hab.symm)
        · exact congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inr)
            (ledger.outerCollisionRouting.injective hab)

/-- Exact sound residual requirement `|I| + |O| ≤ U + J + K`, conditional on
genuine mutually disjoint embeddings. -/
theorem card_inward_add_outer_le_residual
    (ledger : ComponentResolvedBoundaryGapForestLedger
      axis hn2 hn3 hT root assignment) :
    Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) +
      Fintype.card (FullPrunedOuterCollision axis hn2 hn3 hT) ≤
      Fintype.card (UnreservedCanonicalBoundaryPort axis hn2 hT) +
        Fintype.card (BoundaryGapResidualInternalResource axis hn2 hn3 hT) +
          Fintype.card (BoundaryGapResidualComponentResource axis hn2 hn3 hT) := by
  let := ledger.carrierFintype
  let := ledger.carrierDecidableEq
  have hroute := Fintype.card_le_of_injective
    (ledger.residualRouting axis hn2 hn3 hT)
    (ledger.residualRouting axis hn2 hn3 hT).injective
  simp only [Fintype.card_sum] at hroute
  rw [ledger.forest.card_mergerSlot] at hroute
  have hstarts := ledger.card_starts_le_card_roots_add_branchExcess
    axis hn2 hn3 hT
  have hroots := ledger.card_roots_eq_unreserved_add_reserved axis hn2 hn3 hT
  omega

end ComponentResolvedBoundaryGapForestLedger

/-- Exact remaining geometric theorem for the concrete forest: classify roots,
then route both root classes, merger slots, and outer collisions injectively and
with disjoint images into residual physical resources. -/
def ComponentResolvedBoundaryGapForestRealizable
    (root : GridVertex n n)
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) : Prop :=
  Nonempty (ComponentResolvedBoundaryGapForestGeometry
    axis hn2 hn3 hT root assignment)

/-- Euler accounting for the canonical occurrence-labelled construction,
available before either missing geometric map is proved. -/
theorem fullPrunedComponentCotreeDual_card_starts_le
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) ≤
      (fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment).roots.card +
        (fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment).branchExcess :=
  (fullPrunedComponentCotreeDualHull_card_starts_eq
    axis hn2 hn3 hT assignment).le

/-- Resource pool of one collision's component-resolved minimal dual hull.
Outer collisions are demands and are not a target summand. -/
abbrev BoundaryGapForestResource (_root : GridVertex n n) :=
  BoundaryGapResidualPhysicalResource axis hn2 hn3 hT

/-! #### Legacy selected-subset hull accounting -/

/-- Restrict the canonical inward start leaves to an arbitrary selected set.
The resulting ancestor hull is the union of exactly those starts' minimal
parent chains; no ambient branch is counted merely because it exists. -/
noncomputable def fullPrunedComponentCotreeDualSubsetStartLeaf
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (S : Finset (FullPrunedInwardCollision axis hn2 hn3 hT)) :
    ↥S ↪ ↥((fullPrunedComponentCotreeDualForest
      axis hn2 hn3 hT assignment).leaves) where
  toFun collision := fullPrunedComponentCotreeDualStartLeaf
    axis hn2 hn3 hT assignment collision.1
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact (fullPrunedComponentCotreeDualStartLeaf
      axis hn2 hn3 hT assignment).injective hab

/-- The minimal component-split dual hull generated by an arbitrary subset of
inward sources. -/
noncomputable def fullPrunedComponentCotreeDualSubsetHullForest
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (S : Finset (FullPrunedInwardCollision axis hn2 hn3 hT)) :
    ParentForest ((fullPrunedComponentCotreeDualForest
      axis hn2 hn3 hT assignment).AncestorHull
        (fullPrunedComponentCotreeDualSubsetStartLeaf
          axis hn2 hn3 hT assignment S)) :=
  (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment)
    |>.ancestorHullForest
      (fullPrunedComponentCotreeDualSubsetStartLeaf axis hn2 hn3 hT assignment S)

/-- A root of a selected-subset hull is an ambient component-split dual root. -/
noncomputable def fullPrunedComponentCotreeDualSubsetHullRootEmbedding
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (S : Finset (FullPrunedInwardCollision axis hn2 hn3 hT)) :
    ↥((fullPrunedComponentCotreeDualSubsetHullForest
        axis hn2 hn3 hT assignment S).roots) ↪
      ↥((fullPrunedComponentCotreeDualForest
        axis hn2 hn3 hT assignment).roots) where
  toFun x := ⟨x.1.1,
    ((fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment)
      |>.mem_ancestorHullForest_roots_iff
        (fullPrunedComponentCotreeDualSubsetStartLeaf
          axis hn2 hn3 hT assignment S) x.1).mp x.2⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun x : ↥((fullPrunedComponentCotreeDualForest
        axis hn2 hn3 hT assignment).roots) => x.1) hab

/-- Physical port of a root retained by a selected-subset hull. -/
noncomputable def fullPrunedComponentCotreeDualSubsetHullRootPort
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (S : Finset (FullPrunedInwardCollision axis hn2 hn3 hT)) :
    ↥((fullPrunedComponentCotreeDualSubsetHullForest
        axis hn2 hn3 hT assignment S).roots) → GridCotreeOuterPort T :=
  fullPrunedComponentCotreeDualRootPort axis hn2 hn3 hT assignment ∘
    fullPrunedComponentCotreeDualSubsetHullRootEmbedding
      axis hn2 hn3 hT assignment S

/-- Exact selected-subset Euler ledger after quotienting occurrence roots by
their physical ports: starts are used ports plus duplicate roots plus branch
excess.  This includes the empty subset. -/
theorem fullPrunedComponentCotreeDualSubsetHull_card_starts_eq_grouped
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (S : Finset (FullPrunedInwardCollision axis hn2 hn3 hT)) :
    S.card =
      ((fullPrunedComponentCotreeDualSubsetHullForest
          axis hn2 hn3 hT assignment S).usedRootPorts
        (fullPrunedComponentCotreeDualSubsetHullRootPort
          axis hn2 hn3 hT assignment S)).card +
      (fullPrunedComponentCotreeDualSubsetHullForest
          axis hn2 hn3 hT assignment S).rootPortDebt
        (fullPrunedComponentCotreeDualSubsetHullRootPort
          axis hn2 hn3 hT assignment S) +
      (fullPrunedComponentCotreeDualSubsetHullForest
        axis hn2 hn3 hT assignment S).branchExcess := by
  let F := fullPrunedComponentCotreeDualSubsetHullForest
    axis hn2 hn3 hT assignment S
  let rootPort := fullPrunedComponentCotreeDualSubsetHullRootPort
    axis hn2 hn3 hT assignment S
  have heuler : Fintype.card ↥S = F.roots.card + F.branchExcess := by
    simpa [F, fullPrunedComponentCotreeDualSubsetHullForest] using
      (ParentForest.card_start_eq_card_ancestorHull_roots_add_branchExcess
        (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment)
        (fullPrunedComponentCotreeDualSubsetStartLeaf
          axis hn2 hn3 hT assignment S))
  have hroots : (F.usedRootPorts rootPort).card + F.rootPortDebt rootPort =
      F.roots.card := F.card_usedRootPorts_add_rootPortDebt rootPort
  have hgrouped : Fintype.card ↥S =
      (F.usedRootPorts rootPort).card + F.rootPortDebt rootPort +
        F.branchExcess := by omega
  simpa [F, rootPort] using hgrouped

/-- Source-local, jointly distinct witnesses in the union of a selected set's
minimal hull resources.  This is deliberately stronger than a cardinal target:
every witness records membership in its own source hull. -/
structure ComponentResolvedBoundaryGapHullExpansionWitness
    (root : GridVertex n n)
    (hullResources : FullPrunedOrderedCollision axis hn2 hn3 hT →
      Finset (BoundaryGapForestResource axis hn2 hn3 hT root))
    (S : Finset (FullPrunedOrderedCollision axis hn2 hn3 hT)) where
  resource : ↥S ↪ BoundaryGapForestResource axis hn2 hn3 hT root
  mem_source_hull : ∀ source, resource source ∈ hullResources source.1

/-- Legacy strong witness proposition for the superseded minimal-hull route.
Despite its name, this is already a source-local matching certificate, not a
topological hull-expansion theorem derivable from C1--C4. -/
def ComponentResolvedBoundaryGapHullExpansion
    (root : GridVertex n n)
    (_assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (hullResources : FullPrunedOrderedCollision axis hn2 hn3 hT →
      Finset (BoundaryGapForestResource axis hn2 hn3 hT root)) : Prop :=
  ∀ S : Finset (FullPrunedOrderedCollision axis hn2 hn3 hT),
    Nonempty (ComponentResolvedBoundaryGapHullExpansionWitness
      axis hn2 hn3 hT root hullResources S)

/-- Strong grouped C5 target. Unlike the global Euler bound above, this asks
for the resources in the union of the selected collisions' own minimal dual
hulls. It is Hall over grouped hulls, not pointwise freshness. -/
def ComponentResolvedBoundaryGapHullResidual
    (root : GridVertex n n)
    (_assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (hullResources : FullPrunedOrderedCollision axis hn2 hn3 hT →
      Finset (BoundaryGapForestResource axis hn2 hn3 hT root)) : Prop :=
  LocalizedHall hullResources

/-- Expanded form of the remaining grouped inequality. -/
theorem componentResolvedBoundaryGapHullResidual_iff
    (root : GridVertex n n)
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (hullResources : FullPrunedOrderedCollision axis hn2 hn3 hT →
      Finset (BoundaryGapForestResource axis hn2 hn3 hT root)) :
    ComponentResolvedBoundaryGapHullResidual axis hn2 hn3 hT root
        assignment hullResources ↔
      ∀ S : Finset (FullPrunedOrderedCollision axis hn2 hn3 hT),
        S.card ≤ (S.biUnion hullResources).card :=
  Iff.rfl

/-- Distinct source-local witnesses in every selected minimal-hull union prove
the grouped residual Hall inequalities directly.  No unrestricted matching or
global target-cardinality hypothesis is used. -/
theorem componentResolvedBoundaryGapHullResidual_of_expansion
    (root : GridVertex n n)
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (hullResources : FullPrunedOrderedCollision axis hn2 hn3 hT →
      Finset (BoundaryGapForestResource axis hn2 hn3 hT root))
    (hexpansion : ComponentResolvedBoundaryGapHullExpansion
      axis hn2 hn3 hT root assignment hullResources) :
    ComponentResolvedBoundaryGapHullResidual axis hn2 hn3 hT root
      assignment hullResources := by
  intro S
  let witness := Classical.choice (hexpansion S)
  let intoUnion : ↥S ↪ ↥(S.biUnion hullResources) :=
    { toFun := fun source => ⟨witness.resource source,
        Finset.mem_biUnion.mpr
          ⟨source.1, source.2, witness.mem_source_hull source⟩⟩
      inj' := fun a b hab => witness.resource.injective
        (congrArg Subtype.val hab) }
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective intoUnion intoUnion.injective

def PlanarLensGeometricEvent.rawResource?
    {root : GridVertex n n} :
    PlanarLensGeometricEvent axis hn2 hn3 hT root →
      Option (PlanarLensRawPhysicalResource (T := T))
  | .supportedOuterPort _ _ port => some (.inl port)
  | .retainedInternalSupportEdge _ _ edge => some (.inr (.inl edge))
  | .freeComponentContact _ _ contact => some (.inr (.inr contact.component))
  | .omittedEdgeContinuation _ _ _ => none

/-- The three canonical reservation ranges, viewed in the common raw physical
resource type.  This is deliberately a predicate on raw resources: an event is
not residual merely because it retained an occurrence label. -/
def PlanarLensRawPhysicalResource.IsCanonicallyReserved :
    PlanarLensRawPhysicalResource (T := T) → Prop
  | .inl port => port ∈ Set.range (exitEmbedding axis hn2 hT)
  | .inr (.inl edge) => edge ∈ Set.range (internalTreeEdgeTokenEmbedding
      (supportFinset (gridGraph n n \ T))
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT))
  | .inr (.inr component) => component ∈ Set.range (carrierQuotientEmbedding
      (FullPrunedTokenCarrier axis hn2 hn3 hT))

/-- A geometric event is genuinely residual only when it exposes a physical
resource outside all three canonical reservation ranges. -/
def PlanarLensGeometricEvent.IsResidual
    {root : GridVertex n n}
    (event : PlanarLensGeometricEvent axis hn2 hn3 hT root) : Prop :=
  ∃ raw, event.rawResource? axis hn2 hn3 hT = some raw ∧
    ¬raw.IsCanonicallyReserved axis hn2 hn3 hT

/-- Provenance-labelled use of the existing contour escape system.  `Source`
is retained even when several sources enter the same contour state. -/
structure PlanarLensSourceEscapeState
    (Source : Type*) (root : GridVertex n n) where
  source : Source
  state : PlanarLensRootEscapeState axis hn2 hn3 hT root

/-- Every source-labelled state reaches an occurrence-labelled geometric event
and preserves both source provenance and the original debt.  No freshness is
claimed for that event. -/
theorem planarLensSourceEscape_exists_event
    {Source : Type*} {root : GridVertex n n}
    (provenance : PlanarLensSourceEscapeState
      axis hn2 hn3 hT Source root) :
    ∃ terminal event,
      Relation.ReflTransGen
          (planarLensRootEscapeSystem axis hn2 hn3 hT root).Step
          provenance.state terminal ∧
        (planarLensRootEscapeSystem axis hn2 hn3 hT root).terminal terminal =
          some event ∧ terminal.origin = provenance.state.origin :=
  planarLensRootEscape_exists_event axis hn2 hn3 hT provenance.state

/-- Provenance states for reserved roots of a component-resolved boundary-gap
forest.  Constructing one still requires the geometric map from such a dual
root to a planar occurrence and original debt. -/
abbrev ReservedBoundaryGapRootEscapeState
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T)
    (root : GridVertex n n) :=
  PlanarLensSourceEscapeState axis hn2 hn3 hT
    (ReservedBoundaryGapRoot axis hn2 hT forest rootPort) root

/-- Legacy component-split launch hypothesis.  A reserved boundary-gap root
carries neither an original planar debt nor an inward occurrence, so no active
global-core construction should attempt to recover either from its port. -/
abbrev ReservedBoundaryGapRootEscapeLaunch
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (forest : ParentForest Carrier)
    (rootPort : ↥forest.roots → GridCotreeOuterPort T)
    (root : GridVertex n n) :=
  ReservedBoundaryGapRoot axis hn2 hT forest rootPort →
    PlanarLensRootEscapeState axis hn2 hn3 hT root

theorem reservedBoundaryGapRootEscape_exists_event
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    {forest : ParentForest Carrier}
    {rootPort : ↥forest.roots → GridCotreeOuterPort T}
    {root : GridVertex n n}
    (provenance : ReservedBoundaryGapRootEscapeState axis hn2 hn3 hT
      forest rootPort root) :
    ∃ terminal event,
      Relation.ReflTransGen
          (planarLensRootEscapeSystem axis hn2 hn3 hT root).Step
          provenance.state terminal ∧
        (planarLensRootEscapeSystem axis hn2 hn3 hT root).terminal terminal =
          some event ∧ terminal.origin = provenance.state.origin :=
  planarLensSourceEscape_exists_event axis hn2 hn3 hT provenance

/-- The raw resource at an outer collision's direct event is inside, not
outside, the canonical port reservation. -/
theorem FullPrunedOuterCollision.direct_raw_isCanonicallyReserved
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
    PlanarLensRawPhysicalResource.IsCanonicallyReserved axis hn2 hn3 hT
      (Sum.inl (collision.port axis hn2 hn3 hT) :
        PlanarLensRawPhysicalResource (T := T)) :=
  collision.port_mem_range_exitEmbedding axis hn2 hn3 hT

/-- Likewise, the chosen port of a reserved boundary-gap root is canonically
reserved.  It may classify the source, but cannot pay it residually. -/
theorem ReservedBoundaryGapRoot.port_raw_isCanonicallyReserved
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    {forest : ParentForest Carrier}
    {rootPort : ↥forest.roots → GridCotreeOuterPort T}
    (source : ReservedBoundaryGapRoot axis hn2 hT forest rootPort) :
    PlanarLensRawPhysicalResource.IsCanonicallyReserved axis hn2 hn3 hT
      (Sum.inl (rootPort source.1) :
        PlanarLensRawPhysicalResource (T := T)) :=
  source.2

/-- A residual event is usable by a provenance state only when the event is
actually reached and its raw resource is first-owned by the event occurrence.
This is the first geometric condition absent from the current contour system. -/
def PlanarLensSourceEscapeCanUse
    {Source : Type*} {root : GridVertex n n}
    (provenance : PlanarLensSourceEscapeState
      axis hn2 hn3 hT Source root)
    (raw : PlanarLensRawPhysicalResource (T := T)) : Prop :=
  ∃ terminal event,
    Relation.ReflTransGen
        (planarLensRootEscapeSystem axis hn2 hn3 hT root).Step
        provenance.state terminal ∧
      (planarLensRootEscapeSystem axis hn2 hn3 hT root).terminal terminal =
        some event ∧
      event.rawResource? axis hn2 hn3 hT = some raw ∧
      ¬raw.IsCanonicallyReserved axis hn2 hn3 hT ∧
      ∃ owned : PlanarLensRegionalOwned axis hn2 hT root
          provenance.state.occurrence,
        planarLensFirstOwnedResourceRaw axis hn2 hT owned.1 = raw

noncomputable def planarLensSourceEscapeResidualNeighborhood
    {Source : Type*} {root : GridVertex n n}
    (start : Source → PlanarLensSourceEscapeState
      axis hn2 hn3 hT Source root) (source : Source) :
    Finset (PlanarLensRawPhysicalResource (T := T)) :=
  Finset.univ.filter fun raw =>
    PlanarLensSourceEscapeCanUse axis hn2 hn3 hT (start source) raw

/-- Exact grouped geometric gate for genuine source routing.  By construction
it asks for residual first-owned events and does not assume unrestricted
terminal freshness. -/
def PlanarLensSourceResidualHall
    {Source : Type*} [Fintype Source] [DecidableEq Source]
    {root : GridVertex n n}
    (start : Source → PlanarLensSourceEscapeState
      axis hn2 hn3 hT Source root) : Prop :=
  LocalizedHall
    (planarLensSourceEscapeResidualNeighborhood axis hn2 hn3 hT start)

theorem planarLensSourceResidualHall_iff_nonempty_routing
    {Source : Type*} [Fintype Source] [DecidableEq Source]
    {root : GridVertex n n}
    (start : Source → PlanarLensSourceEscapeState
      axis hn2 hn3 hT Source root) :
    PlanarLensSourceResidualHall axis hn2 hn3 hT start ↔
      Nonempty (LocalizedRouting
        (planarLensSourceEscapeResidualNeighborhood axis hn2 hn3 hT start)) :=
  localizedHall_iff_nonempty_routing _

noncomputable def planarLensSourceResidualRoutingOfHall
    {Source : Type*} [Fintype Source] [DecidableEq Source]
    {root : GridVertex n n}
    (start : Source → PlanarLensSourceEscapeState
      axis hn2 hn3 hT Source root)
    (hHall : PlanarLensSourceResidualHall axis hn2 hn3 hT start) :
    LocalizedRouting
      (planarLensSourceEscapeResidualNeighborhood axis hn2 hn3 hT start) :=
  Classical.choice
    ((planarLensSourceResidualHall_iff_nonempty_routing
      axis hn2 hn3 hT start).mp hHall)

theorem planarLensSourceResidualRoutingOfHall_canUse
    {Source : Type*} [Fintype Source] [DecidableEq Source]
    {root : GridVertex n n}
    (start : Source → PlanarLensSourceEscapeState
      axis hn2 hn3 hT Source root)
    (hHall : PlanarLensSourceResidualHall axis hn2 hn3 hT start)
    (source : Source) :
    PlanarLensSourceEscapeCanUse axis hn2 hn3 hT (start source)
      (planarLensSourceResidualRoutingOfHall axis hn2 hn3 hT
        start hHall source) := by
  simpa [planarLensSourceEscapeResidualNeighborhood] using
    (planarLensSourceResidualRoutingOfHall axis hn2 hn3 hT
      start hHall).mem_neighborhood source

theorem planarLensSourceResidualRoutingOfHall_injective
    {Source : Type*} [Fintype Source] [DecidableEq Source]
    {root : GridVertex n n}
    (start : Source → PlanarLensSourceEscapeState
      axis hn2 hn3 hT Source root)
    (hHall : PlanarLensSourceResidualHall axis hn2 hn3 hT start) :
    Function.Injective
      (planarLensSourceResidualRoutingOfHall axis hn2 hn3 hT start hHall) :=
  (planarLensSourceResidualRoutingOfHall axis hn2 hn3 hT
    start hHall).toEmbedding.injective

/-- Distinct source occurrences receive disjoint raw resources.  In particular,
using a sum as `Source` proves cross-class disjointness as well as injectivity
inside each class. -/
theorem planarLensSourceResidualRoutingOfHall_disjoint
    {Source : Type*} [Fintype Source] [DecidableEq Source]
    {root : GridVertex n n}
    (start : Source → PlanarLensSourceEscapeState
      axis hn2 hn3 hT Source root)
    (hHall : PlanarLensSourceResidualHall axis hn2 hn3 hT start)
    {source other : Source} (hne : source ≠ other) :
    planarLensSourceResidualRoutingOfHall axis hn2 hn3 hT
        start hHall source ≠
      planarLensSourceResidualRoutingOfHall axis hn2 hn3 hT
        start hHall other := by
  intro heq
  exact hne (planarLensSourceResidualRoutingOfHall_injective
    axis hn2 hn3 hT start hHall heq)

/-! #### Canonical minimal-hull grouped residual Hall -/

/-- One physical-separator obligation for each merger-slot occurrence.  Equal
first separators do not identify these values: each occurrence must be matched
to a distinct member of its concrete physical neighborhood. -/
structure CanonicalGroupedSeparatorOccurrenceObligation
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) where
  slot : (fullPrunedComponentCotreeDualHullForest
    axis hn2 hn3 hT assignment).MergerSlot

noncomputable instance canonicalGroupedSeparatorOccurrenceObligationFintype
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    Fintype (CanonicalGroupedSeparatorOccurrenceObligation
      axis hn2 hn3 hT assignment) :=
  Fintype.ofEquiv
    (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot
    { toFun := fun slot => ⟨slot⟩
      invFun := CanonicalGroupedSeparatorOccurrenceObligation.slot
      left_inv := fun _ => rfl
      right_inv := fun obligation => by cases obligation; rfl }

instance canonicalGroupedSeparatorOccurrenceObligationDecidableEq
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    DecidableEq (CanonicalGroupedSeparatorOccurrenceObligation
      axis hn2 hn3 hT assignment) := fun a b =>
  decidable_of_iff (a.slot = b.slot) ⟨fun h => by cases a; cases b; cases h; rfl,
    congrArg CanonicalGroupedSeparatorOccurrenceObligation.slot⟩

/-- The exact physical child from which a grouped merger-slot obligation starts
its canonical separator walk. -/
noncomputable def canonicalGroupedSeparatorOccurrenceSource
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (obligation : CanonicalGroupedSeparatorOccurrenceObligation
      axis hn2 hn3 hT assignment) :
    {x : FullPrunedComponentCotreeDualHullCarrier axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x} :=
  (fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
    |>.mergerSlotPhysicalChildEmbedding
      (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
      (fullPrunedComponentCotreeDualHull_nonphysicalChildren_card_le_one
        axis hn2 hn3 hT assignment) obligation.slot

/-- A grouped obligation that terminates at a reserved boundary retains both
the original merger-slot occurrence and the exact terminal path provenance. -/
structure CanonicalGroupedSeparatorReservedTerminalProvenance
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) where
  obligation : CanonicalGroupedSeparatorOccurrenceObligation
    axis hn2 hn3 hT assignment
  remaining : CanonicalHullFirstSeparatingRemainingCase
    axis hn2 hn3 hT assignment
      (canonicalGroupedSeparatorOccurrenceSource
        axis hn2 hn3 hT assignment obligation)
  result_eq : canonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment
      (canonicalGroupedSeparatorOccurrenceSource
        axis hn2 hn3 hT assignment obligation) = .remaining remaining

/-- Every grouped merger-slot occurrence is resolved by the actual minimal-hull
parent path.  It receives either its genuine singleton residual neighborhood or
an exact reserved terminal carrying the same occurrence as provenance. -/
theorem canonicalGroupedSeparatorOccurrence_residual_or_reservedTerminal
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (obligation : CanonicalGroupedSeparatorOccurrenceObligation
      axis hn2 hn3 hT assignment) :
    (canonicalActiveBranchNeighborhood axis hn2 hn3 hT assignment
      (canonicalHullFirstSeparatingClassification axis hn2 hn3 hT assignment)
      obligation.slot).Nonempty ∨
      ∃ terminal : CanonicalGroupedSeparatorReservedTerminalProvenance
          axis hn2 hn3 hT assignment,
        terminal.obligation = obligation := by
  classical
  let source := canonicalGroupedSeparatorOccurrenceSource
    axis hn2 hn3 hT assignment obligation
  cases hresult : canonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment source with
  | residual candidate =>
      left
      refine ⟨canonicalHullFirstSeparatingCandidateEquiv
        axis hn2 hn3 hT candidate, ?_⟩
      change canonicalHullFirstSeparatingCandidateEquiv
          axis hn2 hn3 hT candidate ∈
        match canonicalHullFirstSeparatingClassification
            axis hn2 hn3 hT assignment source with
        | .residual candidate =>
            {canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate}
        | .remaining _ => ∅
      simp [hresult]
  | remaining remaining =>
      right
      exact ⟨
        { obligation := obligation
          remaining := remaining
          result_eq := hresult }, rfl⟩

/-- The terminal alternative above is genuinely a reserved-source obligation:
its endpoint is reached along the certified canonical chain and its physical
port lies in the canonical exit reservation. -/
theorem CanonicalGroupedSeparatorReservedTerminalProvenance.is_reserved_source
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    (terminal : CanonicalGroupedSeparatorReservedTerminalProvenance
      axis hn2 hn3 hT assignment) :
    Relation.ReflTransGen
        (fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).ParentStep
        (canonicalGroupedSeparatorOccurrenceSource
          axis hn2 hn3 hT assignment terminal.obligation).1
        terminal.remaining.terminal ∧
      terminal.remaining.port ∈ Set.range (exitEmbedding axis hn2 hT) :=
  ⟨terminal.remaining.reached, terminal.remaining.reserved⟩

/-- The four genuinely unresolved source classes in the canonical grouped
minimal-hull ledger.  Used unreserved ports and compatible duplicate slots do
not occur here, since their physical embeddings are canonical. -/
abbrev CanonicalGroupedResidualSource
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  let realization := fullPrunedComponentCotreeDualRealization
    axis hn2 hn3 hT assignment
  let rootPort := fullPrunedComponentCotreeDualHullRootPort
    axis hn2 hn3 hT assignment
  ReservedBoundaryGapUsedRootPort axis hn2 hT realization.forest rootPort ⊕
    (IncompatibleBoundaryGapRootPortDebtSlot
      axis hn2 hn3 hT realization rootPort ⊕
      (CanonicalGroupedSeparatorOccurrenceObligation
        axis hn2 hn3 hT assignment ⊕
        FullPrunedOuterCollision axis hn2 hn3 hT))

noncomputable instance canonicalGroupedResidualSourceFintype
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    Fintype (CanonicalGroupedResidualSource axis hn2 hn3 hT assignment) := by
  unfold CanonicalGroupedResidualSource
  dsimp only
  unfold IncompatibleBoundaryGapRootPortDebtSlot ParentForest.RootPortDebtSlot
  infer_instance

/-- The two routes already installed before residual Hall is invoked.  Their
sum is injective because ports and duplicate components occupy different
physical summands. -/
noncomputable def canonicalGroupedAutomaticEmbedding
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    (UnreservedBoundaryGapUsedRootPort axis hn2 hT
        (fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
        (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment) ⊕
      CompatibleBoundaryGapRootPortDebtSlot axis hn2 hn3 hT
        (fullPrunedComponentCotreeDualRealization axis hn2 hn3 hT assignment)
        (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment)) ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT where
  toFun
    | .inl port => unreservedBoundaryGapUsedRootPortEmbedding
        axis hn2 hn3 hT _ _ port
    | .inr slot => compatibleBoundaryGapRootPortDebtEmbedding
        axis hn2 hn3 hT _ _ slot
  inj' := by
    intro a b
    rcases a with a | a
    · rcases b with b | b
      · intro hab
        exact congrArg Sum.inl
          ((unreservedBoundaryGapUsedRootPortEmbedding
            axis hn2 hn3 hT _ _).injective hab)
      · exact False.elim b.2
    · exact False.elim a.2

/-- A residual resource is still free after installing the automatic
unreserved-port and compatible-duplicate routes. -/
def CanonicalGroupedResidualResource.IsAvailable
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (resource : BoundaryGapResidualPhysicalResource axis hn2 hn3 hT) : Prop :=
  resource ∉ Set.range (canonicalGroupedAutomaticEmbedding
    axis hn2 hn3 hT assignment)

/-- All inward collision occurrences whose occurrence-split dual parent path
reaches a given active hull root.  This is the provenance fiber carried by the
root; no representative source is selected. -/
noncomputable def canonicalHullRootAssociatedInwardCandidates
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots)) :
    Finset (FullPrunedInwardCollision axis hn2 hn3 hT) :=
  Finset.univ.filter fun collision =>
    Relation.ReflTransGen
      (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment).ParentStep
      (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment collision).1
      activeRoot.1.1

@[simp] theorem mem_canonicalHullRootAssociatedInwardCandidates
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (collision : FullPrunedInwardCollision axis hn2 hn3 hT) :
    collision ∈ canonicalHullRootAssociatedInwardCandidates
        axis hn2 hn3 hT assignment activeRoot ↔
      Relation.ReflTransGen
        (fullPrunedComponentCotreeDualForest axis hn2 hn3 hT assignment).ParentStep
        (fullPrunedComponentCotreeDualStartLeaf axis hn2 hn3 hT assignment collision).1
        activeRoot.1.1 := by
  classical
  simp [canonicalHullRootAssociatedInwardCandidates]

/-- Every active hull root has a nonempty inward-source association fiber. -/
theorem canonicalHullRootAssociatedInwardCandidates_nonempty
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots)) :
    (canonicalHullRootAssociatedInwardCandidates
      axis hn2 hn3 hT assignment activeRoot).Nonempty := by
  classical
  obtain ⟨collision, hreaches⟩ := activeRoot.1.2
  exact ⟨collision, (mem_canonicalHullRootAssociatedInwardCandidates
    axis hn2 hn3 hT assignment activeRoot collision).2 hreaches⟩

/-- All active hull roots over a used physical port.  Keeping the whole fiber
avoids an arbitrary classification root for reserved ports and duplicate debt. -/
noncomputable def canonicalHullRootsAtUsedPort
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (port : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).usedRootPorts
        (fullPrunedComponentCotreeDualHullRootPort
          axis hn2 hn3 hT assignment))) :
    Finset ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots) :=
  Finset.univ.filter fun activeRoot =>
    fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
      activeRoot = port.1

@[simp] theorem mem_canonicalHullRootsAtUsedPort
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (port : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).usedRootPorts
        (fullPrunedComponentCotreeDualHullRootPort
          axis hn2 hn3 hT assignment)))
    (activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots)) :
    activeRoot ∈ canonicalHullRootsAtUsedPort axis hn2 hn3 hT assignment port ↔
      fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
        activeRoot = port.1 := by
  classical
  simp [canonicalHullRootsAtUsedPort]

/-- A used port has at least one active hull root in its association fiber. -/
theorem canonicalHullRootsAtUsedPort_nonempty
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (port : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).usedRootPorts
        (fullPrunedComponentCotreeDualHullRootPort
          axis hn2 hn3 hT assignment))) :
    (canonicalHullRootsAtUsedPort axis hn2 hn3 hT assignment port).Nonempty := by
  classical
  obtain ⟨activeRoot, _, hport⟩ := Finset.mem_image.mp port.2
  exact ⟨activeRoot, (mem_canonicalHullRootsAtUsedPort
    axis hn2 hn3 hT assignment port activeRoot).2 hport⟩

/-- Direct occurrence-split dual provenance of an outer-germ collision.  No
`PlanarInwardLensOccurrence` is asserted or manufactured. -/
structure FullPrunedOuterCollisionDualProvenance
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) where
  occurrence : ComponentOmittedEdgeOccurrence axis hn2 hT
    (fullPrunedCollisionEnrichedToken axis hn2 hn3 hT collision.1).component

noncomputable def fullPrunedOuterCollisionDualProvenance
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
    FullPrunedOuterCollisionDualProvenance axis hn2 hn3 hT collision where
  occurrence := componentSpatialGapEquivOrdinarySumDuplicatedCorner
    axis hn2 hT _ (fullPrunedCollisionSpatialGap axis hn2 hn3 hT collision.1)

/-- Outer collisions require a first separator on their own occurrence-split
dual branch.  This is the honest geometric input replacing an impossible inward
launch of their rank-zero outer direct germ. -/
abbrev CanonicalOuterCollisionFirstSeparatingClassification :=
  (collision : FullPrunedOuterCollision axis hn2 hn3 hT) →
    FullPrunedOuterCollisionDualProvenance axis hn2 hn3 hT collision →
      CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT

noncomputable def canonicalGroupedRootEscapeNeighborhood
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (port : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).usedRootPorts
        (fullPrunedComponentCotreeDualHullRootPort
          axis hn2 hn3 hT assignment))) :
    Finset (BoundaryGapResidualPhysicalResource axis hn2 hn3 hT) :=
  (canonicalHullRootsAtUsedPort axis hn2 hn3 hT assignment port).biUnion
    fun activeRoot =>
      (canonicalHullRootAssociatedInwardCandidates
        axis hn2 hn3 hT assignment activeRoot).biUnion fun _collision =>
          let active : {x : FullPrunedComponentCotreeDualHullCarrier
              axis hn2 hn3 hT assignment //
            FullPrunedComponentCotreeDualHullCarrier.IsPhysical
              (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x} :=
            ⟨activeRoot.1, by trivial⟩
          match firstSeparating active with
          | .residual candidate =>
              {canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate}
          | .remaining _ => ∅

/-- A residual classification at any associated active root supplies a member
of the used-port neighborhood. -/
theorem mem_canonicalGroupedRootEscapeNeighborhood_of_residual
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (port : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).usedRootPorts
        (fullPrunedComponentCotreeDualHullRootPort
          axis hn2 hn3 hT assignment)))
    (activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (hroot : fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
      activeRoot = port.1)
    (candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (hresidual : firstSeparating ⟨activeRoot.1, by trivial⟩ = .residual candidate) :
    canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate ∈
      canonicalGroupedRootEscapeNeighborhood axis hn2 hn3 hT assignment
        firstSeparating port := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨activeRoot, (mem_canonicalHullRootsAtUsedPort
    axis hn2 hn3 hT assignment port activeRoot).2 hroot, ?_⟩
  apply Finset.mem_biUnion.mpr
  obtain ⟨collision, hcollision⟩ :=
    canonicalHullRootAssociatedInwardCandidates_nonempty
      axis hn2 hn3 hT assignment activeRoot
  refine ⟨collision, hcollision, ?_⟩
  simp [hresidual]

/-- Hence the used-port neighborhood is nonempty whenever one associated root
has a proved residual first separator. -/
theorem canonicalGroupedRootEscapeNeighborhood_nonempty_of_residual
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (port : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).usedRootPorts
        (fullPrunedComponentCotreeDualHullRootPort
          axis hn2 hn3 hT assignment)))
    (activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (hroot : fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
      activeRoot = port.1)
    (candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (hresidual : firstSeparating ⟨activeRoot.1, by trivial⟩ = .residual candidate) :
    (canonicalGroupedRootEscapeNeighborhood axis hn2 hn3 hT assignment
      firstSeparating port).Nonempty :=
  ⟨canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate,
    mem_canonicalGroupedRootEscapeNeighborhood_of_residual
      axis hn2 hn3 hT assignment firstSeparating port activeRoot hroot candidate hresidual⟩

/-- Exact obstruction to nonemptiness of the unfiltered used-port union.  The
inward-collision fiber over every active root is nonempty, so the union is
nonempty exactly when one active root over the port has a residual first
separator. -/
theorem canonicalGroupedRootEscapeNeighborhood_nonempty_iff
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (port : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).usedRootPorts
        (fullPrunedComponentCotreeDualHullRootPort
          axis hn2 hn3 hT assignment))) :
    (canonicalGroupedRootEscapeNeighborhood axis hn2 hn3 hT assignment
      firstSeparating port).Nonempty ↔
      ∃ activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).roots),
        fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
            activeRoot = port.1 ∧
          ∃ candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT,
            firstSeparating ⟨activeRoot.1, by trivial⟩ = .residual candidate := by
  classical
  constructor
  · rintro ⟨resource, hresource⟩
    rw [canonicalGroupedRootEscapeNeighborhood] at hresource
    obtain ⟨activeRoot, hroot, hresource⟩ := Finset.mem_biUnion.mp hresource
    obtain ⟨_collision, _hcollision, hresource⟩ :=
      Finset.mem_biUnion.mp hresource
    have hport := (mem_canonicalHullRootsAtUsedPort
      axis hn2 hn3 hT assignment port activeRoot).1 hroot
    cases hresult : firstSeparating ⟨activeRoot.1, by trivial⟩ with
    | residual candidate => exact ⟨activeRoot, hport, candidate, hresult⟩
    | remaining exception => simp [hresult] at hresource
  · rintro ⟨activeRoot, hroot, candidate, hresidual⟩
    exact canonicalGroupedRootEscapeNeighborhood_nonempty_of_residual
      axis hn2 hn3 hT assignment firstSeparating port activeRoot hroot
        candidate hresidual

noncomputable def canonicalOuterCollisionNeighborhood
    (firstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
    Finset (BoundaryGapResidualPhysicalResource axis hn2 hn3 hT) :=
  {canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT
    (firstSeparating collision
      (fullPrunedOuterCollisionDualProvenance axis hn2 hn3 hT collision))}

/-- A supplied legacy classification determines a singleton outer-collision
candidate.  This proves no availability or canonical classification theorem. -/
@[simp] theorem canonicalOuterCollisionNeighborhood_nonempty
    (firstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
    (canonicalOuterCollisionNeighborhood axis hn2 hn3 hT
      firstSeparating collision).Nonempty := by
  simp [canonicalOuterCollisionNeighborhood]

@[simp] theorem card_canonicalOuterCollisionNeighborhood
    (firstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
    (canonicalOuterCollisionNeighborhood axis hn2 hn3 hT
      firstSeparating collision).card = 1 := by
  simp [canonicalOuterCollisionNeighborhood]

/-- Physically admissible resources for each remaining source.  Escape sources
must reach a residual first-owned event with their source label intact; active
merger slots must select one of their realized first separators.  Every branch
also excludes resources consumed by the two automatic embeddings. -/
noncomputable def canonicalGroupedResidualNeighborhood
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (source : CanonicalGroupedResidualSource axis hn2 hn3 hT assignment) :
    Finset (BoundaryGapResidualPhysicalResource axis hn2 hn3 hT) :=
  Finset.univ.filter fun resource =>
    CanonicalGroupedResidualResource.IsAvailable
      axis hn2 hn3 hT assignment resource ∧
      match source with
      | .inl port => resource ∈ canonicalGroupedRootEscapeNeighborhood
          axis hn2 hn3 hT assignment firstSeparating port.1
      | .inr (.inl slot) => resource ∈ canonicalGroupedRootEscapeNeighborhood
          axis hn2 hn3 hT assignment firstSeparating slot.1.1
      | .inr (.inr (.inl obligation)) => resource ∈
          canonicalActiveBranchNeighborhood axis hn2 hn3 hT assignment
            firstSeparating obligation.slot
      | .inr (.inr (.inr collision)) => resource ∈
          canonicalOuterCollisionNeighborhood axis hn2 hn3 hT
            outerFirstSeparating collision

/-- With the current physical-neighborhood relation, a separator occurrence
whose canonical hull child returns `candidate` can use no resource other than
that candidate.  The availability filter may remove it, but cannot add a
downstream root- or branch-debt resource. -/
theorem canonicalGroupedResidualNeighborhood_separatorOccurrence_subset_singleton
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot)
    (candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (hseparator :
      firstSeparating
          ((fullPrunedComponentCotreeDualHullForest
            axis hn2 hn3 hT assignment).mergerSlotPhysicalChildEmbedding
              (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
                (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
              (fullPrunedComponentCotreeDualHull_nonphysicalChildren_card_le_one
                axis hn2 hn3 hT assignment) slot) =
        .residual candidate) :
    canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
        firstSeparating outerFirstSeparating
        (.inr (.inr (.inl
          (⟨slot⟩ : CanonicalGroupedSeparatorOccurrenceObligation
            axis hn2 hn3 hT assignment)))) ⊆
      {canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate} := by
  classical
  intro resource hresource
  have hbranch := (Finset.mem_filter.mp hresource).2.2
  simpa [canonicalActiveBranchNeighborhood, hseparator] using hbranch

/-- Exact shared-separator multiplicity obstruction for the current grouped
neighborhoods.  Two distinct merger-slot occurrences with the same realized
physical separator violate the two-element Hall inequality, even though the
minimal-hull Euler ledger counts both branch-excess occurrences.  Consequently
the missing multiplicity lemma must enlarge at least one occurrence's concrete
neighborhood by an additional downstream root/branch-debt resource; the Euler
cardinality identity alone cannot prove grouped Hall. -/
theorem not_localizedHall_canonicalGroupedResidualNeighborhood_of_shared_separatorOccurrences
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    {a b : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot}
    (hab : a ≠ b)
    (candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (ha :
      firstSeparating
          ((fullPrunedComponentCotreeDualHullForest
            axis hn2 hn3 hT assignment).mergerSlotPhysicalChildEmbedding
              (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
                (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
              (fullPrunedComponentCotreeDualHull_nonphysicalChildren_card_le_one
                axis hn2 hn3 hT assignment) a) =
        .residual candidate)
    (hb :
      firstSeparating
          ((fullPrunedComponentCotreeDualHullForest
            axis hn2 hn3 hT assignment).mergerSlotPhysicalChildEmbedding
              (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
                (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
              (fullPrunedComponentCotreeDualHull_nonphysicalChildren_card_le_one
                axis hn2 hn3 hT assignment) b) =
        .residual candidate) :
    ¬LocalizedHall (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT
      assignment firstSeparating outerFirstSeparating) := by
  classical
  let source : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot →
      CanonicalGroupedResidualSource axis hn2 hn3 hT assignment := fun slot =>
    .inr (.inr (.inl ⟨slot⟩))
  have hsource : source a ≠ source b := by
    intro h
    apply hab
    exact congrArg CanonicalGroupedSeparatorOccurrenceObligation.slot
      (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h)))
  intro hHall
  have hselected := hHall ({source a, source b} : Finset
    (CanonicalGroupedResidualSource axis hn2 hn3 hT assignment))
  have hunion :
      ({source a, source b} : Finset
          (CanonicalGroupedResidualSource axis hn2 hn3 hT assignment)).biUnion
          (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
            firstSeparating outerFirstSeparating) ⊆
        {canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate} := by
    intro resource hresource
    obtain ⟨selected, hselectedMem, hresource⟩ :=
      Finset.mem_biUnion.mp hresource
    simp only [Finset.mem_insert, Finset.mem_singleton] at hselectedMem
    rcases hselectedMem with rfl | rfl
    · exact canonicalGroupedResidualNeighborhood_separatorOccurrence_subset_singleton
        axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating a
          candidate ha hresource
    · exact canonicalGroupedResidualNeighborhood_separatorOccurrence_subset_singleton
        axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating b
          candidate hb hresource
  have hunionCard :
      (({source a, source b} : Finset
          (CanonicalGroupedResidualSource axis hn2 hn3 hT assignment)).biUnion
          (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
            firstSeparating outerFirstSeparating)).card ≤ 1 := by
    simpa using Finset.card_le_card hunion
  have hselectedCard :
      ({source a, source b} : Finset
        (CanonicalGroupedResidualSource axis hn2 hn3 hT assignment)).card = 2 := by
    simp [hsource]
  omega

/-- After freshness against the automatic routes is proved, an outer source has
exactly its provenance-classified first separator as grouped neighborhood. -/
theorem canonicalGroupedResidualNeighborhood_outer_eq_singleton
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT)
    (havailable : CanonicalGroupedResidualResource.IsAvailable
      axis hn2 hn3 hT assignment
      (canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT
        (outerFirstSeparating collision
          (fullPrunedOuterCollisionDualProvenance
            axis hn2 hn3 hT collision)))) :
    canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
        firstSeparating outerFirstSeparating (.inr (.inr (.inr collision))) =
      {canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT
        (outerFirstSeparating collision
          (fullPrunedOuterCollisionDualProvenance
            axis hn2 hn3 hT collision))} := by
  classical
  ext resource
  constructor
  · intro hresource
    exact (Finset.mem_filter.mp hresource).2.2
  · intro hresource
    have heq := Finset.mem_singleton.mp hresource
    subst resource
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨havailable, ?_⟩⟩
    simp [canonicalOuterCollisionNeighborhood]

/-- In particular, the proof-carrying outer classification and freshness proof
discharge singleton availability without a separate Hall assumption. -/
theorem canonicalGroupedResidualNeighborhood_outer_nonempty
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT)
    (havailable : CanonicalGroupedResidualResource.IsAvailable
      axis hn2 hn3 hT assignment
      (canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT
        (outerFirstSeparating collision
          (fullPrunedOuterCollisionDualProvenance
            axis hn2 hn3 hT collision)))) :
    (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating
      (.inr (.inr (.inr collision)))).Nonempty := by
  rw [canonicalGroupedResidualNeighborhood_outer_eq_singleton
    axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating
    collision havailable]
  exact Finset.singleton_nonempty _

/-- Every unresolved source neighborhood is separated from both automatic
routes.  This is the displayed availability filter, stated as a reusable API. -/
theorem canonicalGroupedResidualNeighborhood_not_mem_automaticRange
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (source : CanonicalGroupedResidualSource axis hn2 hn3 hT assignment)
    {resource : BoundaryGapResidualPhysicalResource axis hn2 hn3 hT}
    (hresource : resource ∈ canonicalGroupedResidualNeighborhood
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating source) :
    resource ∉ Set.range (canonicalGroupedAutomaticEmbedding
      axis hn2 hn3 hT assignment) := by
  exact (Finset.mem_filter.mp hresource).2.1

/-- Exact obstruction after filtering a used-port association union by
availability.  This isolates the extra fact not supplied by root escape
termination: the residual first separator must avoid the automatic image. -/
private theorem canonicalGroupedAvailableRootEscapeNeighborhood_nonempty_iff
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (port : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).usedRootPorts
        (fullPrunedComponentCotreeDualHullRootPort
          axis hn2 hn3 hT assignment))) :
    ((Finset.univ.filter fun resource =>
      CanonicalGroupedResidualResource.IsAvailable axis hn2 hn3 hT
          assignment resource ∧
        resource ∈ canonicalGroupedRootEscapeNeighborhood
          axis hn2 hn3 hT assignment firstSeparating port)).Nonempty ↔
      ∃ activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).roots),
        fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
            activeRoot = port.1 ∧
          ∃ candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT,
            firstSeparating ⟨activeRoot.1, by trivial⟩ = .residual candidate ∧
              CanonicalGroupedResidualResource.IsAvailable axis hn2 hn3 hT
                assignment (canonicalHullFirstSeparatingCandidateEquiv
                  axis hn2 hn3 hT candidate) := by
  classical
  constructor
  · rintro ⟨resource, hresource⟩
    obtain ⟨_, havailable, hresource⟩ := Finset.mem_filter.mp hresource
    rw [canonicalGroupedRootEscapeNeighborhood] at hresource
    obtain ⟨activeRoot, hrootMem, hresource⟩ := Finset.mem_biUnion.mp hresource
    obtain ⟨_collision, _hcollision, hresource⟩ :=
      Finset.mem_biUnion.mp hresource
    have hroot := (mem_canonicalHullRootsAtUsedPort
      axis hn2 hn3 hT assignment port activeRoot).1 hrootMem
    cases hresidual : firstSeparating ⟨activeRoot.1, by trivial⟩ with
    | residual candidate =>
        have heq : resource = canonicalHullFirstSeparatingCandidateEquiv
            axis hn2 hn3 hT candidate := by
          simpa [hresidual] using hresource
        exact ⟨activeRoot, hroot, candidate, hresidual, heq ▸ havailable⟩
    | remaining exception => simp [hresidual] at hresource
  · rintro ⟨activeRoot, hroot, candidate, hresidual, havailable⟩
    refine ⟨canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, havailable, ?_⟩⟩
    exact mem_canonicalGroupedRootEscapeNeighborhood_of_residual
      axis hn2 hn3 hT assignment firstSeparating port activeRoot hroot
        candidate hresidual

/-- Exact singleton obstruction for a reserved used port.  Association fibers
and their inward provenance are already nonempty; what remains is one residual
classification whose resource is not consumed by an automatic route. -/
theorem canonicalGroupedResidualNeighborhood_reservedUsedPort_nonempty_iff
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (source : ReservedBoundaryGapUsedRootPort axis hn2 hT
      (fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
      (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment)) :
    (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating (.inl source)).Nonempty ↔
      ∃ activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).roots),
        fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
            activeRoot = source.1.1 ∧
          ∃ candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT,
            firstSeparating ⟨activeRoot.1, by trivial⟩ = .residual candidate ∧
              CanonicalGroupedResidualResource.IsAvailable axis hn2 hn3 hT
                assignment (canonicalHullFirstSeparatingCandidateEquiv
                  axis hn2 hn3 hT candidate) := by
  simpa only [canonicalGroupedResidualNeighborhood] using
    (canonicalGroupedAvailableRootEscapeNeighborhood_nonempty_iff
      axis hn2 hn3 hT assignment firstSeparating source.1)

/-- Incompatible duplicate slots use the same complete active-root association
fiber as their underlying used port.  Their neighborhood is nonempty under
exactly the same residual-and-available condition. -/
theorem canonicalGroupedResidualNeighborhood_incompatibleDuplicate_nonempty_iff
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (source : IncompatibleBoundaryGapRootPortDebtSlot axis hn2 hn3 hT
      (fullPrunedComponentCotreeDualRealization axis hn2 hn3 hT assignment)
      (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment)) :
    (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating (.inr (.inl source))).Nonempty ↔
      ∃ activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).roots),
        fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
            activeRoot = source.1.1.1 ∧
          ∃ candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT,
            firstSeparating ⟨activeRoot.1, by trivial⟩ = .residual candidate ∧
              CanonicalGroupedResidualResource.IsAvailable axis hn2 hn3 hT
                assignment (canonicalHullFirstSeparatingCandidateEquiv
                  axis hn2 hn3 hT candidate) := by
  classical
  simpa only [canonicalGroupedResidualNeighborhood] using
    (canonicalGroupedAvailableRootEscapeNeighborhood_nonempty_iff
      axis hn2 hn3 hT assignment firstSeparating source.1.1)

/-- An associated active root and a fresh residual hull continuation directly
pay a reserved used port.  No planar escape state is introduced: the used port
itself need not carry an inward planar occurrence. -/
theorem canonicalGroupedResidualNeighborhood_reservedUsedPort_nonempty_of_continuation
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (source : ReservedBoundaryGapUsedRootPort axis hn2 hT
      (fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
      (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment))
    (activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (hroot : fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
      activeRoot = source.1.1)
    (candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (hresidual : firstSeparating ⟨activeRoot.1, by trivial⟩ = .residual candidate)
    (havailable : CanonicalGroupedResidualResource.IsAvailable
      axis hn2 hn3 hT assignment
      (canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate)) :
    (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating (.inl source)).Nonempty :=
  (canonicalGroupedResidualNeighborhood_reservedUsedPort_nonempty_iff
    axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating source).2
      ⟨activeRoot, hroot, candidate, hresidual, havailable⟩

/-- Incompatible duplicate debt uses the same active-root association and hull
continuation as its underlying used port, again without manufacturing a planar
inward occurrence for the duplicate source. -/
theorem canonicalGroupedResidualNeighborhood_incompatibleDuplicate_nonempty_of_continuation
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (source : IncompatibleBoundaryGapRootPortDebtSlot axis hn2 hn3 hT
      (fullPrunedComponentCotreeDualRealization axis hn2 hn3 hT assignment)
      (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment))
    (activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (hroot : fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
      activeRoot = source.1.1.1)
    (candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (hresidual : firstSeparating ⟨activeRoot.1, by trivial⟩ = .residual candidate)
    (havailable : CanonicalGroupedResidualResource.IsAvailable
      axis hn2 hn3 hT assignment
      (canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate)) :
    (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating (.inr (.inl source))).Nonempty :=
  (canonicalGroupedResidualNeighborhood_incompatibleDuplicate_nonempty_iff
    axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating source).2
      ⟨activeRoot, hroot, candidate, hresidual, havailable⟩

/-- A fresh residual first separator of the physical merger child supplies the
singleton availability required by its grouped branch obligation. -/
theorem canonicalGroupedResidualNeighborhood_branch_nonempty_of_continuation
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (obligation : CanonicalGroupedSeparatorOccurrenceObligation
      axis hn2 hn3 hT assignment)
    (candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT)
    (hresidual : firstSeparating
      ⟨canonicalHullMergerSlotChild axis hn2 hn3 hT assignment obligation.slot,
        by trivial⟩ = .residual candidate)
    (havailable : CanonicalGroupedResidualResource.IsAvailable
      axis hn2 hn3 hT assignment
      (canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate)) :
    (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating
      (.inr (.inr (.inl obligation)))).Nonempty := by
  classical
  refine ⟨canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, havailable, ?_⟩
  have hresidual' : firstSeparating
      (((fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
        |>.mergerSlotPhysicalChildEmbedding
          (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
            (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
          (fullPrunedComponentCotreeDualHull_nonphysicalChildren_card_le_one
            axis hn2 hn3 hT assignment)) obligation.slot) =
        .residual candidate := hresidual
  simp [canonicalActiveBranchNeighborhood, hresidual']

/-- The four source-local geometric inputs prove singleton availability for the
entire unresolved sum.  Reserved ports and incompatible duplicates are handled
only through active-root association and hull continuation; outer collisions
use their own occurrence-split dual separator. -/
theorem canonicalGroupedResidualNeighborhood_all_nonempty
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (hreserved : ∀ source : ReservedBoundaryGapUsedRootPort axis hn2 hT
        (fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
        (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment),
      ∃ activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).roots),
        fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
            activeRoot = source.1.1 ∧
          ∃ candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT,
            firstSeparating ⟨activeRoot.1, by trivial⟩ = .residual candidate ∧
              CanonicalGroupedResidualResource.IsAvailable axis hn2 hn3 hT
                assignment (canonicalHullFirstSeparatingCandidateEquiv
                  axis hn2 hn3 hT candidate))
    (hduplicate : ∀ source : IncompatibleBoundaryGapRootPortDebtSlot
        axis hn2 hn3 hT
        (fullPrunedComponentCotreeDualRealization axis hn2 hn3 hT assignment)
        (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment),
      ∃ activeRoot : ↥((fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).roots),
        fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment
            activeRoot = source.1.1.1 ∧
          ∃ candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT,
            firstSeparating ⟨activeRoot.1, by trivial⟩ = .residual candidate ∧
              CanonicalGroupedResidualResource.IsAvailable axis hn2 hn3 hT
                assignment (canonicalHullFirstSeparatingCandidateEquiv
                  axis hn2 hn3 hT candidate))
    (hbranch : ∀ obligation : CanonicalGroupedSeparatorOccurrenceObligation
        axis hn2 hn3 hT assignment,
      ∃ candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT,
        firstSeparating
            ⟨canonicalHullMergerSlotChild axis hn2 hn3 hT assignment obligation.slot,
              by trivial⟩ = .residual candidate ∧
          CanonicalGroupedResidualResource.IsAvailable axis hn2 hn3 hT assignment
            (canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT candidate))
    (houter : ∀ collision : FullPrunedOuterCollision axis hn2 hn3 hT,
      CanonicalGroupedResidualResource.IsAvailable axis hn2 hn3 hT assignment
        (canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT
          (outerFirstSeparating collision
            (fullPrunedOuterCollisionDualProvenance axis hn2 hn3 hT collision))))
    (source : CanonicalGroupedResidualSource axis hn2 hn3 hT assignment) :
    (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating source).Nonempty := by
  rcases source with source | source
  · obtain ⟨activeRoot, hroot, candidate, hresidual, havailable⟩ := hreserved source
    exact canonicalGroupedResidualNeighborhood_reservedUsedPort_nonempty_of_continuation
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating source
        activeRoot hroot candidate hresidual havailable
  · rcases source with source | source
    · obtain ⟨activeRoot, hroot, candidate, hresidual, havailable⟩ := hduplicate source
      exact canonicalGroupedResidualNeighborhood_incompatibleDuplicate_nonempty_of_continuation
        axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating source
          activeRoot hroot candidate hresidual havailable
    · rcases source with obligation | collision
      · obtain ⟨candidate, hresidual, havailable⟩ := hbranch obligation
        exact canonicalGroupedResidualNeighborhood_branch_nonempty_of_continuation
          axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating
            obligation candidate hresidual havailable
      · exact canonicalGroupedResidualNeighborhood_outer_nonempty
          axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating
            collision (houter collision)

/-- A canonical partial grouped routing contains no unrestricted embedding: it
is precisely an injective neighborhood-respecting choice for the unresolved
source sum. -/
abbrev CanonicalPartialGroupedResidualRouting
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT) :=
  LocalizedRouting (canonicalGroupedResidualNeighborhood
    axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating)

/-- Exact Hall condition for completing the canonical minimal-hull grouped
residual routing after the two automatic classes have been installed. -/
def CanonicalGroupedResidualHall
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT) : Prop :=
  LocalizedHall (canonicalGroupedResidualNeighborhood
    axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating)

theorem canonicalGroupedResidualHall_iff_nonempty_partialRouting
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT) :
    CanonicalGroupedResidualHall axis hn2 hn3 hT assignment
        firstSeparating outerFirstSeparating ↔
      Nonempty (CanonicalPartialGroupedResidualRouting axis hn2 hn3 hT
        assignment firstSeparating outerFirstSeparating) :=
  localizedHall_iff_nonempty_routing _

/-- Source-local witnesses for one arbitrary subset of the four unresolved
grouped classes.  Membership certifies that reserved ports, incompatible
duplicates, and outer collisions reach a residual first-owned resource, while
branch slots use a realized first separator of the minimal hull. -/
structure CanonicalGroupedResidualHullExpansionWitness
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (S : Finset (CanonicalGroupedResidualSource
      axis hn2 hn3 hT assignment)) where
  resource : ↥S ↪ BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  mem_source_hull : ∀ source, resource source ∈
    canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating source.1

/-- Legacy matching certificate for the component-split route.  Quantifying
over every source subset makes this Hall-strength data; it is not a topology
statement supplied by hull union, C1--C4, or corner separation alone. -/
def CanonicalGroupedResidualHullExpansion
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT) : Prop :=
  ∀ S : Finset (CanonicalGroupedResidualSource
      axis hn2 hn3 hT assignment),
    Nonempty (CanonicalGroupedResidualHullExpansionWitness
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating S)

/-- The exact componentwise data needed by the direct minimal-hull argument.
Singleton availability includes residuality, first ownership, and freshness
after the automatic embeddings.  The same-component field is where the exact
minimal-hull Euler branch/root-debt slots must be realized.  The final field is
the distinct-raw-component consequence sought from nonalternation and corner
separation. -/
structure CanonicalGroupedResidualComponentDecomposition
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT) where
  Component : Type
  [componentFintype : Fintype Component]
  [componentDecidableEq : DecidableEq Component]
  component : CanonicalGroupedResidualSource axis hn2 hn3 hT assignment → Component
  singleton_available : ∀ source,
    (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating source).Nonempty
  same_component_slots : ∀ (raw : Component)
      (S : Finset (CanonicalGroupedResidualSource axis hn2 hn3 hT assignment)),
    2 ≤ S.card → (∀ source ∈ S, component source = raw) →
      Nonempty (CanonicalGroupedResidualHullExpansionWitness
        axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating S)
  different_component_disjoint : ∀ {source other},
    component source ≠ component other →
      Disjoint
        (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
          firstSeparating outerFirstSeparating source)
        (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
          firstSeparating outerFirstSeparating other)

/-- Proof-carrying classification of every unresolved source and every resource
in its exact minimal-hull neighborhood.  `firstSeparator_mem` includes
residuality and freshness.  `neighborhood_component` is the component label
preserved by the hull, so distinct labels force disjoint neighborhoods. -/
structure CanonicalGroupedResidualSourceClassification
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT) where
  Component : Type
  [componentFintype : Fintype Component]
  [componentDecidableEq : DecidableEq Component]
  component : CanonicalGroupedResidualSource axis hn2 hn3 hT assignment → Component
  resourceComponent : BoundaryGapResidualPhysicalResource axis hn2 hn3 hT → Component
  firstSeparator : CanonicalGroupedResidualSource axis hn2 hn3 hT assignment →
    BoundaryGapResidualPhysicalResource axis hn2 hn3 hT
  firstSeparator_mem : ∀ source, firstSeparator source ∈
    canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating source
  neighborhood_component : ∀ source {resource}, resource ∈
    canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating source →
        resourceComponent resource = component source

/-- Instantiate the source classification from the proved singleton witnesses
and the first-ownership/component-label law.  The only choices made are members
of the already exact source neighborhoods. -/
noncomputable def canonicalGroupedResidualSourceClassificationOfSingletons
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment}
    {outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT}
    (Component : Type) [Fintype Component] [DecidableEq Component]
    (component : CanonicalGroupedResidualSource axis hn2 hn3 hT assignment →
      Component)
    (resourceComponent : BoundaryGapResidualPhysicalResource axis hn2 hn3 hT →
      Component)
    (havailable : ∀ source,
      (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
        firstSeparating outerFirstSeparating source).Nonempty)
    (hfirstOwnership : ∀ source {resource}, resource ∈
      canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
        firstSeparating outerFirstSeparating source →
          resourceComponent resource = component source) :
    CanonicalGroupedResidualSourceClassification axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating where
  Component := Component
  component := component
  resourceComponent := resourceComponent
  firstSeparator := fun source => Classical.choose (havailable source)
  firstSeparator_mem := fun source => Classical.choose_spec (havailable source)
  neighborhood_component := hfirstOwnership

noncomputable instance canonicalGroupedResidualSourceClassificationFintype
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment}
    {outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT}
    (classification : CanonicalGroupedResidualSourceClassification
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating) :
    Fintype classification.Component := classification.componentFintype

noncomputable instance canonicalGroupedResidualSourceClassificationDecidableEq
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment}
    {outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT}
    (classification : CanonicalGroupedResidualSourceClassification
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating) :
    DecidableEq classification.Component := classification.componentDecidableEq

/-- A proof-carrying classification makes every source neighborhood nonempty. -/
theorem CanonicalGroupedResidualSourceClassification.singleton_available
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment}
    {outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT}
    (classification : CanonicalGroupedResidualSourceClassification
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating)
    (source : CanonicalGroupedResidualSource axis hn2 hn3 hT assignment) :
    (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating source).Nonempty :=
  ⟨classification.firstSeparator source,
    classification.firstSeparator_mem source⟩

/-- Component preservation on exact neighborhoods gives the required
distinct-component separation. -/
theorem CanonicalGroupedResidualSourceClassification.different_component_disjoint
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment}
    {outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT}
    (classification : CanonicalGroupedResidualSourceClassification
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating)
    {source other : CanonicalGroupedResidualSource axis hn2 hn3 hT assignment}
    (hne : classification.component source ≠ classification.component other) :
    Disjoint
      (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
        firstSeparating outerFirstSeparating source)
      (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
        firstSeparating outerFirstSeparating other) := by
  rw [Finset.disjoint_left]
  intro resource hsource hother
  apply hne
  exact (classification.neighborhood_component source hsource).symm.trans
    (classification.neighborhood_component other hother)

/-- All decomposition fields except same-component capacity follow from the
proof-carrying classification.  Same-component Hall is reduced exactly to
injectivity of the classified first separators within one component.  The
remaining geometric proof is elimination of
`CanonicalHullSameComponentNestedException`. -/
noncomputable def CanonicalGroupedResidualSourceClassification.toComponentDecomposition
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment}
    {outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT}
    (classification : CanonicalGroupedResidualSourceClassification
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating)
    (hfirstSeparator : ∀ {source other},
      classification.component source = classification.component other →
      classification.firstSeparator source = classification.firstSeparator other →
      source = other) :
    CanonicalGroupedResidualComponentDecomposition
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating where
  Component := classification.Component
  component := classification.component
  singleton_available := classification.singleton_available
  same_component_slots := by
    intro raw S _hcard hsame
    exact ⟨
      { resource :=
          { toFun := fun source => classification.firstSeparator source.1
            inj' := by
              intro a b hab
              apply Subtype.ext
              exact hfirstSeparator
                ((hsame a.1 a.2).trans (hsame b.1 b.2).symm) hab }
        mem_source_hull := fun source =>
          classification.firstSeparator_mem source.1 }⟩
  different_component_disjoint := classification.different_component_disjoint

noncomputable instance canonicalGroupedResidualComponentDecompositionFintype
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment}
    {outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT}
    (decomposition : CanonicalGroupedResidualComponentDecomposition
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating) :
    Fintype decomposition.Component := decomposition.componentFintype

noncomputable instance canonicalGroupedResidualComponentDecompositionDecidableEq
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment}
    {outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT}
    (decomposition : CanonicalGroupedResidualComponentDecomposition
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating) :
    DecidableEq decomposition.Component := decomposition.componentDecidableEq

/-- Source-local slots give the corresponding union-cardinality inequality
without passing through a global matching theorem. -/
private theorem canonicalGroupedResidual_card_le_union_of_slots
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment}
    {outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT}
    {S : Finset (CanonicalGroupedResidualSource axis hn2 hn3 hT assignment)}
    (hslots : Nonempty (CanonicalGroupedResidualHullExpansionWitness
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating S)) :
    S.card ≤ (S.biUnion (canonicalGroupedResidualNeighborhood
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating)).card := by
  let witness := Classical.choice hslots
  let intoUnion : ↥S ↪ ↥(S.biUnion
      (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
        firstSeparating outerFirstSeparating)) :=
    { toFun := fun source => ⟨witness.resource source,
        Finset.mem_biUnion.mpr
          ⟨source.1, source.2, witness.mem_source_hull source⟩⟩
      inj' := fun a b hab => witness.resource.injective
        (congrArg Subtype.val hab) }
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective intoUnion intoUnion.injective

/-- Singleton availability, exact repeated-source slots in each component, and
cross-component separation prove the full grouped Hall inequalities directly.
No embedding-to-Hall implication is used. -/
theorem canonicalGroupedResidualHall_of_componentDecomposition
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (decomposition : CanonicalGroupedResidualComponentDecomposition
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating) :
    CanonicalGroupedResidualHall axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating := by
  apply localizedHall_of_fiberwise_of_neighborhood_disjoint
    decomposition.component
  · intro raw S hsame
    by_cases hsmall : S.card ≤ 1
    · exact card_le_biUnion_of_card_le_one_of_neighborhood_nonempty _
        decomposition.singleton_available S hsmall
    · exact canonicalGroupedResidual_card_le_union_of_slots axis hn2 hn3 hT
        (decomposition.same_component_slots raw S (by omega) hsame)
  · exact decomposition.different_component_disjoint

/-- Proof-carrying source classification reduces the full grouped residual Hall
theorem to first-separator injectivity inside each exact minimal-hull component.
The currently missing geometric input is precisely elimination of the
same-component nested exception. -/
theorem canonicalGroupedResidualHall_of_sourceClassification
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (classification : CanonicalGroupedResidualSourceClassification
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating)
    (hfirstSeparator : ∀ {source other},
      classification.component source = classification.component other →
      classification.firstSeparator source = classification.firstSeparator other →
      source = other) :
    CanonicalGroupedResidualHall axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating :=
    canonicalGroupedResidualHall_of_componentDecomposition
    axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating
      (CanonicalGroupedResidualSourceClassification.toComponentDecomposition
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT)
        classification hfirstSeparator)

/-- Once the direct Hall inequalities above are established, finite Hall may be
used in its forward direction merely to package source-local witnesses for all
subsets. -/
theorem canonicalGroupedResidualHullExpansion_of_componentDecomposition
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (decomposition : CanonicalGroupedResidualComponentDecomposition
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating) :
    CanonicalGroupedResidualHullExpansion axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating := by
  have hHall := canonicalGroupedResidualHall_of_componentDecomposition
    axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating decomposition
  let routing := Classical.choice
    ((localizedHall_iff_nonempty_routing
      (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
        firstSeparating outerFirstSeparating)).mp hHall)
  intro S
  exact ⟨
    { resource :=
        { toFun := fun source => routing source.1
          inj' := fun a b hab => Subtype.ext
            (routing.toEmbedding.injective hab) }
      mem_source_hull := fun source => routing.mem_neighborhood source.1 }⟩

/-- A legacy hull-expansion witness implies its grouped Hall statement.  This
is the matching-to-Hall direction, not a geometric expansion result. -/
theorem canonicalGroupedResidualHall_of_hullExpansion
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT)
    (hexpansion : CanonicalGroupedResidualHullExpansion
      axis hn2 hn3 hT assignment firstSeparating outerFirstSeparating) :
    CanonicalGroupedResidualHall axis hn2 hn3 hT assignment
      firstSeparating outerFirstSeparating := by
  intro S
  let witness := Classical.choice (hexpansion S)
  let intoUnion : ↥S ↪ ↥(S.biUnion
      (canonicalGroupedResidualNeighborhood axis hn2 hn3 hT assignment
        firstSeparating outerFirstSeparating)) :=
    { toFun := fun source => ⟨witness.resource source,
        Finset.mem_biUnion.mpr
          ⟨source.1, source.2, witness.mem_source_hull source⟩⟩
      inj' := fun a b hab => witness.resource.injective
        (congrArg Subtype.val hab) }
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective intoUnion intoUnion.injective

private noncomputable def canonicalGroupedCompletedEmbedding
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment}
    {outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT}
    (routing : CanonicalPartialGroupedResidualRouting axis hn2 hn3 hT
      assignment firstSeparating outerFirstSeparating) :
    (UnreservedBoundaryGapUsedRootPort axis hn2 hT
        (fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
        (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment) ⊕
      (CompatibleBoundaryGapRootPortDebtSlot axis hn2 hn3 hT
        (fullPrunedComponentCotreeDualRealization axis hn2 hn3 hT assignment)
        (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment) ⊕
      CanonicalGroupedResidualSource axis hn2 hn3 hT assignment)) ↪
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT where
  toFun
    | .inl source => canonicalGroupedAutomaticEmbedding
        axis hn2 hn3 hT assignment (.inl source)
    | .inr (.inl source) => canonicalGroupedAutomaticEmbedding
        axis hn2 hn3 hT assignment (.inr source)
    | .inr (.inr source) => routing source
  inj' := by
    intro a b hab
    have havailable : ∀ source,
        CanonicalGroupedResidualResource.IsAvailable
          axis hn2 hn3 hT assignment (routing source) := by
      intro source
      exact (by
        simpa only [canonicalGroupedResidualNeighborhood, Finset.mem_filter,
          Finset.mem_univ, true_and] using
            (routing.mem_neighborhood source) :
          CanonicalGroupedResidualResource.IsAvailable
              axis hn2 hn3 hT assignment (routing source) ∧ _).1
    rcases a with a | a <;> rcases b with b | b
    · have h := (canonicalGroupedAutomaticEmbedding
          axis hn2 hn3 hT assignment).injective hab
      exact congrArg Sum.inl (Sum.inl.inj h)
    · rcases b with b | b
      · have h := (canonicalGroupedAutomaticEmbedding
          axis hn2 hn3 hT assignment).injective hab
        cases h
      · have hab' : canonicalGroupedAutomaticEmbedding
            axis hn2 hn3 hT assignment (.inl a) = routing b := by
          exact hab
        exact False.elim ((havailable b) ⟨.inl a, hab'⟩)
    · rcases a with a | a
      · have h := (canonicalGroupedAutomaticEmbedding
          axis hn2 hn3 hT assignment).injective hab
        cases h
      · have hab' : canonicalGroupedAutomaticEmbedding
            axis hn2 hn3 hT assignment (.inl b) = routing a := by
          exact hab.symm
        exact False.elim ((havailable a) ⟨.inl b, hab'⟩)
    · rcases a with a | a <;> rcases b with b | b
      · have h := (canonicalGroupedAutomaticEmbedding
            axis hn2 hn3 hT assignment).injective hab
        exact congrArg (Sum.inr ∘ Sum.inl) (Sum.inr.inj h)
      · have hab' : canonicalGroupedAutomaticEmbedding
            axis hn2 hn3 hT assignment (.inr a) = routing b := by
          exact hab
        exact False.elim ((havailable b) ⟨.inr a, hab'⟩)
      · have hab' : canonicalGroupedAutomaticEmbedding
            axis hn2 hn3 hT assignment (.inr b) = routing a := by
          exact hab.symm
        exact False.elim ((havailable a) ⟨.inr b, hab'⟩)
      · exact congrArg (Sum.inr ∘ Sum.inr) (routing.toEmbedding.injective hab)

/-- Preserve all six grouped source classes while replacing a raw merger slot
by its explicit separator-occurrence obligation. -/
private def canonicalGroupedCompletedSourceEmbedding
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root} :
    BoundaryGapCompletedGroupedSource axis hn2 hn3 hT
        (fullPrunedComponentCotreeDualRealization axis hn2 hn3 hT assignment)
        (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment) ↪
      (UnreservedBoundaryGapUsedRootPort axis hn2 hT
          (fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
          (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment) ⊕
        (CompatibleBoundaryGapRootPortDebtSlot axis hn2 hn3 hT
          (fullPrunedComponentCotreeDualRealization axis hn2 hn3 hT assignment)
          (fullPrunedComponentCotreeDualHullRootPort axis hn2 hn3 hT assignment) ⊕
        CanonicalGroupedResidualSource axis hn2 hn3 hT assignment)) where
  toFun
    | .inl p => .inl p
    | .inr (.inl d) => .inr (.inl d)
    | .inr (.inr (.inl p)) => .inr (.inr (.inl p))
    | .inr (.inr (.inr (.inl d))) => .inr (.inr (.inr (.inl d)))
    | .inr (.inr (.inr (.inr (.inl m)))) =>
        .inr (.inr (.inr (.inr (.inl ⟨m⟩))))
    | .inr (.inr (.inr (.inr (.inr o)))) =>
        .inr (.inr (.inr (.inr (.inr o))))
  inj' := by
    intro a b hab
    rcases a with a | a | a | a | a | a <;>
      rcases b with b | b | b | b | b | b <;>
      simp_all <;> injection hab

/-- Forget only the neighborhood proofs and split the one unresolved routing
into the legacy four-field partial package. -/
noncomputable def CanonicalPartialGroupedResidualRouting.toPartialGroupedRouting
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment}
    {outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT}
    (routing : CanonicalPartialGroupedResidualRouting axis hn2 hn3 hT
      assignment firstSeparating outerFirstSeparating) :
    FullPrunedComponentCotreeDualHullPartialGroupedResidualRouting
      axis hn2 hn3 hT assignment where
  reservedUsedPortRouting :=
    { toFun := fun source => canonicalGroupedCompletedEmbedding
        axis hn2 hn3 hT routing (.inr (.inr (.inl source)))
      inj' := fun _ _ h => Sum.inl.inj (Sum.inr.inj
        (Sum.inr.inj ((canonicalGroupedCompletedEmbedding
          axis hn2 hn3 hT routing).injective h))) }
  incompatibleDuplicateRouting :=
    { toFun := fun source => canonicalGroupedCompletedEmbedding
        axis hn2 hn3 hT routing (.inr (.inr (.inr (.inl source))))
      inj' := fun _ _ h => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj
        (Sum.inr.inj ((canonicalGroupedCompletedEmbedding
          axis hn2 hn3 hT routing).injective h)))) }
  mergerSlotRouting :=
    { toFun := fun source => canonicalGroupedCompletedEmbedding
        axis hn2 hn3 hT routing
          (.inr (.inr (.inr (.inr (.inl ⟨source⟩)))))
      inj' := by
        intro a b h
        have hw := (canonicalGroupedCompletedEmbedding
          axis hn2 hn3 hT routing).injective h
        exact congrArg (fun source => match source with
          | .inr (.inr (.inr (.inr (.inl obligation)))) => obligation.slot
          | _ => a) hw }
  outerCollisionRouting :=
    { toFun := fun source => canonicalGroupedCompletedEmbedding
        axis hn2 hn3 hT routing (.inr (.inr (.inr (.inr (.inr source)))))
      inj' := fun _ _ h => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
        (Sum.inr.inj ((canonicalGroupedCompletedEmbedding
          axis hn2 hn3 hT routing).injective h))))) }
  image_disjoint := by
    intro a b hab
    apply (canonicalGroupedCompletedSourceEmbedding
      (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT)).injective
    apply (canonicalGroupedCompletedEmbedding axis hn2 hn3 hT routing).injective
    rcases a with a | a | a | a | a | a <;>
      rcases b with b | b | b | b | b | b <;>
      exact hab

/-- Legacy adapter from the component-split neighborhood routing to the old
component-resolved grouped ledger.  It is not the active shared-core ledger. -/
noncomputable def CanonicalPartialGroupedResidualRouting.toLegacyGroupedLedger
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment}
    {outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT}
    (routing : CanonicalPartialGroupedResidualRouting axis hn2 hn3 hT
      assignment firstSeparating outerFirstSeparating) :
    ComponentResolvedBoundaryGapGroupedLedger axis hn2 hn3 hT root assignment :=
  (routing.toPartialGroupedRouting axis hn2 hn3 hT).toGroupedLedger
    axis hn2 hn3 hT

/-- Legacy component-split completion characterization. -/
theorem canonicalGroupedResidualHall_iff_exists_legacyGroupedLedgerCompletion
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (firstSeparating : CanonicalHullFirstSeparatingClassification
      axis hn2 hn3 hT assignment)
    (outerFirstSeparating : CanonicalOuterCollisionFirstSeparatingClassification
      axis hn2 hn3 hT) :
    CanonicalGroupedResidualHall axis hn2 hn3 hT assignment
        firstSeparating outerFirstSeparating ↔
      ∃ routing : CanonicalPartialGroupedResidualRouting axis hn2 hn3 hT
          assignment firstSeparating outerFirstSeparating,
        ∃ ledger : ComponentResolvedBoundaryGapGroupedLedger
            axis hn2 hn3 hT root assignment,
          ledger = routing.toLegacyGroupedLedger axis hn2 hn3 hT := by
  rw [canonicalGroupedResidualHall_iff_nonempty_partialRouting]
  constructor
  · rintro ⟨routing⟩
    exact ⟨routing, routing.toLegacyGroupedLedger axis hn2 hn3 hT, rfl⟩
  · rintro ⟨routing, _ledger, _⟩
    exact ⟨routing⟩

/-! #### Active global-core U3 endpoint -/

abbrev PlanarLensRootActiveDebt
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root) :=
  Σ a : ↥((PlanarInwardLensForest axis hn2 hn3 hT root).roots),
    routing.ActiveDebtFiber axis hn2 hn3 hT a.1

/-- A root debt can use a raw resource when one provenance-preserving root
escape reaches that resource and the same root first-owns a witness collapsing
to it. -/
def RootDebtCanUse
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (debt : PlanarLensRootActiveDebt axis hn2 hn3 hT routing)
    (raw : PlanarLensRawPhysicalResource (T := T)) : Prop :=
  (∃ escape : routing.SelectedRootEscape axis hn2 hn3 hT debt.1.1,
      escape.1.1 = debt.2.1 ∧
      ∃ terminal event,
        Relation.ReflTransGen
            (planarLensRootEscapeSystem axis hn2 hn3 hT root).Step
            (Classical.choose escape.2).1 terminal ∧
          (planarLensRootEscapeSystem axis hn2 hn3 hT root).terminal terminal =
            some event ∧
          event.rawResource? axis hn2 hn3 hT = some raw) ∧
    ∃ owned : PlanarLensRegionalOwned axis hn2 hT root debt.1.1,
      planarLensFirstOwnedResourceRaw axis hn2 hT owned.1 = raw

/-- Root escape terminals expose only supported outer ports.  In particular,
no internal edge or free component can occur in a root raw neighborhood. -/
theorem rootDebtCanUse_eq_outerPort
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (debt : PlanarLensRootActiveDebt axis hn2 hn3 hT routing)
    (raw : PlanarLensRawPhysicalResource (T := T))
    (huse : RootDebtCanUse axis hn2 hn3 hT routing debt raw) :
    ∃ port, raw = .inl port := by
  classical
  rcases huse.1 with ⟨_escape, _hdebt, terminal, event, _hsteps,
    hterminal, hraw⟩
  simp only [planarLensRootEscapeSystem] at hterminal
  split at hterminal
  · simp only [Option.some.injEq] at hterminal
    subst event
    exact ⟨_, Option.some.inj hraw.symm⟩
  · simp at hterminal

private def RootEscapeSlotStep (source target : GridCompassSlot n n) : Prop :=
  source ∉ markedSlots (T := T) ∧
    GridExpandedContour.equiv (T := T) source = target

private theorem rootEscapeSlotStep_rightUnique :
    Relator.RightUnique (RootEscapeSlotStep (n := n) (T := T)) := by
  intro source target other hto hother
  exact hto.2.symm.trans hother.2

private theorem rootEscape_step_slots
    {root : GridVertex n n}
    {source target : PlanarLensRootEscapeState axis hn2 hn3 hT root}
    (hstep : (planarLensRootEscapeSystem axis hn2 hn3 hT root).Step source target) :
    RootEscapeSlotStep (T := T) source.slot target.slot := by
  simp only [RankedTransitionSystem.Step, planarLensRootEscapeSystem] at hstep
  split at hstep
  · simp at hstep
  · rename_i hmarked
    simp only [Option.some.injEq] at hstep
    subst target
    exact ⟨hmarked, rfl⟩

private theorem rootEscape_steps_slots
    {root : GridVertex n n}
    {source target : PlanarLensRootEscapeState axis hn2 hn3 hT root}
    (hsteps : Relation.ReflTransGen
      (planarLensRootEscapeSystem axis hn2 hn3 hT root).Step source target) :
    Relation.ReflTransGen (RootEscapeSlotStep (T := T)) source.slot target.slot := by
  induction hsteps with
  | refl => exact Relation.ReflTransGen.refl
  | tail hsteps hstep ih => exact ih.tail (rootEscape_step_slots axis hn2 hn3 hT hstep)

private theorem rootEscape_terminal_slot_marked
    {root : GridVertex n n}
    {state : PlanarLensRootEscapeState axis hn2 hn3 hT root}
    {event : PlanarLensGeometricEvent axis hn2 hn3 hT root}
    (hterminal : (planarLensRootEscapeSystem axis hn2 hn3 hT root).terminal state =
      some event) :
    state.slot ∈ markedSlots (T := T) := by
  simp only [planarLensRootEscapeSystem] at hterminal
  split at hterminal
  · assumption
  · simp at hterminal

private theorem rootEscape_terminal_slot_eq
    {root : GridVertex n n}
    {start otherStart terminal otherTerminal :
      PlanarLensRootEscapeState axis hn2 hn3 hT root}
    {event otherEvent : PlanarLensGeometricEvent axis hn2 hn3 hT root}
    (hstart : start.slot = otherStart.slot)
    (hsteps : Relation.ReflTransGen
      (planarLensRootEscapeSystem axis hn2 hn3 hT root).Step start terminal)
    (hotherSteps : Relation.ReflTransGen
      (planarLensRootEscapeSystem axis hn2 hn3 hT root).Step otherStart otherTerminal)
    (hterminal : (planarLensRootEscapeSystem axis hn2 hn3 hT root).terminal terminal =
      some event)
    (hotherTerminal :
      (planarLensRootEscapeSystem axis hn2 hn3 hT root).terminal otherTerminal =
        some otherEvent) :
    terminal.slot = otherTerminal.slot := by
  have hfirst := rootEscape_steps_slots axis hn2 hn3 hT hsteps
  have hsecond := rootEscape_steps_slots axis hn2 hn3 hT hotherSteps
  rw [← hstart] at hsecond
  rcases Relation.ReflTransGen.total_of_right_unique
      rootEscapeSlotStep_rightUnique hfirst hsecond with hforward | hbackward
  · rcases hforward.cases_head with heq | ⟨next, hstep, _⟩
    · exact heq
    · exact (hstep.1 (rootEscape_terminal_slot_marked
        axis hn2 hn3 hT hterminal)).elim
  · rcases hbackward.cases_head with heq | ⟨next, hstep, _⟩
    · exact heq.symm
    · exact (hstep.1 (rootEscape_terminal_slot_marked
        axis hn2 hn3 hT hotherTerminal)).elim

private theorem canonicalSelectedRootEscape_slot
    {root : GridVertex n n}
    {a : PlanarInwardLensOccurrence axis hn2 hT root}
    (escape : (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root).SelectedRootEscape
      axis hn2 hn3 hT a) :
    (Classical.choose escape.2).1.slot =
      GridExpandedContour.slotOfDart (a.rootedShore axis hn2 hT).1 := by
  have hroot := PlanarLensDebtRouting.selectedRootEscape_parentless
    axis hn2 hn3 hT (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root) escape
  let chosen := Classical.choose escape.2
  have htransition := Classical.choose_spec escape.2
  have hcanonical :
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root).transition a escape.1 =
        some (.inr (.inr (planarLensCanonicalRootEscape
          axis hn2 hn3 hT escape.1.1 a))) := by
    simp [canonicalPlanarLensDebtRouting, planarLensCanonicalTransition, hroot]
  have hlabels := Option.some.inj (hcanonical.symm.trans htransition)
  have hescape := Sum.inr.inj (Sum.inr.inj hlabels)
  have hstate := congrArg Subtype.val hescape
  have hslot := congrArg PlanarLensRootEscapeState.slot hstate
  change chosen.1.slot =
    (planarLensCanonicalRootEscape axis hn2 hn3 hT escape.1.1 a).1.slot
  exact hslot.symm

noncomputable def rootRawNeighborhood
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (debt : PlanarLensRootActiveDebt axis hn2 hn3 hT routing) :
    Finset (PlanarLensRawPhysicalResource (T := T)) :=
  Finset.univ.filter fun raw => RootDebtCanUse axis hn2 hn3 hT routing debt raw

/-- Canonical root debts at the same root occurrence reach the same raw
resource whenever both uses exist.  Their occurrence-labelled states retain
different origins, but their slot orbits have the same canonical start. -/
theorem canonicalRootDebtCanUse_raw_eq
    {root : GridVertex n n}
    (debt other : PlanarLensRootActiveDebt axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root))
    (hsameRoot : debt.1 = other.1)
    {raw otherRaw : PlanarLensRawPhysicalResource (T := T)}
    (huse : RootDebtCanUse axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root) debt raw)
    (hotherUse : RootDebtCanUse axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root) other otherRaw) :
    raw = otherRaw := by
  classical
  rcases huse.1 with ⟨escape, _hdebt, terminal, event, hsteps,
    hterminal, hraw⟩
  rcases hotherUse.1 with ⟨otherEscape, _hotherDebt, otherTerminal, otherEvent,
    hotherSteps, hotherTerminal, hotherRaw⟩
  have hstart : (Classical.choose escape.2).1.slot =
      (Classical.choose otherEscape.2).1.slot := by
    rw [canonicalSelectedRootEscape_slot axis hn2 hn3 hT escape,
      canonicalSelectedRootEscape_slot axis hn2 hn3 hT otherEscape,
      congrArg Subtype.val hsameRoot]
  have hterminalSlots := rootEscape_terminal_slot_eq axis hn2 hn3 hT hstart
    hsteps hotherSteps hterminal hotherTerminal
  have hmarked := rootEscape_terminal_slot_marked axis hn2 hn3 hT hterminal
  have hotherMarked := rootEscape_terminal_slot_marked
    axis hn2 hn3 hT hotherTerminal
  have hevent : event = .supportedOuterPort terminal.origin terminal.occurrence
      (outerPortOfMarkedSlot (T := T) ⟨terminal.slot, hmarked⟩) := by
    simp only [planarLensRootEscapeSystem, hmarked, ↓reduceDIte,
      Option.some.injEq] at hterminal
    exact hterminal.symm
  have hotherEvent : otherEvent = .supportedOuterPort
      otherTerminal.origin otherTerminal.occurrence
      (outerPortOfMarkedSlot (T := T) ⟨otherTerminal.slot, hotherMarked⟩) := by
    simp only [planarLensRootEscapeSystem, hotherMarked, ↓reduceDIte,
      Option.some.injEq] at hotherTerminal
    exact hotherTerminal.symm
  subst event
  subst otherEvent
  have hrawEq : raw = .inl
      (outerPortOfMarkedSlot (T := T) ⟨terminal.slot, hmarked⟩) :=
    Option.some.inj hraw.symm
  have hotherRawEq : otherRaw = .inl
      (outerPortOfMarkedSlot (T := T) ⟨otherTerminal.slot, hotherMarked⟩) :=
    Option.some.inj hotherRaw.symm
  rw [hrawEq, hotherRawEq]
  exact congrArg Sum.inl (congrArg (outerPortOfMarkedSlot (T := T))
    (Subtype.ext hterminalSlots))

/-- Every canonical root raw neighborhood is empty or a singleton. -/
theorem canonicalRootRawNeighborhood_card_le_one
    {root : GridVertex n n}
    (debt : PlanarLensRootActiveDebt axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root)) :
    (rootRawNeighborhood axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root) debt).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro raw hraw otherRaw hotherRaw
  apply canonicalRootDebtCanUse_raw_eq axis hn2 hn3 hT debt debt rfl
  · simpa [rootRawNeighborhood] using hraw
  · simpa [rootRawNeighborhood] using hotherRaw

/-- Audited C5 candidate after global-core correction.  It retains original
provenance and counts no copied roots or branch slots, but the current escape
system makes each same-root neighborhood a common singleton.  The no-go
theorems below show that this is too strong to serve as the final endpoint. -/
def CanonicalUpperU3RootHall
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root) : Prop :=
  LocalizedHall (rootRawNeighborhood axis hn2 hn3 hT routing)

noncomputable def rootRawRoutingOfHall
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (hHall : CanonicalUpperU3RootHall axis hn2 hn3 hT routing) :
    LocalizedRouting (rootRawNeighborhood axis hn2 hn3 hT routing) :=
  Classical.choice ((localizedHall_iff_nonempty_routing
    (rootRawNeighborhood axis hn2 hn3 hT routing)).mp hHall)

theorem rootRawRoutingOfHall_canUse
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (hHall : CanonicalUpperU3RootHall axis hn2 hn3 hT routing)
    (debt : PlanarLensRootActiveDebt axis hn2 hn3 hT routing) :
    RootDebtCanUse axis hn2 hn3 hT routing debt
      (rootRawRoutingOfHall axis hn2 hn3 hT routing hHall debt) := by
  simpa [rootRawNeighborhood] using
    (rootRawRoutingOfHall axis hn2 hn3 hT routing hHall).mem_neighborhood debt

/-- Canonical root Hall cannot separate two debts at the same root occurrence:
their deterministic contour orbits expose the same raw resource. -/
theorem canonicalUpperU3RootHall_debt_eq_of_sameRoot
    {root : GridVertex n n}
    (hHall : CanonicalUpperU3RootHall axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root))
    (debt other : PlanarLensRootActiveDebt axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root))
    (hsameRoot : debt.1 = other.1) :
    debt = other := by
  let routing := rootRawRoutingOfHall axis hn2 hn3 hT
    (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root) hHall
  apply routing.toEmbedding.injective
  apply canonicalRootDebtCanUse_raw_eq axis hn2 hn3 hT debt other hsameRoot
  · exact rootRawRoutingOfHall_canUse axis hn2 hn3 hT _ hHall debt
  · exact rootRawRoutingOfHall_canUse axis hn2 hn3 hT _ hHall other

/-- Consequently canonical root Hall forces every active fiber over a root
occurrence to contain at most one debt. -/
theorem canonicalUpperU3RootHall_activeFiber_card_le_one
    {root : GridVertex n n}
    (hHall : CanonicalUpperU3RootHall axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root))
    (a : ↥((PlanarInwardLensForest axis hn2 hn3 hT root).roots)) :
    ((canonicalPlanarLensDebtRouting axis hn2 hn3 hT root).active a.1).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro debt hdebt other hother
  let x : PlanarLensRootActiveDebt axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root) :=
    ⟨a, ⟨debt, hdebt⟩⟩
  let y : PlanarLensRootActiveDebt axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root) :=
    ⟨a, ⟨other, hother⟩⟩
  have hxy := canonicalUpperU3RootHall_debt_eq_of_sameRoot
    axis hn2 hn3 hT hHall x y rfl
  exact congrArg (fun z : PlanarLensRootActiveDebt axis hn2 hn3 hT
    (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root) => z.2.1) hxy

noncomputable def rootOwnedWitnessOfHall
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (hHall : CanonicalUpperU3RootHall axis hn2 hn3 hT routing)
    (debt : PlanarLensRootActiveDebt axis hn2 hn3 hT routing) :
    PlanarLensRegionalOwned axis hn2 hT root debt.1.1 :=
  Classical.choose
    (rootRawRoutingOfHall_canUse axis hn2 hn3 hT routing hHall debt).2

theorem rootOwnedWitnessOfHall_raw
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (hHall : CanonicalUpperU3RootHall axis hn2 hn3 hT routing)
    (debt : PlanarLensRootActiveDebt axis hn2 hn3 hT routing) :
    planarLensFirstOwnedResourceRaw axis hn2 hT
        (rootOwnedWitnessOfHall axis hn2 hn3 hT routing hHall debt).1 =
      rootRawRoutingOfHall axis hn2 hn3 hT routing hHall debt :=
  Classical.choose_spec
    (rootRawRoutingOfHall_canUse axis hn2 hn3 hT routing hHall debt).2

noncomputable def rootTerminationAssignmentOfHall
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (hHall : CanonicalUpperU3RootHall axis hn2 hn3 hT routing)
    (a : PlanarInwardLensOccurrence axis hn2 hT root)
    (hroot : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a = none) :
    routing.RootTerminationAssignment axis hn2 hn3 hT a where
  toFun debt :=
    rootOwnedWitnessOfHall axis hn2 hn3 hT routing hHall
      ⟨⟨a, by simp [ParentForest.roots, hroot]⟩, debt⟩
  inj' := by
    intro debt other heq
    let x : PlanarLensRootActiveDebt axis hn2 hn3 hT routing :=
      ⟨⟨a, by simp [ParentForest.roots, hroot]⟩, debt⟩
    let y : PlanarLensRootActiveDebt axis hn2 hn3 hT routing :=
      ⟨⟨a, by simp [ParentForest.roots, hroot]⟩, other⟩
    have howned : rootOwnedWitnessOfHall axis hn2 hn3 hT routing hHall x =
        rootOwnedWitnessOfHall axis hn2 hn3 hT routing hHall y := by
      exact heq
    have hraw : rootRawRoutingOfHall axis hn2 hn3 hT routing hHall x =
        rootRawRoutingOfHall axis hn2 hn3 hT routing hHall y := by
      rw [← rootOwnedWitnessOfHall_raw axis hn2 hn3 hT routing hHall x,
        ← rootOwnedWitnessOfHall_raw axis hn2 hn3 hT routing hHall y, howned]
    have hxy := (rootRawRoutingOfHall axis hn2 hn3 hT routing hHall).toEmbedding.injective hraw
    apply Subtype.ext
    exact congrArg
      (fun z : PlanarLensRootActiveDebt axis hn2 hn3 hT routing => z.2.1) hxy

/-- C5 plus the already-constructed nonroot transport gives the paid transport
certificate. -/
noncomputable def canonicalUpperU3TransportCertificateOfRootHall
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (localInterfaces : ∀ a,
      (PlanarInwardLensForest axis hn2 hn3 hT root).parent a ≠ none →
        routing.CarriesCanonicalLocalInterfacesAt axis hn2 hn3 hT a)
    (passIncoming : ∀ a,
      (PlanarInwardLensForest axis hn2 hn3 hT root).parent a ≠ none →
        routing.PassesIncomingAt axis hn2 hn3 hT a)
    (hHall : CanonicalUpperU3RootHall axis hn2 hn3 hT routing) :
    CanonicalUpperU3TransportCertificate axis hn2 hn3 hT root where
  routing := routing
  localInterfaces := localInterfaces
  passIncoming := passIncoming
  rootTermination := rootTerminationAssignmentOfHall axis hn2 hn3 hT routing hHall

/-- Fully instantiated finite ordered collision residual left after C4: Hall
for the concrete root debts and raw-resource neighborhoods above. -/
def CanonicalUpperU3OrderedRootCollisionResidual
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root) : Prop :=
  ∀ S : Finset (PlanarLensRootActiveDebt axis hn2 hn3 hT routing),
    S.card ≤ (S.biUnion (rootRawNeighborhood axis hn2 hn3 hT routing)).card

theorem canonicalUpperU3RootHall_iff_orderedCollisionResidual
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root) :
    CanonicalUpperU3RootHall axis hn2 hn3 hT routing ↔
      CanonicalUpperU3OrderedRootCollisionResidual axis hn2 hn3 hT routing :=
  Iff.rfl

def CanonicalUpperU3TransportCertificate.activeDebtCertificate
    {root : GridVertex n n}
    (certificate : CanonicalUpperU3TransportCertificate axis hn2 hn3 hT root) :
    CanonicalUpperU3ActiveDebtCertificate axis hn2 hn3 hT root where
  routing := certificate.routing
  regionalAssignment := by
    intro a
    cases hp : (PlanarInwardLensForest axis hn2 hn3 hT root).parent a with
    | none =>
        let terminal := certificate.rootTermination a hp
        exact {
          toFun := fun q => .inl (terminal q)
          inj' := by
            intro q r hqr
            exact terminal.injective (Sum.inl.inj hqr) }
    | some parent =>
        apply certificate.routing.regionalAssignmentOfAllActiveMoves
          axis hn2 hn3 hT a
        · simp [hp]
        apply certificate.routing.allActiveMoves_of_localInterfaces_of_passesIncoming
          axis hn2 hn3 hT a
        · exact certificate.localInterfaces a (by simp [hp])
        · exact certificate.passIncoming a (by simp [hp])

theorem CanonicalUpperU3ActiveDebtCertificate.globalHall
    {root : GridVertex n n}
    (certificate : CanonicalUpperU3ActiveDebtCertificate axis hn2 hn3 hT root) :
    LocalizedHall (canonicalUpperU3ActiveNeighborhood
      (root := root) axis hn2 hn3 hT) := by
  apply canonicalUpperU3_activeLocalInequality_globalHall
    axis hn2 hn3 hT certificate.routing
  intro a
  exact certificate.routing.regionInequality_of_assignment
    axis hn2 hn3 hT a (certificate.regionalAssignment a)

theorem CanonicalUpperU3TransportCertificate.globalHall
    {root : GridVertex n n}
    (certificate : CanonicalUpperU3TransportCertificate axis hn2 hn3 hT root) :
    LocalizedHall (canonicalUpperU3ActiveNeighborhood
      (root := root) axis hn2 hn3 hT) :=
  certificate.activeDebtCertificate.globalHall axis hn2 hn3 hT

theorem canonicalUpperU3_activeGlobalHall_of_rootHall
    {root : GridVertex n n}
    (routing : PlanarLensDebtRouting axis hn2 hn3 hT root)
    (localInterfaces : ∀ a,
      (PlanarInwardLensForest axis hn2 hn3 hT root).parent a ≠ none →
        routing.CarriesCanonicalLocalInterfacesAt axis hn2 hn3 hT a)
    (passIncoming : ∀ a,
      (PlanarInwardLensForest axis hn2 hn3 hT root).parent a ≠ none →
        routing.PassesIncomingAt axis hn2 hn3 hT a)
    (hHall : CanonicalUpperU3RootHall axis hn2 hn3 hT routing) :
    LocalizedHall (canonicalUpperU3ActiveNeighborhood
      (root := root) axis hn2 hn3 hT) :=
  (canonicalUpperU3TransportCertificateOfRootHall axis hn2 hn3 hT routing
    localInterfaces passIncoming hHall).globalHall axis hn2 hn3 hT

/-- For the canonical occurrence routing, all nonroot transport obligations are
discharged, so active global Hall reduces exactly to root Hall. -/
theorem canonicalUpperU3_activeGlobalHall_of_canonicalRootHall
    {root : GridVertex n n}
    (hHall : CanonicalUpperU3RootHall axis hn2 hn3 hT
      (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root)) :
    LocalizedHall (canonicalUpperU3ActiveNeighborhood
      (root := root) axis hn2 hn3 hT) :=
  canonicalUpperU3_activeGlobalHall_of_rootHall axis hn2 hn3 hT
    (canonicalPlanarLensDebtRouting axis hn2 hn3 hT root)
    (PlanarLensDebtRouting.canonicalPlanarLensDebtRouting_carriesCanonicalLocalInterfacesAt
      axis hn2 hn3 hT)
    (PlanarLensDebtRouting.canonicalPlanarLensDebtRouting_passesIncomingAt
      axis hn2 hn3 hT) hHall

/-- REJECTED AUDIT API: product-census inequality over all possible crossing
edges.  Main U3 theorems use `CanonicalUpperU3ActiveLocalInequality`. -/
def CanonicalUpperU3LocalInequality (root : GridVertex n n) : Prop :=
  ∀ a : PlanarInwardLensOccurrence axis hn2 hT root,
    CanonicalUpperU3RegionInequality axis hn2 hn3 hT root a

/-- Since every leaf case is proved, full U3 is equivalent to the single
nonleaf propagation/reconvergence residual subtype. -/
theorem canonicalUpperU3_localInequality_iff_nonleaf
    (root : GridVertex n n) :
    CanonicalUpperU3LocalInequality axis hn2 hn3 hT root ↔
      ∀ a : PlanarLensNonleafReconvergenceRegion axis hn2 hn3 hT root,
        CanonicalUpperU3RegionInequality axis hn2 hn3 hT root a.1 := by
  constructor
  · intro h a
    exact h a.1
  · intro h a
    by_cases ha : a ∈ (PlanarInwardLensForest axis hn2 hn3 hT root).leaves
    · exact canonicalUpperU3_regionInequality_of_mem_leaves axis hn2 hn3 hT a ha
    · exact h ⟨a, ha⟩

/-- Exhaustive structural reduction: leaves are already discharged, so only
unary propagation and genuine multi-child reconvergence remain. -/
theorem canonicalUpperU3_localInequality_iff_unary_and_genuine
    (root : GridVertex n n) :
    CanonicalUpperU3LocalInequality axis hn2 hn3 hT root ↔
      (∀ a : PlanarLensUnaryPropagationRegion axis hn2 hn3 hT root,
        CanonicalUpperU3RegionInequality axis hn2 hn3 hT root a.1) ∧
      (∀ a : PlanarLensGenuineReconvergenceRegion axis hn2 hn3 hT root,
        CanonicalUpperU3RegionInequality axis hn2 hn3 hT root a.1) := by
  constructor
  · intro h
    exact ⟨fun a => h a.1, fun a => h a.1⟩
  · rintro ⟨hunary, hgenuine⟩ a
    let F := PlanarInwardLensForest axis hn2 hn3 hT root
    cases hcount : F.childCount a with
    | zero =>
        apply canonicalUpperU3_regionInequality_of_mem_leaves axis hn2 hn3 hT a
        have hcount' :
            (PlanarInwardLensForest axis hn2 hn3 hT root).childCount a = 0 := by
          simpa [F] using hcount
        simp [ParentForest.leaves, hcount']
    | succ k =>
        cases k with
        | zero =>
            exact hunary ⟨a, by simpa [F] using hcount⟩
        | succ k =>
            have hcount' :
                (PlanarInwardLensForest axis hn2 hn3 hT root).childCount a =
                  Nat.succ (Nat.succ k) := by
              simpa [F] using hcount
            exact hgenuine ⟨a, by omega⟩

/-- Once the unary slot-to-cell/comb gate is supplied, the only remaining U3
case is genuine multi-child reconvergence. -/
theorem canonicalUpperU3_localInequality_of_unaryAssignments_and_genuine
    (root : GridVertex n n)
    (hunary : CanonicalUpperU3AllCrossingUnaryAssignmentGate axis hn2 hn3 hT root)
    (hgenuine : ∀ a : PlanarLensGenuineReconvergenceRegion axis hn2 hn3 hT root,
      CanonicalUpperU3RegionInequality axis hn2 hn3 hT root a.1) :
    CanonicalUpperU3LocalInequality axis hn2 hn3 hT root := by
  rw [canonicalUpperU3_localInequality_iff_unary_and_genuine axis hn2 hn3 hT root]
  exact ⟨fun a => canonicalUpperU3_regionInequality_of_assignment
    axis hn2 hn3 hT a.1 (Classical.choice (hunary a)), hgenuine⟩

/-- REJECTED AUDIT API: complete neighborhood for the product-census model. -/
def canonicalUpperU3GlobalNeighborhood (root : GridVertex n n)
    (_ : (PlanarInwardLensForest axis hn2 hn3 hT root).MergerSlot) :
    Finset (PlanarLensFirstOwnedResource axis hn2 hT root) := Finset.univ

/-- REJECTED AUDIT API: use
`canonicalUpperU3_activeLocalInequality_globalHall`. -/
theorem canonicalUpperU3_localInequality_implies_globalHall
    (root : GridVertex n n)
    (hlocal : CanonicalUpperU3LocalInequality axis hn2 hn3 hT root) :
    LocalizedHall (canonicalUpperU3GlobalNeighborhood axis hn2 hn3 hT root) := by
  let F := PlanarInwardLensForest axis hn2 hn3 hT root
  let debt := fun a => Fintype.card (PlanarLensLocalDebt axis hn2 hn3 hT root a)
  let owned := fun a => Fintype.card (PlanarLensRegionalOwned axis hn2 hT root a)
  let passed := fun a =>
    Fintype.card (PlanarLensPassedTransition axis hn2 hn3 hT root a)
  have hroot : ∀ a, F.parent a = none → passed a = 0 := by
    intro a ha
    let := planarLensPassedTransition_empty_of_isRoot axis hn2 hn3 hT a ha
    exact Fintype.card_eq_zero
  have hlocal' : ∀ a,
      debt a + ∑ c ∈ F.children a, passed c ≤ owned a + passed a := by
    intro a
    have ha := hlocal a
    change debt a + (∑ c : ↥(F.children a), passed c.1) ≤
      owned a + passed a at ha
    rw [sum_finset_subtype_eq_sum_filter] at ha
    exact ha
  have hglobal : ∑ a, debt a ≤ ∑ a, owned a :=
    parentForest_global_le_of_regional_telescope F debt owned passed hroot hlocal'
  have hdebt : Fintype.card F.MergerSlot = ∑ a, debt a := by
    rw [Fintype.card_congr (planarLensLocalDebtDecomposition axis hn2 hn3 hT root),
      Fintype.card_sigma]
  have howned : Fintype.card (PlanarLensFirstOwnedResource axis hn2 hT root) =
      ∑ a, owned a := by
    rw [Fintype.card_congr (planarLensRegionalOwnedDecomposition axis hn2 hT root),
      Fintype.card_sigma]
  intro S
  by_cases hS : S = ∅
  · simp [hS]
  · calc
      S.card ≤ Fintype.card F.MergerSlot := by
        simpa [← Finset.card_univ] using Finset.card_le_card (Finset.subset_univ S)
      _ = ∑ a, debt a := hdebt
      _ ≤ ∑ a, owned a := hglobal
      _ = Fintype.card (PlanarLensFirstOwnedResource axis hn2 hT root) := howned.symm
      _ = (S.biUnion
          (canonicalUpperU3GlobalNeighborhood axis hn2 hn3 hT root)).card := by
        have hbi : S.biUnion
            (canonicalUpperU3GlobalNeighborhood axis hn2 hn3 hT root) =
            (Finset.univ : Finset (PlanarLensFirstOwnedResource axis hn2 hT root)) := by
          ext r
          simp only [Finset.mem_biUnion, canonicalUpperU3GlobalNeighborhood,
            Finset.mem_univ, iff_true]
          obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hS
          exact ⟨a, ha, trivial⟩
        rw [hbi]
        exact (Finset.card_univ).symm

/-- Under the still-residual face-cut gate, corrected common-root regions are
unconditionally laminar or disjoint. -/
theorem rootedInwardLensInteriorFaces_laminar_of_faceCutGate
    (hgate : InwardShoreFaceCutGate hn2 hT)
    (root : GridVertex n n)
    (L K : CanonicalLens axis hn2 hT)
    {d e : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d)
    (he : lensDirectBranchGerm axis hn2 hT K = .inward e) :
    rootedInwardLensInteriorFaces axis hn2 hT root L hd ⊆
        rootedInwardLensInteriorFaces axis hn2 hT root K he ∨
      rootedInwardLensInteriorFaces axis hn2 hT root K he ⊆
        rootedInwardLensInteriorFaces axis hn2 hT root L hd ∨
      Disjoint (rootedInwardLensInteriorFaces axis hn2 hT root L hd)
        (rootedInwardLensInteriorFaces axis hn2 hT root K he) := by
  let rd := rootedInwardRegionDart hT root d
  let re := rootedInwardRegionDart hT root e
  have hrd : GridDirectionalDart.AwayFromRoot root rd :=
    rootedInwardRegionDart_awayFromRoot hT root d
  have hre : GridDirectionalDart.AwayFromRoot root re :=
    rootedInwardRegionDart_awayFromRoot hT root e
  rcases GridDirectionalDart.targetShoreVertices_laminar hT.isTree root hrd hre with
    hde | hed | hdis
  · exact Or.inl
      (inwardShoreInteriorFaces_subset_of_targetShore_subset hn2 hT rd re hde
        (hgate.1 rd re hde))
  · exact Or.inr (Or.inl
      (inwardShoreInteriorFaces_subset_of_targetShore_subset hn2 hT re rd hed
        (hgate.1 re rd hed)))
  · exact Or.inr (Or.inr
      (inwardShoreInteriorFaces_disjoint_of_targetShores_disjoint hn2 hT rd re hdis
        (hgate.2 rd re hdis)))

/-- The cycle theorem specialized to an inward canonical lens. -/
theorem inwardLensCollarCycle_isCycle
    (L : CanonicalLens axis hn2 hT) {d : GridDirectionalDart T}
    (_hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    (inwardShoreCollarCycle hn2 hT d).IsCycle :=
  inwardShoreCollarCycle_isCycle hn2 hT d

/-- Occurrence-level package assigning an inward lens's canonical owner to its
nonempty local face carrier.  Minimality among several such carriers requires
the unresolved shore-to-face nesting transport. -/
structure InwardLensRegionAssignment
    (L : CanonicalLens axis hn2 hT) where
  dart : GridDirectionalDart T
  direct_eq : lensDirectBranchGerm axis hn2 hT L = .inward dart
  occurrence : ↥(startSlots axis hn2 hT)
  occurrence_mem : occurrence ∈ L.originRegion
  faces : Finset (GridFace (GridExpandedContour.collarSize n)
    (GridExpandedContour.collarSize n))
  faces_eq : faces = inwardLensInteriorFaces axis hn2 hT L direct_eq
  faces_nonempty : faces.Nonempty

def inwardLensRegionAssignment
    (L : CanonicalLens axis hn2 hT) {d : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d) :
    InwardLensRegionAssignment axis hn2 hT L where
  dart := d
  direct_eq := hd
  occurrence := L.ownerStart
  occurrence_mem :=
    MarkedCycleFirstStop.ReconvergenceLens.ownerStart_mem_origins L
  faces := inwardLensInteriorFaces axis hn2 hT L hd
  faces_eq := rfl
  faces_nonempty := inwardLensInteriorFaces_nonempty axis hn2 hT L hd

/-- Residual direct-germ case not covered by reverse-dart history. -/
def IsOuterDirectLens (L : CanonicalLens axis hn2 hT) : Prop :=
  ∃ p : GridCotreeOuterPort T,
    lensDirectBranchGerm axis hn2 hT L = .outer p

/-- Outer direct germs occur at marked merger slots, so their shared suffix has
rank zero.  They are a degenerate residual case rather than a nontrivial lens
arc. -/
theorem lensRank_eq_zero_of_direct_outer
    (L : CanonicalLens axis hn2 hT) {p : GridCotreeOuterPort T}
    (hp : lensDirectBranchGerm axis hn2 hT L = .outer p) : L.rank = 0 := by
  have hslot := lensDirectBranchGerm_slot axis hn2 hT L
  rw [hp, lensMergerBranches_directStart_value] at hslot
  change GridExpandedContour.outerPortSlot p = L.mergerState.1.1 at hslot
  have hmarked : L.mergerState.1.1 ∈ markedSlots (T := T) := by
    rw [← hslot]
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
  rw [L.rank_eq]
  exact ((firstStop axis hn2 hT).distance_eq_zero_iff _).mpr hmarked

theorem planarOuterLensOccurrence_lensRank_eq_zero
    {root : GridVertex n n}
    (a : PlanarOuterLensOccurrence axis hn2 hT root) :
    a.lens.rank = 0 :=
  lensRank_eq_zero_of_direct_outer axis hn2 hT a.lens a.direct_eq

theorem lensParent_eq_none_of_rank_eq_zero
    (L : CanonicalLens axis hn2 hT) (hrank : L.rank = 0) :
    L.parent = none := by
  cases hparent : L.parent with
  | none => rfl
  | some K =>
      have hlt := MarkedCycleFirstStop.ReconvergenceLens.rank_parent hparent
      omega

/-- Outer direct lenses are rank-zero roots of the occurrence-level lens
forest, hence boundary degeneracies rather than bounded inward regions. -/
theorem outerDirectLens_parent_eq_none
    (L : CanonicalLens axis hn2 hT) {p : GridCotreeOuterPort T}
    (hp : lensDirectBranchGerm axis hn2 hT L = .outer p) :
    L.parent = none :=
  lensParent_eq_none_of_rank_eq_zero axis hn2 hT L
    (lensRank_eq_zero_of_direct_outer axis hn2 hT L hp)

/-- Every canonical lens is either an eligible inward reverse-history case, an
inward case still missing the reverse-occurrence ordering theorem, or a
rank-zero outer case. -/
theorem preStartHistory_case_split
    (L : CanonicalLens axis hn2 hT) :
    Nonempty (InwardReverseHistoryData axis hn2 hT L) ∨
      (∃ d : GridDirectionalDart T,
        lensDirectBranchGerm axis hn2 hT L = .inward d ∧
        IsEmpty (InwardReverseHistoryData axis hn2 hT L)) ∨
      IsOuterDirectLens axis hn2 hT L := by
  classical
  cases h : lensDirectBranchGerm axis hn2 hT L with
  | inward d =>
      by_cases he : Nonempty (InwardReverseHistoryData axis hn2 hT L)
      · exact Or.inl he
      · right
        left
        have : IsEmpty (InwardReverseHistoryData axis hn2 hT L) :=
          ⟨fun x => he ⟨x⟩⟩
        exact ⟨d, rfl, inferInstance⟩
  | outer p =>
      exact Or.inr (Or.inr ⟨p, h⟩)

/-- Parent interval data has a strictly larger set of originating
occurrences.  This is not planar containment. -/
theorem lensIntervalRegion_originSlots_ssubset_of_parent
    {L K : CanonicalLens axis hn2 hT} (hparent : L.parent = some K) :
    (lensIntervalRegion axis hn2 hT L).originSlots ⊂
      (lensIntervalRegion axis hn2 hT K).originSlots :=
  MarkedCycleFirstStop.ReconvergenceLens.originRegion_ssubset_of_parent hparent

theorem mem_parent_originSlots_of_mem
    {L K : CanonicalLens axis hn2 hT} (hparent : L.parent = some K)
    {s : ↥(startSlots axis hn2 hT)}
    (hs : s ∈ (lensIntervalRegion axis hn2 hT L).originSlots) :
    s ∈ (lensIntervalRegion axis hn2 hT K).originSlots :=
  (lensIntervalRegion_originSlots_ssubset_of_parent axis hn2 hT hparent).1 hs

/-- Exact conditional parent-region theorem.  The occurrence parent relation
alone supplies strict occurrence containment, while planar strict containment
additionally requires target-shore nesting, dual path transport across the two
attachment chords, and a parent-annulus face. -/
theorem inwardLensInteriorFaces_ssubset_of_parent_of_dualNesting
    {L K : CanonicalLens axis hn2 hT} (hparent : L.parent = some K)
    {d e : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d)
    (he : lensDirectBranchGerm axis hn2 hT K = .inward e)
    (_hshore : d.targetShoreVertices ⊆ e.targetShoreVertices)
    (hdual : InwardShoreDualNesting hn2 hT d e)
    (hannulus : ∃ f, f ∈ inwardLensInteriorFaces axis hn2 hT K he ∧
      f ∉ inwardLensInteriorFaces axis hn2 hT L hd) :
    inwardLensInteriorFaces axis hn2 hT L hd ⊂
      inwardLensInteriorFaces axis hn2 hT K he := by
  have _ := hparent
  exact inwardShoreInteriorFaces_ssubset_of_dualNesting hn2 hT d e hdual hannulus

/-- Parent lenses continue along the same expanded-contour suffix to the same
outer cotree port. -/
theorem lensOuterPort_eq_of_parent {L K : CanonicalLens axis hn2 hT}
    (hparent : L.parent = some K) :
    lensOuterPort axis hn2 hT L = lensOuterPort axis hn2 hT K := by
  apply congrArg (outerPortOfMarkedSlot (T := T))
  apply Subtype.ext
  change L.reachedStop.1 = K.reachedStop.1
  exact congrArg Subtype.val
    (MarkedCycleFirstStop.ReconvergenceLens.reachedStop_eq_of_parent hparent)

theorem lensRegionRoot_eq_of_parent {L K : CanonicalLens axis hn2 hT}
    (hparent : L.parent = some K) :
    lensRegionRoot axis hn2 hT L = lensRegionRoot axis hn2 hT K := by
  exact congrArg (fun p : GridCotreeOuterPort T => p.vertex)
    (lensOuterPort_eq_of_parent axis hn2 hT hparent)

/-- Parent-related inward lenses have a common canonical root, hence their
correctly oriented local regions are laminar or disjoint, but not necessarily
strictly nested. -/
theorem canonicalRootedInwardLensInteriorFaces_laminar_of_parent
    (hgate : InwardShoreFaceCutGate hn2 hT)
    {L K : CanonicalLens axis hn2 hT} (hparent : L.parent = some K)
    {d e : GridDirectionalDart T}
    (hd : lensDirectBranchGerm axis hn2 hT L = .inward d)
    (he : lensDirectBranchGerm axis hn2 hT K = .inward e) :
    canonicalRootedInwardLensInteriorFaces axis hn2 hT L hd ⊆
        canonicalRootedInwardLensInteriorFaces axis hn2 hT K he ∨
      canonicalRootedInwardLensInteriorFaces axis hn2 hT K he ⊆
        canonicalRootedInwardLensInteriorFaces axis hn2 hT L hd ∨
      Disjoint (canonicalRootedInwardLensInteriorFaces axis hn2 hT L hd)
        (canonicalRootedInwardLensInteriorFaces axis hn2 hT K he) := by
  have hroot := lensRegionRoot_eq_of_parent axis hn2 hT hparent
  simpa [canonicalRootedInwardLensInteriorFaces, hroot] using
    rootedInwardLensInteriorFaces_laminar_of_faceCutGate axis hn2 hT hgate
      (lensRegionRoot axis hn2 hT L) L K hd he

/-- Parent interval data has the same concrete expanded-contour terminal slot. -/
theorem lensIntervalRegion_terminalSlot_eq_of_parent
    {L K : CanonicalLens axis hn2 hT} (hparent : L.parent = some K) :
    (lensIntervalRegion axis hn2 hT L).terminalSlot =
      (lensIntervalRegion axis hn2 hT K).terminalSlot := by
  exact congrArg (fun x => x.1)
    (MarkedCycleFirstStop.ReconvergenceLens.reachedStop_eq_of_parent hparent)

/-- Root characterization available without planar geometry: the interval
data is terminal in the lens forest exactly when no later merger occurrence
lies before its outer-port terminal on the shared contour suffix. -/
theorem lensIntervalRegion_isRoot_iff
    (L : CanonicalLens axis hn2 hT) :
    L.parent = none ↔ ¬∃ K : CanonicalLens axis hn2 hT, L.OnSharedSuffix K :=
  MarkedCycleFirstStop.ReconvergenceLens.parent_eq_none_iff_no_later_lens L

end

end CanonicalExpandedContourForest

end GridGraphs
