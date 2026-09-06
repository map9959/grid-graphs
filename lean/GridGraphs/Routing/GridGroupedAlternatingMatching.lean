import GridGraphs.Surgery.FiniteAlternatingExchange
import GridGraphs.Routing.ReverseRootSharedHullAdjacency
import GridGraphs.Geometry.RetainedSupportEdgePassThrough
import GridGraphs.Routing.RawFreeComponentContinuation

/-!
# Grid grouped alternating matching

This module joins the canonical automatic reservations to the actual grouped
shared-hull residual sources.  The resource side remains the raw physical
universe, so a residual source may first enter an occupied reservation and then
displace its automatic owner.  No Hall or total outgoing-adjacency statement is
made.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace CanonicalExpandedContourForest

variable {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
  {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
  (hT : IsSpanningSubtree (gridGraph n n) T)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The complete source universe for grouped alternating exchange: installed
automatic owners together with exactly the active shared-hull residual source.
The latter consists of reserved used root ports, one-copy merger slots, and
outer collisions. -/
abbrev GridGroupedAlternatingSource
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  FullPrunedAutomaticOwner axis hn2 hn3 hT ⊕
    SharedCanonicalGroupedResidualSource axis hn2 hn3 hT assignment

/-- Alternating exchange is performed against raw physical resources, including
the occupied canonical reservations. -/
abbrev GridGroupedAlternatingRawResource :=
  PlanarLensRawPhysicalResource (T := T)

/-- Exact source-to-resource incidence for the grouped grid layer. -/
inductive GridGroupedAlternatingAdjacent
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT) :
    GridGroupedAlternatingSource axis hn2 hn3 hT assignment →
      GridGroupedAlternatingRawResource (T := T) → Prop
  | occupiedReservation
      (owner : FullPrunedAutomaticOwner axis hn2 hn3 hT) :
      GridGroupedAlternatingAdjacent assignment continuation (.inl owner)
        (owner.rawResource axis hn2 hn3 hT)
  | reservedUsedRoot
      (source : ReservedBoundaryGapUsedRootPort axis hn2 hT
        (fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment)
        (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment)) :
      GridGroupedAlternatingAdjacent assignment continuation (.inr (.inl source))
        (.inl source.1.1)
  | sharedHullReverseRoot
      (source : ReservedBoundaryGapUsedRootPort axis hn2 hT
        (fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment)
        (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment))
      (activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
        axis hn2 hn3 hT assignment).roots))
      (source_eq : fullPrunedSharedCotreeDualHullRootPort
        axis hn2 hn3 hT assignment activeRoot = source.1.1)
      (raw : GridGroupedAlternatingRawResource (T := T))
      (hadj : FullPrunedSharedCotreeDualHullReverseRootAdjacent
        axis hn2 hn3 hT assignment activeRoot raw) :
      GridGroupedAlternatingAdjacent assignment continuation
        (.inr (.inl source)) raw
  | sharedHullContinuation
      (slot : (fullPrunedSharedCotreeDualHullForest
        axis hn2 hn3 hT assignment).MergerSlot)
      (raw : GridGroupedAlternatingRawResource (T := T))
      (hadj : FullPrunedSharedCotreeDualHullContinuationAdjacent
        axis hn2 hn3 hT assignment slot raw) :
      GridGroupedAlternatingAdjacent assignment continuation
        (.inr (.inr (.inl slot))) raw
  | outerDirectPort
      (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
      GridGroupedAlternatingAdjacent assignment continuation
        (.inr (.inr (.inr collision)))
        (.inl (collision.port axis hn2 hn3 hT))
  | displacedOwnerOutgoing
      (owner : FullPrunedAutomaticOwner axis hn2 hn3 hT)
      (raw : GridGroupedAlternatingRawResource (T := T))
      (hadj : FullPrunedDisplacedOwnerOutgoingAdjacent
        axis hn2 hn3 hT continuation owner raw) :
      GridGroupedAlternatingAdjacent assignment continuation (.inl owner) raw

/-- Canonical partial ownership, defined only on the range of the automatic
owner embedding. -/
noncomputable def gridGroupedAutomaticOwner
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (raw : GridGroupedAlternatingRawResource (T := T)) :
    Option (GridGroupedAlternatingSource axis hn2 hn3 hT assignment) :=
  if h : ∃ owner : FullPrunedAutomaticOwner axis hn2 hn3 hT,
      owner.rawResource axis hn2 hn3 hT = raw then
    some (.inl (Classical.choose h))
  else none

theorem gridGroupedAutomaticOwner_eq_some_iff
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (raw : GridGroupedAlternatingRawResource (T := T))
    (owner : FullPrunedAutomaticOwner axis hn2 hn3 hT) :
    gridGroupedAutomaticOwner axis hn2 hn3 hT assignment raw = some (.inl owner) ↔
      owner.rawResource axis hn2 hn3 hT = raw := by
  unfold gridGroupedAutomaticOwner
  constructor
  · intro howner
    split at howner
    · rename_i h
      have hchosen : Classical.choose h = owner := Sum.inl.inj (Option.some.inj howner)
      simpa [hchosen] using Classical.choose_spec h
    · cases howner
  · intro hraw
    have h : ∃ other : FullPrunedAutomaticOwner axis hn2 hn3 hT,
        other.rawResource axis hn2 hn3 hT = raw := ⟨owner, hraw⟩
    rw [dif_pos h]
    have hchosen : Classical.choose h = owner :=
      (fullPrunedAutomaticOwnerResourceEmbedding axis hn2 hn3 hT).injective
        ((Classical.choose_spec h).trans hraw.symm)
    rw [hchosen]

theorem gridGroupedAutomaticOwner_ne_residual
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (raw : GridGroupedAlternatingRawResource (T := T))
    (source : SharedCanonicalGroupedResidualSource axis hn2 hn3 hT assignment) :
    gridGroupedAutomaticOwner axis hn2 hn3 hT assignment raw ≠ some (.inr source) := by
  unfold gridGroupedAutomaticOwner
  split <;> simp

/-- The initial partial matching consists exactly of the automatic canonical
reservations. -/
noncomputable def gridGroupedInitialMatching
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT) :
    PartialMatching (GridGroupedAlternatingAdjacent
      axis hn2 hn3 hT assignment continuation) where
  owner := gridGroupedAutomaticOwner axis hn2 hn3 hT assignment
  owner_injective := by
    intro raw other source hraw hother
    rcases source with owner | source
    · have hr := (gridGroupedAutomaticOwner_eq_some_iff
        axis hn2 hn3 hT assignment raw owner).mp hraw
      have ho := (gridGroupedAutomaticOwner_eq_some_iff
        axis hn2 hn3 hT assignment other owner).mp hother
      exact hr.symm.trans ho
    · exact False.elim
        (gridGroupedAutomaticOwner_ne_residual
          axis hn2 hn3 hT assignment raw source hraw)
  adjacent_owner := by
    intro raw source howner
    rcases source with owner | source
    · have hraw := (gridGroupedAutomaticOwner_eq_some_iff
        axis hn2 hn3 hT assignment raw owner).mp howner
      rw [← hraw]
      exact .occupiedReservation owner
    · exact False.elim
        (gridGroupedAutomaticOwner_ne_residual
          axis hn2 hn3 hT assignment raw source howner)

/-- Alternating reachability from any grouped source in the initial matching. -/
abbrev GridGroupedAlternatingReachable
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (start : GridGroupedAlternatingSource axis hn2 hn3 hT assignment) :=
  (gridGroupedInitialMatching axis hn2 hn3 hT assignment continuation).Reachable start

/-- Source side of the alternating closure of a grouped source. -/
def gridGroupedAlternatingSourceClosure
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (start : GridGroupedAlternatingSource axis hn2 hn3 hT assignment) :
    Set (GridGroupedAlternatingSource axis hn2 hn3 hT assignment) :=
  {source | GridGroupedAlternatingReachable axis hn2 hn3 hT
    assignment continuation start (.inl source)}

/-- Resource side of the same alternating closure. -/
def gridGroupedAlternatingResourceClosure
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (start : GridGroupedAlternatingSource axis hn2 hn3 hT assignment) :
    Set (GridGroupedAlternatingRawResource (T := T)) :=
  {raw | GridGroupedAlternatingReachable axis hn2 hn3 hT
    assignment continuation start (.inr raw)}

theorem gridGroupedAlternatingSourceClosure_self
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (start : GridGroupedAlternatingSource axis hn2 hn3 hT assignment) :
    start ∈ gridGroupedAlternatingSourceClosure
      axis hn2 hn3 hT assignment continuation start :=
  (gridGroupedInitialMatching axis hn2 hn3 hT assignment continuation).reachable_root start

/-! Only source-local nonemptiness justified by the present APIs is recorded.
No claim is made that a displaced owner has an outgoing edge. -/

theorem gridGroupedAutomaticOwner_adjacent_nonempty
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (owner : FullPrunedAutomaticOwner axis hn2 hn3 hT) :
    ∃ raw, GridGroupedAlternatingAdjacent axis hn2 hn3 hT assignment continuation
      (.inl owner) raw :=
  ⟨owner.rawResource axis hn2 hn3 hT, .occupiedReservation owner⟩

theorem gridGroupedReservedUsedRoot_adjacent_nonempty
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (source : ReservedBoundaryGapUsedRootPort axis hn2 hT
      (fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment)
      (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment)) :
    ∃ raw, GridGroupedAlternatingAdjacent axis hn2 hn3 hT assignment continuation
      (.inr (.inl source)) raw :=
  ⟨.inl source.1.1, .reservedUsedRoot source⟩

/-- A reverse incoming-chain observation at the exact active root represented
by a reserved used port is grouped alternating adjacency.  This is incidence
only; it supplies no Hall inequality. -/
theorem gridGroupedReservedUsedRoot_reverse_adjacent
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (source : ReservedBoundaryGapUsedRootPort axis hn2 hT
      (fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment)
      (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment))
    (activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (source_eq : fullPrunedSharedCotreeDualHullRootPort
      axis hn2 hn3 hT assignment activeRoot = source.1.1)
    (raw : GridGroupedAlternatingRawResource (T := T))
    (hadj : FullPrunedSharedCotreeDualHullReverseRootAdjacent
      axis hn2 hn3 hT assignment activeRoot raw) :
    GridGroupedAlternatingAdjacent axis hn2 hn3 hT assignment continuation
      (.inr (.inl source)) raw :=
  .sharedHullReverseRoot source activeRoot source_eq raw hadj

theorem gridGroupedSharedHullMerger_adjacent_nonempty
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (slot : (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    ∃ raw, GridGroupedAlternatingAdjacent axis hn2 hn3 hT assignment continuation
      (.inr (.inr (.inl slot))) raw := by
  obtain ⟨raw, hraw⟩ :=
    fullPrunedSharedCotreeDualHullContinuationAdjacent_nonempty
      axis hn2 hn3 hT assignment slot
  exact ⟨raw, .sharedHullContinuation slot raw hraw⟩

theorem gridGroupedOuterCollision_adjacent_nonempty
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (collision : FullPrunedOuterCollision axis hn2 hn3 hT) :
    ∃ raw, GridGroupedAlternatingAdjacent axis hn2 hn3 hT assignment continuation
      (.inr (.inr (.inr collision))) raw :=
  ⟨.inl (collision.port axis hn2 hn3 hT), .outerDirectPort collision⟩

/-- Exit owners demonstrate why outgoing totality, and hence an unconditional
Hall conclusion, is unavailable: after displacement they have no next raw
resource. -/
theorem gridGroupedExitOwner_has_no_outgoing
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (owner : ↥(planeChannelForest axis hn2 hT).exits)
    (raw : GridGroupedAlternatingRawResource (T := T)) :
    ¬FullPrunedDisplacedOwnerOutgoingAdjacent axis hn2 hn3 hT continuation
      (.exit owner) raw :=
  fullPrunedDisplacedOwnerOutgoingAdjacent_exit
    axis hn2 hn3 hT continuation owner raw

/-! ### Optional occurrence-preserving support-edge continuation -/

/-- An entered support-edge state whose origin is one grouped alternating
source.  Its raw edge is still a single member of the existing raw resource
type; faces are occurrence state, not additional resources. -/
abbrev GridGroupedRetainedSupportEdgeState
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  RetainedSupportEdgePassThroughState
    (GridGroupedAlternatingSource axis hn2 hn3 hT assignment) T

/-- Optional policy for accepting the opposite-face continuation of an entered
support edge.  `none` adds no adjacency. -/
abbrev GridGroupedRetainedSupportEdgeContinuation
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  Option (GridGroupedRetainedSupportEdgeState axis hn2 hn3 hT assignment → Prop)

/-- The established grouped adjacency, optionally enlarged by an
occurrence-preserving pass through a retained support-support tree edge.  This
is incidence only and makes no Hall assertion. -/
inductive GridGroupedAlternatingAdjacentWithPassThrough
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (supportContinuation : GridGroupedRetainedSupportEdgeContinuation
      axis hn2 hn3 hT assignment) :
    GridGroupedAlternatingSource axis hn2 hn3 hT assignment →
      GridGroupedAlternatingRawResource (T := T) → Prop
  | base {source raw}
      (hadj : GridGroupedAlternatingAdjacent axis hn2 hn3 hT assignment
        continuation source raw) :
      GridGroupedAlternatingAdjacentWithPassThrough assignment continuation
        supportContinuation source raw
  | retainedSupportEdge
      (entered : GridGroupedRetainedSupportEdgeState
        axis hn2 hn3 hT assignment)
      (accept : GridGroupedRetainedSupportEdgeState
        axis hn2 hn3 hT assignment → Prop)
      (henabled : supportContinuation = some accept)
      (haccept : accept entered.passThrough) :
      GridGroupedAlternatingAdjacentWithPassThrough assignment continuation
        supportContinuation entered.origin (.inr (.inl entered.raw))

/-- With no support-edge continuation policy, the optional relation is exactly
the original grouped adjacency. -/
theorem gridGroupedAlternatingAdjacentWithPassThrough_none_iff
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (source : GridGroupedAlternatingSource axis hn2 hn3 hT assignment)
    (raw : GridGroupedAlternatingRawResource (T := T)) :
    GridGroupedAlternatingAdjacentWithPassThrough axis hn2 hn3 hT assignment
        continuation none source raw ↔
      GridGroupedAlternatingAdjacent axis hn2 hn3 hT assignment continuation
        source raw := by
  constructor
  · intro hadj
    cases hadj with
    | base h => exact h
    | retainedSupportEdge _ _ henabled _ => cases henabled
  · exact GridGroupedAlternatingAdjacentWithPassThrough.base

/-- The optional continuation exposes exactly the pre-existing raw edge and
preserves the initiating grouped occurrence. -/
theorem gridGrouped_retainedSupportEdge_adjacent
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (entered : GridGroupedRetainedSupportEdgeState
      axis hn2 hn3 hT assignment)
    (accept : GridGroupedRetainedSupportEdgeState
      axis hn2 hn3 hT assignment → Prop)
    (haccept : accept entered.passThrough) :
    GridGroupedAlternatingAdjacentWithPassThrough axis hn2 hn3 hT assignment
      continuation (some accept) entered.origin (.inr (.inl entered.raw)) :=
  .retainedSupportEdge entered accept rfl haccept

/-! ### Optional physical saturation by component-contact exchange -/

/-- One grouped occurrence at a raw-component contact together with its
certified tree-basis exchange.  The contact edge and cotree edge are provenance;
`component` is the only physical resource exposed by this state. -/
structure GridGroupedRawComponentTreeBasisExchangeState
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) where
  component : ContactRawComponent (T := T)
  state : RawFreeComponentContinuationState axis hn2 hT
    (GridGroupedAlternatingSource axis hn2 hn3 hT assignment) component
  exchange : RawFreeComponentTreeBasisExchange axis hn2 hT state

namespace GridGroupedRawComponentTreeBasisExchangeState

variable {root : GridVertex n n}
  {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}

/-- The initiating grouped occurrence. -/
def origin
    (entered : GridGroupedRawComponentTreeBasisExchangeState
      axis hn2 hn3 hT assignment) :
    GridGroupedAlternatingSource axis hn2 hn3 hT assignment :=
  entered.state.origin

/-- The one-copy raw component represented by this contact state. -/
def rawResource
    (entered : GridGroupedRawComponentTreeBasisExchangeState
      axis hn2 hn3 hT assignment) :
    GridGroupedAlternatingRawResource (T := T) :=
  .inr (.inr entered.component)

/-- The certified continuation at the inserted cotree edge's opposite face. -/
def continuationState
    (entered : GridGroupedRawComponentTreeBasisExchangeState
      axis hn2 hn3 hT assignment) :=
  entered.exchange.continuationState

@[simp] theorem continuationState_origin
    (entered : GridGroupedRawComponentTreeBasisExchangeState
      axis hn2 hn3 hT assignment) :
    entered.continuationState.origin = entered.origin := rfl

theorem exchange_isGridSpanningSubtree
    (entered : GridGroupedRawComponentTreeBasisExchangeState
      axis hn2 hn3 hT assignment) :
    IsSpanningSubtree (gridGraph n n)
      (entered.exchange.contact.retainedTreeContactEdge.basisExchange
        entered.exchange.cotree.1) :=
  entered.exchange.isGridSpanningSubtree

end GridGroupedRawComponentTreeBasisExchangeState

/-- Optional policy enabling certified component-contact exchanges. -/
abbrev GridGroupedRawComponentTreeBasisExchangeContinuation
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  Option (GridGroupedRawComponentTreeBasisExchangeState
    axis hn2 hn3 hT assignment → Prop)

/-- Existing grouped adjacency and retained-edge pass-through, optionally
saturated by certified component-contact tree-basis exchanges.  This remains an
incidence relation and asserts no Hall condition. -/
inductive GridGroupedAlternatingAdjacentWithPhysicalSaturation
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (supportContinuation : GridGroupedRetainedSupportEdgeContinuation
      axis hn2 hn3 hT assignment)
    (componentContinuation : GridGroupedRawComponentTreeBasisExchangeContinuation
      axis hn2 hn3 hT assignment) :
    GridGroupedAlternatingSource axis hn2 hn3 hT assignment →
      GridGroupedAlternatingRawResource (T := T) → Prop
  | base {source raw}
      (hadj : GridGroupedAlternatingAdjacentWithPassThrough axis hn2 hn3 hT
        assignment continuation supportContinuation source raw) :
      GridGroupedAlternatingAdjacentWithPhysicalSaturation assignment continuation
        supportContinuation componentContinuation source raw
  | componentTreeBasisExchange
      (entered : GridGroupedRawComponentTreeBasisExchangeState
        axis hn2 hn3 hT assignment)
      (accept : GridGroupedRawComponentTreeBasisExchangeState
        axis hn2 hn3 hT assignment → Prop)
      (henabled : componentContinuation = some accept)
      (haccept : accept entered) :
      GridGroupedAlternatingAdjacentWithPhysicalSaturation assignment continuation
        supportContinuation componentContinuation entered.origin entered.rawResource

/-- Disabling component-contact exchange recovers exactly the existing optional
retained-edge relation. -/
theorem gridGroupedAlternatingAdjacentWithPhysicalSaturation_none_iff
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (supportContinuation : GridGroupedRetainedSupportEdgeContinuation
      axis hn2 hn3 hT assignment)
    (source : GridGroupedAlternatingSource axis hn2 hn3 hT assignment)
    (raw : GridGroupedAlternatingRawResource (T := T)) :
    GridGroupedAlternatingAdjacentWithPhysicalSaturation axis hn2 hn3 hT
        assignment continuation supportContinuation none source raw ↔
      GridGroupedAlternatingAdjacentWithPassThrough axis hn2 hn3 hT assignment
        continuation supportContinuation source raw := by
  constructor
  · intro hadj
    cases hadj with
    | base h => exact h
    | componentTreeBasisExchange _ _ henabled _ => cases henabled
  · exact GridGroupedAlternatingAdjacentWithPhysicalSaturation.base

/-- An enabled contact exchange exposes the existing one-copy raw component
while retaining the initiating grouped occurrence. -/
theorem gridGrouped_rawComponentTreeBasisExchange_adjacent
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (supportContinuation : GridGroupedRetainedSupportEdgeContinuation
      axis hn2 hn3 hT assignment)
    (entered : GridGroupedRawComponentTreeBasisExchangeState
      axis hn2 hn3 hT assignment)
    (accept : GridGroupedRawComponentTreeBasisExchangeState
      axis hn2 hn3 hT assignment → Prop)
    (haccept : accept entered) :
    GridGroupedAlternatingAdjacentWithPhysicalSaturation axis hn2 hn3 hT
      assignment continuation supportContinuation (some accept)
        entered.origin entered.rawResource :=
  .componentTreeBasisExchange entered accept rfl haccept

end

end CanonicalExpandedContourForest

end GridGraphs
