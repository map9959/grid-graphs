import GridGraphs.GridGroupedAlternatingMatching
import GridGraphs.OrderedOuterBoundaryExchange

/-!
# Finite physical saturation transition system

This module combines the occurrence-labelled continuation mechanisms used by
the grouped alternating construction.  States are indexed by the grouped
source which initiated the search, while observations always land in the
one-copy raw physical resource type.  In particular, occurrence states do not
create additional physical resources.  No Hall assertion is made.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace CanonicalExpandedContourForest

variable {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
  {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
  (hT : IsSpanningSubtree (gridGraph n n) T)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

variable {root : GridVertex n n}
  (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)

abbrev GridPhysicalSaturationSource :=
  GridGroupedAlternatingSource axis hn2 hn3 hT assignment

abbrev GridPhysicalSaturationRawResource :=
  GridGroupedAlternatingRawResource (T := T)

/-- All certified grouped incidences are enabled in the saturation system.
The predicates are `True`; the certificates carried by the entered states are
still required. -/
abbrev GridPhysicalSaturationAdjacent
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT) :=
  GridGroupedAlternatingAdjacentWithPhysicalSaturation axis hn2 hn3 hT
    assignment continuation (some fun _ => True) (some fun _ => True)

private def outerTraversalDirectionCode : OuterTraversalDirection → Bool
  | .clockwise => false
  | .counterclockwise => true

private theorem outerTraversalDirectionCode_injective :
    Function.Injective outerTraversalDirectionCode := by
  intro a b h
  cases a <;> cases b <;> simp [outerTraversalDirectionCode] at h ⊢

private noncomputable instance outerTraversalDirectionFinite :
    Finite OuterTraversalDirection :=
  Finite.of_injective outerTraversalDirectionCode
    outerTraversalDirectionCode_injective

private noncomputable instance outerTraversalDirectionFintype :
    Fintype OuterTraversalDirection := Fintype.ofFinite _

private def fullPrunedAutomaticOwnerCode :
    FullPrunedAutomaticOwner axis hn2 hn3 hT →
      ↥(planeChannelForest axis hn2 hT).exits ⊕
        (InternalTreeEdgeToken (supportFinset (gridGraph n n \ T))
          (terminalTreeEdgeEmbedding axis hn2 hn3 hT) ⊕
        CarrierQuotient (FullPrunedTokenCarrier axis hn2 hn3 hT))
  | .exit owner => .inl owner
  | .internalToken owner => .inr (.inl owner)
  | .carrierQuotient owner => .inr (.inr owner)

private theorem fullPrunedAutomaticOwnerCode_injective :
    Function.Injective (fullPrunedAutomaticOwnerCode axis hn2 hn3 hT) := by
  intro a b h
  cases a <;> cases b
  · exact congrArg FullPrunedAutomaticOwner.exit (Sum.inl.inj h)
  · simp [fullPrunedAutomaticOwnerCode] at h
  · simp [fullPrunedAutomaticOwnerCode] at h
  · simp [fullPrunedAutomaticOwnerCode] at h
  · exact congrArg FullPrunedAutomaticOwner.internalToken
      (Sum.inl.inj (Sum.inr.inj h))
  · simp [fullPrunedAutomaticOwnerCode] at h
  · simp [fullPrunedAutomaticOwnerCode] at h
  · simp [fullPrunedAutomaticOwnerCode] at h
  · exact congrArg FullPrunedAutomaticOwner.carrierQuotient
      (Sum.inr.inj (Sum.inr.inj h))

private noncomputable instance fullPrunedAutomaticOwnerFinite :
    Finite (FullPrunedAutomaticOwner axis hn2 hn3 hT) :=
  Finite.of_injective (fullPrunedAutomaticOwnerCode axis hn2 hn3 hT)
    (fullPrunedAutomaticOwnerCode_injective axis hn2 hn3 hT)

private noncomputable instance gridPhysicalSaturationSourceFintype :
    Fintype (GridPhysicalSaturationSource axis hn2 hn3 hT assignment) :=
  Fintype.ofFinite _

private def retainedSupportEdgeStateCode
    (state : GridGroupedRetainedSupportEdgeState axis hn2 hn3 hT assignment) :=
  (state.origin, state.enteredFace, state.enteredEdge, state.raw)

private theorem retainedSupportEdgeStateCode_injective :
    Function.Injective
      (retainedSupportEdgeStateCode axis hn2 hn3 hT assignment) := by
  intro a b h
  rcases a with ⟨aOrigin, aFace, aEdge, aRaw, aEq, aIncident⟩
  rcases b with ⟨bOrigin, bFace, bEdge, bRaw, bEq, bIncident⟩
  simp only [retainedSupportEdgeStateCode, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

private noncomputable instance retainedSupportEdgeStateFinite :
    Finite (GridGroupedRetainedSupportEdgeState axis hn2 hn3 hT assignment) :=
  Finite.of_injective
    (retainedSupportEdgeStateCode axis hn2 hn3 hT assignment)
    (retainedSupportEdgeStateCode_injective axis hn2 hn3 hT assignment)

private def rawFreeComponentBoundaryContactCode
    {component : ContactRawComponent (T := T)}
    (contact : RawFreeComponentBoundaryContact (T := T) component) :=
  (contact.resource, contact.retainedDart)

private theorem rawFreeComponentBoundaryContactCode_injective
    {component : ContactRawComponent (T := T)} :
    Function.Injective (rawFreeComponentBoundaryContactCode (T := T)
      (component := component)) := by
  intro a b h
  rcases a with ⟨aResource, aEq, aBoundary, aDart, aSource, aTarget⟩
  rcases b with ⟨bResource, bEq, bBoundary, bDart, bSource, bTarget⟩
  simp only [rawFreeComponentBoundaryContactCode, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

private noncomputable instance rawFreeComponentBoundaryContactFinite
    (component : ContactRawComponent (T := T)) :
    Finite (RawFreeComponentBoundaryContact (T := T) component) :=
  Finite.of_injective (rawFreeComponentBoundaryContactCode (T := T))
    rawFreeComponentBoundaryContactCode_injective

private noncomputable instance rawFreeComponentBoundaryContactFintype
    (component : ContactRawComponent (T := T)) :
    Fintype (RawFreeComponentBoundaryContact (T := T) component) :=
  Fintype.ofFinite _

private noncomputable instance componentSpatialGapFintype
    (component : ContactRawComponent (T := T)) :
    Fintype (ComponentSpatialGap axis hn2 hT component) :=
  rankedCarrierCollisionFintype _ _

private noncomputable instance rawFreeComponentContinuationCarrierFintype
    (component : ContactRawComponent (T := T)) :
    Fintype (RawFreeComponentContinuationCarrier axis hn2 hT component) :=
  inferInstance

private def rawFreeComponentContinuationStateCode
    {component : ContactRawComponent (T := T)}
    (state : RawFreeComponentContinuationState axis hn2 hT
      (GridPhysicalSaturationSource axis hn2 hn3 hT assignment) component) :=
  (state.origin, state.entry, state.position)

private theorem rawFreeComponentContinuationStateCode_injective
    {component : ContactRawComponent (T := T)} :
    Function.Injective (rawFreeComponentContinuationStateCode
      axis hn2 hn3 hT assignment (component := component)) := by
  intro a b h
  rcases a with ⟨aOrigin, aEntry, aPosition⟩
  rcases b with ⟨bOrigin, bEntry, bPosition⟩
  simp only [rawFreeComponentContinuationStateCode, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

private noncomputable instance rawFreeComponentContinuationStateFinite
    (component : ContactRawComponent (T := T)) :
    Finite (RawFreeComponentContinuationState axis hn2 hT
      (GridPhysicalSaturationSource axis hn2 hn3 hT assignment) component) :=
  Finite.of_injective
    (rawFreeComponentContinuationStateCode axis hn2 hn3 hT assignment)
    (rawFreeComponentContinuationStateCode_injective axis hn2 hn3 hT assignment)

private def orderedOuterTraversalStateCode
    (state : OrderedOuterTraversalState (T := T)
      (GridPhysicalSaturationSource axis hn2 hn3 hT assignment)) :=
  (state.origin, state.port)

private theorem orderedOuterTraversalStateCode_injective :
    Function.Injective (orderedOuterTraversalStateCode axis hn2 hn3 hT assignment) := by
  intro a b h
  rcases a with ⟨aOrigin, aPort⟩
  rcases b with ⟨bOrigin, bPort⟩
  simpa [orderedOuterTraversalStateCode] using h

private noncomputable instance orderedOuterTraversalStateFinite :
    Finite (OrderedOuterTraversalState (T := T)
      (GridPhysicalSaturationSource axis hn2 hn3 hT assignment)) :=
  Finite.of_injective (orderedOuterTraversalStateCode axis hn2 hn3 hT assignment)
    (orderedOuterTraversalStateCode_injective axis hn2 hn3 hT assignment)

/-- Finite occurrence state indexed by the grouped source which initiated the
search.  Equality proofs pin the origins stored by the existing continuation
APIs to that index. -/
inductive GridPhysicalSaturationState
    (initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment) where
  | alternating
      (vertex : GridPhysicalSaturationSource axis hn2 hn3 hT assignment ⊕
        GridPhysicalSaturationRawResource (T := T))
  | support
      (state : GridGroupedRetainedSupportEdgeState axis hn2 hn3 hT assignment)
      (origin_eq : state.origin = initiating)
  | component
      (component : ContactRawComponent (T := T))
      (state : RawFreeComponentContinuationState axis hn2 hT
        (GridPhysicalSaturationSource axis hn2 hn3 hT assignment) component)
      (origin_eq : state.origin = initiating)
  | outer
      (direction : OuterTraversalDirection)
      (state : OrderedOuterTraversalState (T := T)
        (GridPhysicalSaturationSource axis hn2 hn3 hT assignment))
      (origin_eq : state.origin = initiating)

private def gridPhysicalSaturationStateCode
    {initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment} :
    GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating →
      (GridPhysicalSaturationSource axis hn2 hn3 hT assignment ⊕
          GridPhysicalSaturationRawResource (T := T)) ⊕
        (GridGroupedRetainedSupportEdgeState axis hn2 hn3 hT assignment ⊕
          ((Σ component : ContactRawComponent (T := T),
              RawFreeComponentContinuationState axis hn2 hT
                (GridPhysicalSaturationSource axis hn2 hn3 hT assignment) component) ⊕
            (OuterTraversalDirection × OrderedOuterTraversalState (T := T)
              (GridPhysicalSaturationSource axis hn2 hn3 hT assignment))))
  | .alternating vertex => .inl vertex
  | .support state _ => .inr (.inl state)
  | .component component state _ => .inr (.inr (.inl ⟨component, state⟩))
  | .outer direction state _ => .inr (.inr (.inr (direction, state)))

private theorem gridPhysicalSaturationStateCode_injective
    {initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment} :
    Function.Injective
      (gridPhysicalSaturationStateCode axis hn2 hn3 hT assignment
        (initiating := initiating)) := by
  intro a b h
  cases a <;> cases b <;>
    simp_all [gridPhysicalSaturationStateCode]

private noncomputable instance gridPhysicalSaturationStateFinite
    (initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment) :
    Finite (GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating) :=
  Finite.of_injective
    (gridPhysicalSaturationStateCode axis hn2 hn3 hT assignment)
    (gridPhysicalSaturationStateCode_injective axis hn2 hn3 hT assignment)

noncomputable instance gridPhysicalSaturationStateFintype
    (initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment) :
    Fintype (GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating) :=
  Fintype.ofFinite _

noncomputable instance gridPhysicalSaturationStateDecidableEq
    (initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment) :
    DecidableEq
      (GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating) :=
  Classical.decEq _

/-- The initial occurrence of a grouped source. -/
def gridPhysicalSaturationStart
    (initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment) :
    GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating :=
  .alternating (.inl initiating)

/-- Physical observation made by a saturation state.  Detailed support,
component, and boundary occurrences expose the same raw resource as the
grouped layer, never a labelled copy. -/
def GridPhysicalSaturationState.rawResource?
    {initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment} :
    GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating →
      Option (GridPhysicalSaturationRawResource (T := T))
  | .alternating (.inl _) => none
  | .alternating (.inr raw) => some raw
  | .support state _ => some (.inr (.inl state.raw))
  | .component rawComponent _ _ => some (.inr (.inr rawComponent))
  | .outer _ state _ => some (.inl state.port)

/-- Every state reports its initiating grouped occurrence through its index. -/
def GridPhysicalSaturationState.origin
    {initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment}
    (_ : GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating) :=
  initiating

/-- Unified physical saturation step.  The three `enter` constructors refine a
raw observation to occurrence-labelled state; all subsequent constructors are
the corresponding established continuation relations. -/
inductive GridPhysicalSaturationStep
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    {initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment} :
    GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating →
      GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating → Prop
  | adjacent {source raw}
      (hadj : GridPhysicalSaturationAdjacent axis hn2 hn3 hT assignment
        continuation source raw) :
      GridPhysicalSaturationStep continuation (.alternating (.inl source))
        (.alternating (.inr raw))
  | displace {raw owner}
      (howner : gridGroupedAutomaticOwner axis hn2 hn3 hT assignment raw =
        some (.inl owner)) :
      GridPhysicalSaturationStep continuation (.alternating (.inr raw))
        (.alternating (.inl (.inl owner)))
  | enterSupport
      (entered : GridGroupedRetainedSupportEdgeState axis hn2 hn3 hT assignment)
      (origin_eq : entered.origin = initiating) :
      GridPhysicalSaturationStep continuation
        (.alternating (.inr (.inr (.inl entered.raw))))
        (.support entered origin_eq)
  | supportPassThrough
      (entered : GridGroupedRetainedSupportEdgeState axis hn2 hn3 hT assignment)
      (origin_eq : entered.origin = initiating) :
      GridPhysicalSaturationStep continuation (.support entered origin_eq)
        (.support entered.passThrough (by simpa using origin_eq))
  | enterComponent
      (component : ContactRawComponent (T := T))
      (entered : RawFreeComponentContinuationState axis hn2 hT
        (GridPhysicalSaturationSource axis hn2 hn3 hT assignment) component)
      (origin_eq : entered.origin = initiating) :
      GridPhysicalSaturationStep continuation
        (.alternating (.inr (.inr (.inr component))))
        (.component component entered origin_eq)
  | componentContinuation
      {component : ContactRawComponent (T := T)}
      {entered next : RawFreeComponentContinuationState axis hn2 hT
        (GridPhysicalSaturationSource axis hn2 hn3 hT assignment) component}
      (origin_eq : entered.origin = initiating)
      (step : RawFreeComponentContinuation axis hn2 hT entered next) :
      GridPhysicalSaturationStep continuation (.component component entered origin_eq)
        (.component component next (by
          rw [RawFreeComponentContinuation.origin_eq axis hn2 hT step, origin_eq]))
  | enterOuter
      (direction : OuterTraversalDirection)
      (entered : OrderedOuterTraversalState (T := T)
        (GridPhysicalSaturationSource axis hn2 hn3 hT assignment))
      (origin_eq : entered.origin = initiating) :
      GridPhysicalSaturationStep continuation
        (.alternating (.inr (.inl entered.port)))
        (.outer direction entered origin_eq)
  | outerReserved
      {direction : OuterTraversalDirection}
      {entered next : OrderedOuterTraversalState (T := T)
        (GridPhysicalSaturationSource axis hn2 hn3 hT assignment)}
      (origin_eq : entered.origin = initiating)
      (step : OrderedOuterTraversalStep axis hn2 hT direction entered next) :
      GridPhysicalSaturationStep continuation (.outer direction entered origin_eq)
        (.outer direction next (by
          rw [orderedOuterTraversalStep_origin_eq axis hn2 hT direction step, origin_eq]))

/-- Reachability from the indexed initiating occurrence. -/
def GridPhysicalSaturationReachable
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment)
    (state : GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating) : Prop :=
  Relation.ReflTransGen
    (GridPhysicalSaturationStep axis hn2 hn3 hT assignment continuation)
    (gridPhysicalSaturationStart axis hn2 hn3 hT assignment initiating) state

/-- The finite, one-copy raw neighborhood observed by all reachable occurrence
states. -/
def gridPhysicalSaturationNeighborhood
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment) :
    Finset (GridPhysicalSaturationRawResource (T := T)) :=
  Finset.univ.filter fun raw => ∃ state,
    GridPhysicalSaturationReachable axis hn2 hn3 hT assignment continuation
      initiating state ∧ state.rawResource? = some raw

@[simp] theorem mem_gridPhysicalSaturationNeighborhood
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment)
    (raw : GridPhysicalSaturationRawResource (T := T)) :
    raw ∈ gridPhysicalSaturationNeighborhood axis hn2 hn3 hT assignment
        continuation initiating ↔
      ∃ state, GridPhysicalSaturationReachable axis hn2 hn3 hT assignment
          continuation initiating state ∧ state.rawResource? = some raw := by
  simp [gridPhysicalSaturationNeighborhood]

/-- The index makes origin preservation intrinsic to every transition. -/
theorem gridPhysicalSaturationStep_origin_preserved
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    {initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment}
    {x y : GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating}
    (_ : GridPhysicalSaturationStep axis hn2 hn3 hT assignment continuation x y) :
    y.origin = x.origin :=
  rfl

theorem gridPhysicalSaturationReachable_origin_preserved
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    {initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment}
    {state : GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating}
    (_ : GridPhysicalSaturationReachable axis hn2 hn3 hT assignment continuation
      initiating state) :
    state.origin =
      (gridPhysicalSaturationStart axis hn2 hn3 hT assignment initiating).origin :=
  rfl

/-- Any enabled grouped physical adjacency is one saturation step, hence is
reachable whenever its source state is reachable. -/
theorem gridPhysicalSaturation_reachable_of_adjacent
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    {initiating source : GridPhysicalSaturationSource axis hn2 hn3 hT assignment}
    {raw : GridPhysicalSaturationRawResource (T := T)}
    (hsource : GridPhysicalSaturationReachable axis hn2 hn3 hT assignment
      continuation initiating (.alternating (.inl source)))
    (hadj : GridPhysicalSaturationAdjacent axis hn2 hn3 hT assignment
      continuation source raw) :
    GridPhysicalSaturationReachable axis hn2 hn3 hT assignment continuation
      initiating (.alternating (.inr raw)) :=
  hsource.tail (.adjacent hadj)

theorem gridPhysicalSaturation_baseAdjacent
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    {source : GridPhysicalSaturationSource axis hn2 hn3 hT assignment}
    {raw : GridPhysicalSaturationRawResource (T := T)}
    (hadj : GridGroupedAlternatingAdjacent axis hn2 hn3 hT assignment
      continuation source raw) :
    GridPhysicalSaturationAdjacent axis hn2 hn3 hT assignment continuation
      source raw :=
  .base (.base hadj)

/-- The established internal-edge pass-through incidence is enabled by the
unified adjacency. -/
theorem gridPhysicalSaturation_supportAdjacent
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (entered : GridGroupedRetainedSupportEdgeState axis hn2 hn3 hT assignment) :
    GridPhysicalSaturationAdjacent axis hn2 hn3 hT assignment continuation
      entered.origin (.inr (.inl entered.raw)) :=
  .base (.retainedSupportEdge entered (fun _ => True) rfl trivial)

/-- Every certified raw-component contact basis exchange is enabled and
observes its one-copy raw component. -/
theorem gridPhysicalSaturation_contactBasisExchangeAdjacent
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (entered : GridGroupedRawComponentTreeBasisExchangeState
      axis hn2 hn3 hT assignment) :
    GridPhysicalSaturationAdjacent axis hn2 hn3 hT assignment continuation
      entered.origin entered.rawResource :=
  .componentTreeBasisExchange entered (fun _ => True) rfl trivial

/-- Automatic ownership displacement is the forced resource-to-source half of
the unified transition system. -/
theorem gridPhysicalSaturation_reachable_owner_of_resource
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    {initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment}
    {raw : GridPhysicalSaturationRawResource (T := T)}
    {owner : FullPrunedAutomaticOwner axis hn2 hn3 hT}
    (hraw : GridPhysicalSaturationReachable axis hn2 hn3 hT assignment
      continuation initiating (.alternating (.inr raw)))
    (howner : gridGroupedAutomaticOwner axis hn2 hn3 hT assignment raw =
      some (.inl owner)) :
    GridPhysicalSaturationReachable axis hn2 hn3 hT assignment continuation
      initiating (.alternating (.inl (.inl owner))) :=
  hraw.tail (.displace howner)

theorem gridPhysicalSaturation_reverseRootAdjacent
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (source : ReservedBoundaryGapUsedRootPort axis hn2 hT
      (fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment)
      (fullPrunedSharedCotreeDualHullRootPort axis hn2 hn3 hT assignment))
    (activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (source_eq : fullPrunedSharedCotreeDualHullRootPort
      axis hn2 hn3 hT assignment activeRoot = source.1.1)
    (raw : GridPhysicalSaturationRawResource (T := T))
    (hadj : FullPrunedSharedCotreeDualHullReverseRootAdjacent
      axis hn2 hn3 hT assignment activeRoot raw) :
    GridPhysicalSaturationAdjacent axis hn2 hn3 hT assignment continuation
      (.inr (.inl source)) raw :=
  gridPhysicalSaturation_baseAdjacent axis hn2 hn3 hT assignment continuation
    (.sharedHullReverseRoot source activeRoot source_eq raw hadj)

theorem gridPhysicalSaturation_supportPassThrough
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    {initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment}
    (entered : GridGroupedRetainedSupportEdgeState axis hn2 hn3 hT assignment)
    (origin_eq : entered.origin = initiating) :
    Relation.ReflTransGen
      (GridPhysicalSaturationStep axis hn2 hn3 hT assignment continuation)
      (.support entered origin_eq)
      (.support entered.passThrough (by simpa using origin_eq)) :=
  Relation.ReflTransGen.single (.supportPassThrough entered origin_eq)

theorem gridPhysicalSaturation_componentContinuation
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    {initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment}
    {component : ContactRawComponent (T := T)}
    {entered next : RawFreeComponentContinuationState axis hn2 hT
      (GridPhysicalSaturationSource axis hn2 hn3 hT assignment) component}
    (origin_eq : entered.origin = initiating)
    (step : RawFreeComponentContinuation axis hn2 hT entered next) :
    ∃ next_origin_eq,
      Relation.ReflTransGen
        (GridPhysicalSaturationStep axis hn2 hn3 hT assignment continuation)
        (.component component entered origin_eq)
        (.component component next next_origin_eq) := by
  refine ⟨?_, Relation.ReflTransGen.single (.componentContinuation origin_eq step)⟩
  rw [RawFreeComponentContinuation.origin_eq axis hn2 hT step, origin_eq]

theorem gridPhysicalSaturation_outerTraversal
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    {initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment}
    {direction : OuterTraversalDirection}
    {entered next : OrderedOuterTraversalState (T := T)
      (GridPhysicalSaturationSource axis hn2 hn3 hT assignment)}
    (origin_eq : entered.origin = initiating)
    (step : OrderedOuterTraversalStep axis hn2 hT direction entered next) :
    ∃ next_origin_eq,
      Relation.ReflTransGen
        (GridPhysicalSaturationStep axis hn2 hn3 hT assignment continuation)
        (.outer direction entered origin_eq)
        (.outer direction next next_origin_eq) := by
  refine ⟨?_, Relation.ReflTransGen.single (.outerReserved origin_eq step)⟩
  rw [orderedOuterTraversalStep_origin_eq axis hn2 hT direction step, origin_eq]

/-! ### Finite iteration -/

/-- Inductive bounded reachability used to specify finite iteration without
choosing a particular path representation. -/
inductive GridPhysicalSaturationAtMost
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment) :
    Nat → GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating → Prop
  | zero : GridPhysicalSaturationAtMost continuation initiating 0
      (gridPhysicalSaturationStart axis hn2 hn3 hT assignment initiating)
  | stay {steps state} (reached : GridPhysicalSaturationAtMost continuation
      initiating steps state) :
      GridPhysicalSaturationAtMost continuation initiating (steps + 1) state
  | tail {steps previous state}
      (reached : GridPhysicalSaturationAtMost continuation initiating steps previous)
      (step : GridPhysicalSaturationStep axis hn2 hn3 hT assignment continuation
        previous state) :
      GridPhysicalSaturationAtMost continuation initiating (steps + 1) state

/-- States reachable in at most `steps` saturation steps. -/
def gridPhysicalSaturationIteration
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment) :
    Nat → Finset (GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating)
  | 0 => {gridPhysicalSaturationStart axis hn2 hn3 hT assignment initiating}
  | steps + 1 => Finset.univ.filter fun state =>
      state ∈ gridPhysicalSaturationIteration continuation initiating steps ∨
        ∃ previous ∈ gridPhysicalSaturationIteration continuation initiating steps,
          GridPhysicalSaturationStep axis hn2 hn3 hT assignment continuation
            previous state

/-- Iterating the finite transition operator is exactly inductive bounded
reachability. -/
theorem mem_gridPhysicalSaturationIteration_iff
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment) :
    ∀ steps state,
      state ∈ gridPhysicalSaturationIteration axis hn2 hn3 hT assignment
          continuation initiating steps ↔
        GridPhysicalSaturationAtMost axis hn2 hn3 hT assignment continuation
          initiating steps state := by
  intro steps
  induction steps with
  | zero =>
      intro state
      simp only [gridPhysicalSaturationIteration, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact .zero
      · intro reached
        cases reached
        rfl
  | succ steps ih =>
      intro state
      simp only [gridPhysicalSaturationIteration, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro (hold | ⟨previous, hprevious, hstep⟩)
        · exact .stay ((ih state).mp hold)
        · exact .tail ((ih previous).mp hprevious) hstep
      · intro reached
        cases reached with
        | stay previous => exact Or.inl ((ih state).mpr previous)
        | tail previous step => exact Or.inr ⟨_, (ih _).mpr previous, step⟩

/-- Unbounded saturation reachability is membership in some finite iterate. -/
theorem gridPhysicalSaturation_reachable_iff_exists_iteration
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (initiating : GridPhysicalSaturationSource axis hn2 hn3 hT assignment)
    (state : GridPhysicalSaturationState axis hn2 hn3 hT assignment initiating) :
    GridPhysicalSaturationReachable axis hn2 hn3 hT assignment continuation
        initiating state ↔
      ∃ steps, state ∈ gridPhysicalSaturationIteration axis hn2 hn3 hT assignment
        continuation initiating steps := by
  constructor
  · intro path
    induction path with
    | refl =>
        exact ⟨0, (mem_gridPhysicalSaturationIteration_iff
          axis hn2 hn3 hT assignment continuation initiating 0 _).mpr .zero⟩
    | tail path step ih =>
        obtain ⟨steps, hsteps⟩ := ih
        exact ⟨steps + 1, (mem_gridPhysicalSaturationIteration_iff
          axis hn2 hn3 hT assignment continuation initiating (steps + 1) _).mpr
            (.tail ((mem_gridPhysicalSaturationIteration_iff
              axis hn2 hn3 hT assignment continuation initiating steps _).mp hsteps)
              step)⟩
  · rintro ⟨steps, hstate⟩
    have bounded := (mem_gridPhysicalSaturationIteration_iff
      axis hn2 hn3 hT assignment continuation initiating steps state).mp hstate
    clear hstate
    induction bounded with
    | zero => exact Relation.ReflTransGen.refl
    | stay _ ih => exact ih
    | tail _ step ih => exact ih.tail step

end

end CanonicalExpandedContourForest

end GridGraphs
