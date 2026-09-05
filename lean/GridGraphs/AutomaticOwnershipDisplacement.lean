import GridGraphs.CanonicalReconvergenceLens

/-!
# Automatic ownership and displacement

This module packages the three canonical reservations as actual owners.  Raw
components remain quotient classes on the automatic source side, while ranked
collisions retain their occurrence labels.  No total adjacency, Hall theorem,
or universal-waste conclusion is asserted here.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace CanonicalExpandedContourForest

variable {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
  {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
  (hT : IsSpanningSubtree (gridGraph n n) T)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- An owner installed before any repeated-carrier displacement search.  The
three cases are exactly the canonical exit, internal-token, and one-per-carrier
quotient reservations. -/
inductive FullPrunedAutomaticOwner where
  | exit (owner : ↥(planeChannelForest axis hn2 hT).exits)
  | internalToken (owner : InternalTreeEdgeToken
      (supportFinset (gridGraph n n \ T))
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT))
  | carrierQuotient (owner : CarrierQuotient
      (FullPrunedTokenCarrier axis hn2 hn3 hT))

/-- The pruned forest source represented by an automatic owner.  A quotient
owner uses one canonical representative token; no collision occurrence is
forgotten because collisions do not inhabit `FullPrunedAutomaticOwner`. -/
noncomputable def FullPrunedAutomaticOwner.source :
    FullPrunedAutomaticOwner axis hn2 hn3 hT →
      FullPrunedSource axis hn2 hT
  | .exit owner => .inl owner
  | .internalToken owner => .inr owner.1
  | .carrierQuotient owner => .inr
      (rankedCarrierRepresentative
        (FullPrunedTokenCarrier axis hn2 hn3 hT)
        (fullPrunedTokenRank axis hn2 hn3 hT) owner).1

/-- Raw physical resource reserved by an automatic owner. -/
def FullPrunedAutomaticOwner.rawResource :
    FullPrunedAutomaticOwner axis hn2 hn3 hT →
      PlanarLensRawPhysicalResource (T := T)
  | .exit owner => .inl (exitEmbedding axis hn2 hT owner)
  | .internalToken owner => .inr (.inl
      (internalTreeEdgeTokenEmbedding
        (supportFinset (gridGraph n n \ T))
        (terminalTreeEdgeEmbedding axis hn2 hn3 hT) owner))
  | .carrierQuotient owner => .inr (.inr
      (carrierQuotientEmbedding
        (FullPrunedTokenCarrier axis hn2 hn3 hT) owner))

/-- Automatic owners embed injectively into raw physical resources.  In
particular, the quotient case reserves one raw component, not one resource per
token occurrence. -/
def fullPrunedAutomaticOwnerResourceEmbedding :
    FullPrunedAutomaticOwner axis hn2 hn3 hT ↪
      PlanarLensRawPhysicalResource (T := T) where
  toFun := FullPrunedAutomaticOwner.rawResource axis hn2 hn3 hT
  inj' := by
    intro a b hab
    rcases a with a | a | a <;> rcases b with b | b | b
    · exact congrArg FullPrunedAutomaticOwner.exit
        ((exitEmbedding axis hn2 hT).injective (Sum.inl.inj hab))
    · simp [FullPrunedAutomaticOwner.rawResource] at hab
    · simp [FullPrunedAutomaticOwner.rawResource] at hab
    · simp [FullPrunedAutomaticOwner.rawResource] at hab
    · exact congrArg FullPrunedAutomaticOwner.internalToken
        ((internalTreeEdgeTokenEmbedding
          (supportFinset (gridGraph n n \ T))
          (terminalTreeEdgeEmbedding axis hn2 hn3 hT)).injective
            (Sum.inl.inj (Sum.inr.inj hab)))
    · simp [FullPrunedAutomaticOwner.rawResource] at hab
    · simp [FullPrunedAutomaticOwner.rawResource] at hab
    · simp [FullPrunedAutomaticOwner.rawResource] at hab
    · exact congrArg FullPrunedAutomaticOwner.carrierQuotient
        ((carrierQuotientEmbedding
          (FullPrunedTokenCarrier axis hn2 hn3 hT)).injective
            (Sum.inr.inj (Sum.inr.inj hab)))

/-- Canonical reservation is exactly ownership by one automatic source. -/
theorem planarLensRawPhysicalResource_isCanonicallyReserved_iff_mem_range :
    ∀ raw : PlanarLensRawPhysicalResource (T := T),
      raw.IsCanonicallyReserved axis hn2 hn3 hT ↔
        raw ∈ Set.range
          (fullPrunedAutomaticOwnerResourceEmbedding axis hn2 hn3 hT)
  | .inl port => by
      constructor
      · rintro ⟨owner, rfl⟩
        exact ⟨.exit owner, rfl⟩
      · rintro ⟨owner, howner⟩
        rcases owner with owner | owner | owner
        · exact ⟨owner, Sum.inl.inj howner⟩
        · simp [fullPrunedAutomaticOwnerResourceEmbedding,
            FullPrunedAutomaticOwner.rawResource] at howner
        · simp [fullPrunedAutomaticOwnerResourceEmbedding,
            FullPrunedAutomaticOwner.rawResource] at howner
  | .inr (.inl edge) => by
      constructor
      · rintro ⟨owner, rfl⟩
        exact ⟨.internalToken owner, rfl⟩
      · rintro ⟨owner, howner⟩
        rcases owner with owner | owner | owner
        · simp [fullPrunedAutomaticOwnerResourceEmbedding,
            FullPrunedAutomaticOwner.rawResource] at howner
        · exact ⟨owner, Sum.inl.inj (Sum.inr.inj howner)⟩
        · simp [fullPrunedAutomaticOwnerResourceEmbedding,
            FullPrunedAutomaticOwner.rawResource] at howner
  | .inr (.inr component) => by
      constructor
      · rintro ⟨owner, rfl⟩
        exact ⟨.carrierQuotient owner, rfl⟩
      · rintro ⟨owner, howner⟩
        rcases owner with owner | owner | owner
        · simp [fullPrunedAutomaticOwnerResourceEmbedding,
            FullPrunedAutomaticOwner.rawResource] at howner
        · simp [fullPrunedAutomaticOwnerResourceEmbedding,
            FullPrunedAutomaticOwner.rawResource] at howner
        · exact ⟨owner, Sum.inr.inj (Sum.inr.inj howner)⟩

/-- A raw resource displaces its installed automatic owner.  The relation is
oriented from resources to owners, as required by an alternating search. -/
def FullPrunedResourceDisplaces
    (raw : PlanarLensRawPhysicalResource (T := T))
    (owner : FullPrunedAutomaticOwner axis hn2 hn3 hT) : Prop :=
  owner.rawResource axis hn2 hn3 hT = raw

/-- An automatically reserved raw resource displaces at most one owner. -/
theorem fullPrunedResourceDisplaces_rightUnique :
    Relator.RightUnique (FullPrunedResourceDisplaces axis hn2 hn3 hT) := by
  intro raw owner other howner hother
  exact (fullPrunedAutomaticOwnerResourceEmbedding axis hn2 hn3 hT).injective
    (howner.trans hother.symm)

/-- Total source type for the shared alternating layer.  Automatic quotient
owners are followed by ranked collisions, whose occurrence labels remain only
on this source side. -/
abbrev SharedAlternatingSource :=
  FullPrunedAutomaticOwner axis hn2 hn3 hT ⊕
    FullPrunedOrderedCollision axis hn2 hn3 hT

/-- The alternating layer always uses raw physical resources. -/
abbrev SharedAlternatingRawResource :=
  PlanarLensRawPhysicalResource (T := T)

/-- Lift automatic displacement to the total source type.  Ranked collision
sources are intentionally not assigned an automatic owner. -/
def SharedAlternatingResourceDisplaces
    (raw : SharedAlternatingRawResource (T := T))
    (source : SharedAlternatingSource axis hn2 hn3 hT) : Prop :=
  ∃ owner, source = .inl owner ∧
    FullPrunedResourceDisplaces axis hn2 hn3 hT raw owner

/-- Lifted automatic displacement remains right-unique on the total source
type. -/
theorem sharedAlternatingResourceDisplaces_rightUnique :
    Relator.RightUnique
      (SharedAlternatingResourceDisplaces axis hn2 hn3 hT) := by
  intro raw source other hsource hother
  rcases hsource with ⟨owner, rfl, howner⟩
  rcases hother with ⟨otherOwner, rfl, hotherOwner⟩
  exact congrArg Sum.inl
    (fullPrunedResourceDisplaces_rightUnique axis hn2 hn3 hT
      howner hotherOwner)

/-- Raw resource exposed by a component-split hull observation.  Selected
starts expose their raw component, retained supported sides expose their edge,
and boundary observations expose their port.  Cotree transitions, including
the omitted transition selected at a bounded cell, expose no resource. -/
def CanonicalHullSeparatingObservation.rawResource?
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x}} :
    CanonicalHullSeparatingObservation axis hn2 hn3 hT assignment source →
      Option (PlanarLensRawPhysicalResource (T := T))
  | .selectedStart _ component => some (.inr (.inr component))
  | .boundedCell _ _ (.inl edge) => some (.inr (.inl edge))
  | .boundedCell _ _ (.inr _) => none
  | .cotreeOccurrence _ => none
  | .boundaryPort port => some (.inl port)

/-- Component-split continuation adjacency: a raw resource is adjacent when it
is exposed at the endpoint of an existing certified canonical parent path.
This relation belongs only to the legacy component-split hull.  It is not the
missing occurrence-shared-hull construction and makes no totality claim. -/
def CanonicalHullComponentSplitContinuationAdjacent
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (source : {x : FullPrunedComponentCotreeDualHullCarrier
        axis hn2 hn3 hT assignment //
      FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT) x})
    (raw : PlanarLensRawPhysicalResource (T := T)) : Prop :=
  ∃ terminal,
    Nonempty (CanonicalHullFirstSeparatingContinuationPath
      axis hn2 hn3 hT assignment source terminal) ∧
    (canonicalHullSeparatingObservationAt
      axis hn2 hn3 hT assignment source terminal).rawResource?
        axis hn2 hn3 hT = some raw

/-! ### Outgoing adjacency after automatic displacement -/

/-- A cotree continuation is launched from a terminal token, before splitting
that token into a component representative or a ranked collision.  Keeping this
interface on tokens is important: the token underlying a component reservation
is a representative and therefore is not a `FullPrunedOrderedCollision`. -/
abbrev FullPrunedTerminalCotreeContinuation :=
  FullPrunedTerminalToken axis hn2 hT →
    PlanarLensRawPhysicalResource (T := T) → Prop

/-- Terminal token retained by an automatic owner when one exists.  An exit
retains only its occupied port and supplies no justified cotree launch. -/
noncomputable def FullPrunedAutomaticOwner.continuationToken? :
    FullPrunedAutomaticOwner axis hn2 hn3 hT →
      Option (FullPrunedTerminalToken axis hn2 hT)
  | .exit _ => none
  | .internalToken owner => some owner.1
  | .carrierQuotient owner => some
      (rankedCarrierRepresentative
        (FullPrunedTokenCarrier axis hn2 hn3 hT)
        (fullPrunedTokenRank axis hn2 hn3 hT) owner).1

/-- The token retained by a component owner still splits into its quotient
representative branch.  Relaunching it must not require, or manufacture, a
ranked-collision proof. -/
theorem fullPrunedCarrierQuotient_continuationToken_split
    (owner : CarrierQuotient
      (FullPrunedTokenCarrier axis hn2 hn3 hT)) :
    rankedCarrierQuotientCollisionEquiv
        (FullPrunedTokenCarrier axis hn2 hn3 hT)
        (fullPrunedTokenRank axis hn2 hn3 hT)
        (rankedCarrierRepresentative
          (FullPrunedTokenCarrier axis hn2 hn3 hT)
          (fullPrunedTokenRank axis hn2 hn3 hT) owner) = .inl owner := by
  let split := rankedCarrierQuotientCollisionEquiv
    (FullPrunedTokenCarrier axis hn2 hn3 hT)
    (fullPrunedTokenRank axis hn2 hn3 hT)
  exact split.apply_symm_apply (.inl owner)

/-- All raw resources justified from an installed automatic owner: its
reservation, or a cotree continuation launched from the terminal token it
retains.  In particular, the exit case contains only its occupied port. -/
def FullPrunedAutomaticOwnerReachable
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (owner : FullPrunedAutomaticOwner axis hn2 hn3 hT)
    (raw : PlanarLensRawPhysicalResource (T := T)) : Prop :=
  owner.rawResource axis hn2 hn3 hT = raw ∨
    ∃ token, owner.continuationToken? axis hn2 hn3 hT = some token ∧
      continuation token raw

theorem fullPrunedAutomaticOwnerReachable_exit_iff
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (owner : ↥(planeChannelForest axis hn2 hT).exits)
    (raw : PlanarLensRawPhysicalResource (T := T)) :
    FullPrunedAutomaticOwnerReachable axis hn2 hn3 hT continuation
        (.exit owner) raw ↔
      raw = .inl (exitEmbedding axis hn2 hT owner) := by
  simp [FullPrunedAutomaticOwnerReachable,
    FullPrunedAutomaticOwner.continuationToken?,
    FullPrunedAutomaticOwner.rawResource, eq_comm]

theorem fullPrunedAutomaticOwnerReachable_internalToken_iff
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (owner : InternalTreeEdgeToken
      (supportFinset (gridGraph n n \ T))
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT))
    (raw : PlanarLensRawPhysicalResource (T := T)) :
    FullPrunedAutomaticOwnerReachable axis hn2 hn3 hT continuation
        (.internalToken owner) raw ↔
      raw = .inr (.inl (internalTreeEdgeTokenEmbedding
          (supportFinset (gridGraph n n \ T))
          (terminalTreeEdgeEmbedding axis hn2 hn3 hT) owner)) ∨
        continuation owner.1 raw := by
  unfold FullPrunedAutomaticOwnerReachable
  change
    (Sum.inr (Sum.inl (internalTreeEdgeTokenEmbedding
        (supportFinset (gridGraph n n \ T))
        (terminalTreeEdgeEmbedding axis hn2 hn3 hT) owner)) = raw ∨
      ∃ token, some owner.1 = some token ∧ continuation token raw) ↔ _
  constructor
  · rintro (hraw | ⟨token, htoken, hcontinue⟩)
    · exact Or.inl hraw.symm
    · have h := Option.some.inj htoken
      subst token
      exact Or.inr hcontinue
  · rintro (hraw | hcontinue)
    · exact Or.inl hraw.symm
    · exact Or.inr ⟨owner.1, rfl, hcontinue⟩

theorem fullPrunedAutomaticOwnerReachable_carrierQuotient_iff
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (owner : CarrierQuotient
      (FullPrunedTokenCarrier axis hn2 hn3 hT))
    (raw : PlanarLensRawPhysicalResource (T := T)) :
    FullPrunedAutomaticOwnerReachable axis hn2 hn3 hT continuation
        (.carrierQuotient owner) raw ↔
      raw = .inr (.inr (carrierQuotientEmbedding
          (FullPrunedTokenCarrier axis hn2 hn3 hT) owner)) ∨
        continuation
          (rankedCarrierRepresentative
            (FullPrunedTokenCarrier axis hn2 hn3 hT)
            (fullPrunedTokenRank axis hn2 hn3 hT) owner).1 raw := by
  unfold FullPrunedAutomaticOwnerReachable
  let token := (rankedCarrierRepresentative
    (FullPrunedTokenCarrier axis hn2 hn3 hT)
    (fullPrunedTokenRank axis hn2 hn3 hT) owner).1
  change
    (Sum.inr (Sum.inr (carrierQuotientEmbedding
        (FullPrunedTokenCarrier axis hn2 hn3 hT) owner)) = raw ∨
      ∃ other, some token = some other ∧ continuation other raw) ↔ _
  constructor
  · rintro (hraw | ⟨other, htoken, hcontinue⟩)
    · exact Or.inl hraw.symm
    · have h := Option.some.inj htoken
      subst other
      exact Or.inr hcontinue
  · rintro (hraw | hcontinue)
    · exact Or.inl hraw.symm
    · exact Or.inr ⟨token, rfl, hcontinue⟩

/-- Outgoing adjacency of a displaced automatic owner.  Returning immediately
to the occupied reservation is removed; every remaining edge is an actual
terminal-token cotree continuation. -/
def FullPrunedDisplacedOwnerOutgoingAdjacent
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (owner : FullPrunedAutomaticOwner axis hn2 hn3 hT)
    (raw : PlanarLensRawPhysicalResource (T := T)) : Prop :=
  FullPrunedAutomaticOwnerReachable axis hn2 hn3 hT continuation owner raw ∧
    raw ≠ owner.rawResource axis hn2 hn3 hT

theorem fullPrunedDisplacedOwnerOutgoingAdjacent_exit
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (owner : ↥(planeChannelForest axis hn2 hT).exits)
    (raw : PlanarLensRawPhysicalResource (T := T)) :
    ¬FullPrunedDisplacedOwnerOutgoingAdjacent axis hn2 hn3 hT continuation
      (.exit owner) raw := by
  rw [FullPrunedDisplacedOwnerOutgoingAdjacent,
    fullPrunedAutomaticOwnerReachable_exit_iff]
  simp [FullPrunedAutomaticOwner.rawResource]

theorem fullPrunedDisplacedOwnerOutgoingAdjacent_internalToken_iff
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (owner : InternalTreeEdgeToken
      (supportFinset (gridGraph n n \ T))
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT))
    (raw : PlanarLensRawPhysicalResource (T := T)) :
    FullPrunedDisplacedOwnerOutgoingAdjacent axis hn2 hn3 hT continuation
        (.internalToken owner) raw ↔
      continuation owner.1 raw ∧
        raw ≠ .inr (.inl (internalTreeEdgeTokenEmbedding
          (supportFinset (gridGraph n n \ T))
          (terminalTreeEdgeEmbedding axis hn2 hn3 hT) owner)) := by
  rw [FullPrunedDisplacedOwnerOutgoingAdjacent,
    fullPrunedAutomaticOwnerReachable_internalToken_iff]
  constructor
  · rintro ⟨hraw | hcontinue, hne⟩
    · exact (hne hraw).elim
    · exact ⟨hcontinue, hne⟩
  · rintro ⟨hcontinue, hne⟩
    exact ⟨Or.inr hcontinue, hne⟩

theorem fullPrunedDisplacedOwnerOutgoingAdjacent_carrierQuotient_iff
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT)
    (owner : CarrierQuotient
      (FullPrunedTokenCarrier axis hn2 hn3 hT))
    (raw : PlanarLensRawPhysicalResource (T := T)) :
    FullPrunedDisplacedOwnerOutgoingAdjacent axis hn2 hn3 hT continuation
        (.carrierQuotient owner) raw ↔
      continuation
          (rankedCarrierRepresentative
            (FullPrunedTokenCarrier axis hn2 hn3 hT)
            (fullPrunedTokenRank axis hn2 hn3 hT) owner).1 raw ∧
        raw ≠ .inr (.inr (carrierQuotientEmbedding
          (FullPrunedTokenCarrier axis hn2 hn3 hT) owner)) := by
  rw [FullPrunedDisplacedOwnerOutgoingAdjacent,
    fullPrunedAutomaticOwnerReachable_carrierQuotient_iff]
  constructor
  · rintro ⟨hraw | hcontinue, hne⟩
    · exact (hne hraw).elim
    · exact ⟨hcontinue, hne⟩
  · rintro ⟨hcontinue, hne⟩
    exact ⟨Or.inr hcontinue, hne⟩

/-- Internal automatic owners are absent in this canonical specialization:
every first-stop terminal token was already proved noninternal. -/
theorem fullPrunedInternalTreeEdgeToken_isEmpty :
    IsEmpty (InternalTreeEdgeToken
      (supportFinset (gridGraph n n \ T))
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT)) :=
  ⟨fun owner =>
    (terminalTreeEdgeEmbedding_isNoninternal axis hn2 hn3 hT owner.1) owner.2⟩

/-- Exact blocker to total outgoing adjacency.  Exits can never leave their
occupied port with the present data; internal and component owners are total
exactly when their retained token has a continuation to a different raw
resource.  No such continuation existence is assumed here. -/
theorem fullPrunedDisplacedOwnerOutgoingAdjacent_leftTotal_iff
    (continuation : FullPrunedTerminalCotreeContinuation axis hn2 hT) :
    Relator.LeftTotal
        (FullPrunedDisplacedOwnerOutgoingAdjacent
          axis hn2 hn3 hT continuation) ↔
      IsEmpty ↥(planeChannelForest axis hn2 hT).exits ∧
      (∀ owner : InternalTreeEdgeToken
          (supportFinset (gridGraph n n \ T))
          (terminalTreeEdgeEmbedding axis hn2 hn3 hT),
        ∃ raw, continuation owner.1 raw ∧
          raw ≠ .inr (.inl (internalTreeEdgeTokenEmbedding
            (supportFinset (gridGraph n n \ T))
            (terminalTreeEdgeEmbedding axis hn2 hn3 hT) owner))) ∧
      (∀ owner : CarrierQuotient
          (FullPrunedTokenCarrier axis hn2 hn3 hT),
        ∃ raw, continuation
            (rankedCarrierRepresentative
              (FullPrunedTokenCarrier axis hn2 hn3 hT)
              (fullPrunedTokenRank axis hn2 hn3 hT) owner).1 raw ∧
          raw ≠ .inr (.inr (carrierQuotientEmbedding
            (FullPrunedTokenCarrier axis hn2 hn3 hT) owner))) := by
  constructor
  · intro htotal
    refine ⟨⟨fun exit => ?_⟩, ?_, ?_⟩
    · obtain ⟨raw, hraw⟩ := htotal (.exit exit)
      exact (fullPrunedDisplacedOwnerOutgoingAdjacent_exit
        axis hn2 hn3 hT continuation exit raw) hraw
    · intro owner
      obtain ⟨raw, hraw⟩ := htotal (.internalToken owner)
      exact ⟨raw,
        (fullPrunedDisplacedOwnerOutgoingAdjacent_internalToken_iff
          axis hn2 hn3 hT continuation owner raw).mp hraw⟩
    · intro owner
      obtain ⟨raw, hraw⟩ := htotal (.carrierQuotient owner)
      exact ⟨raw,
        (fullPrunedDisplacedOwnerOutgoingAdjacent_carrierQuotient_iff
          axis hn2 hn3 hT continuation owner raw).mp hraw⟩
  · rintro ⟨hexit, hinternal, hcomponent⟩ owner
    rcases owner with owner | owner | owner
    · exact isEmptyElim owner
    · obtain ⟨raw, hraw⟩ := hinternal owner
      exact ⟨raw,
        (fullPrunedDisplacedOwnerOutgoingAdjacent_internalToken_iff
          axis hn2 hn3 hT continuation owner raw).mpr hraw⟩
    · obtain ⟨raw, hraw⟩ := hcomponent owner
      exact ⟨raw,
        (fullPrunedDisplacedOwnerOutgoingAdjacent_carrierQuotient_iff
          axis hn2 hn3 hT continuation owner raw).mpr hraw⟩

/-! #### One-copy shared-hull continuation adjacency -/

/-- Each branch-excess slot of the actual shared hull is anchored at a distinct
immediate child occurrence.  All shared faces and continuation occurrences
remain in the original carrier; no component-indexed copy is introduced. -/
noncomputable def fullPrunedSharedCotreeDualHullMergerSlotChildEmbedding
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :
    (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot ↪
      FullPrunedSharedCotreeDualHullCarrier axis hn2 hn3 hT assignment := by
  let F := fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment
  let selected := F.mergerSlotPhysicalChildEmbedding (fun _ => True) (by
    intro vertex
    simp [ParentForest.nonphysicalChildren])
  exact {
    toFun := fun slot => (selected slot).1
    inj' := by
      intro slot other h
      apply selected.injective
      exact Subtype.ext h }

/-- The occurrence selected for a shared merger slot is an actual immediate
child of that slot's branch vertex. -/
theorem fullPrunedSharedCotreeDualHullMergerSlotChild_parent
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    (fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment).parent
        (fullPrunedSharedCotreeDualHullMergerSlotChildEmbedding
          axis hn2 hn3 hT assignment slot) = some slot.1 := by
  classical
  let F := fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment
  let hghost : ∀ vertex, (F.nonphysicalChildren (fun _ => True) vertex).card ≤ 1 := by
    intro vertex
    simp [ParentForest.nonphysicalChildren]
  change F.parent
    ((F.localMergerSlotPhysicalChildEmbedding
      (fun _ => True) hghost slot.1 slot.2).1) = some slot.1
  have hchild := (Finset.mem_filter.mp
    (F.localMergerSlotPhysicalChildEmbedding
      (fun _ => True) hghost slot.1 slot.2).2).1
  exact (Finset.mem_filter.mp hchild).2

/-- Constructor-exact observation of a vertex in the one-copy shared hull.
Continuation occurrences retain their occurrence identity, rather than only
their coordinate edge label. -/
inductive FullPrunedSharedCotreeDualHullObservation
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) where
  | selectedStart (collision : FullPrunedInwardCollision axis hn2 hn3 hT)
  | cotreeOccurrence
      (occurrence : FullPrunedSharedCotreeDualEdgeOccurrence
        axis hn2 hn3 hT assignment)
  | boundedCell (row col : Fin (n - 1))
      (raw : GridCellSupportedSideRawResource T)
  | boundary
      (occurrence : BoundaryTransitionOccurrence
        (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment))

/-- Read the exact shared-carrier constructor at an active hull vertex. -/
noncomputable def fullPrunedSharedCotreeDualHullObservationAt
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (vertex : FullPrunedSharedCotreeDualHullCarrier
      axis hn2 hn3 hT assignment) :
    FullPrunedSharedCotreeDualHullObservation axis hn2 hn3 hT assignment := by
  rcases vertex.1 with collision | core
  · exact .selectedStart collision
  · rcases core with occurrence | face
    · exact .cotreeOccurrence occurrence
    · rcases face with bounded | boundary
      · rcases bounded with ⟨face, hout⟩
        cases face with
        | out => exact False.elim (hout rfl)
        | cell row col =>
            exact .boundedCell row col
              (gridTreeCellSupportedSideRawResource T hT row col)
      · exact .boundary boundary

/-- Raw physical resource exposed by an exact shared-hull observation.  An
omitted supported side and an occurrence vertex are continuations, not copied
component resources. -/
def FullPrunedSharedCotreeDualHullObservation.rawResource?
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root} :
    FullPrunedSharedCotreeDualHullObservation axis hn2 hn3 hT assignment →
      Option (PlanarLensRawPhysicalResource (T := T))
  | .selectedStart collision => some (.inr (.inr (assignment.component collision)))
  | .cotreeOccurrence _ => none
  | .boundedCell _ _ (.inl edge) => some (.inr (.inl edge))
  | .boundedCell _ _ (.inr _) => none
  | .boundary occurrence => some (.inl
      (BoundaryTransitionOccurrence.outerPort
        (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
        hn2 hn2 occurrence))

/-- Certified occurrence-preserving adjacency from an actual shared-hull
merger slot to a raw resource encountered above its selected child occurrence.
The endpoint remains a vertex of the one-copy carrier and `reached` certifies
the complete parent-chain connection. -/
structure FullPrunedSharedCotreeDualHullContinuationAdjacencyWitness
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot)
    (raw : PlanarLensRawPhysicalResource (T := T)) where
  terminal : FullPrunedSharedCotreeDualHullCarrier axis hn2 hn3 hT assignment
  reached : Relation.ReflTransGen
    (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).ParentStep
    (fullPrunedSharedCotreeDualHullMergerSlotChildEmbedding
      axis hn2 hn3 hT assignment slot) terminal
  exposes : (fullPrunedSharedCotreeDualHullObservationAt
    axis hn2 hn3 hT assignment terminal).rawResource?
      axis hn2 hn3 hT = some raw

/-- The shared-hull continuation adjacency relation.  It records existence of
certified path data and asserts neither freshness nor a simultaneous choice. -/
def FullPrunedSharedCotreeDualHullContinuationAdjacent
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot)
    (raw : PlanarLensRawPhysicalResource (T := T)) : Prop :=
  Nonempty (FullPrunedSharedCotreeDualHullContinuationAdjacencyWitness
    axis hn2 hn3 hT assignment slot raw)

/-- Every actual shared-hull merger occurrence has at least one adjacent raw
resource.  Following its selected child to a hull root always exposes that
root's unique actual boundary occurrence and hence its physical outer port. -/
theorem fullPrunedSharedCotreeDualHullContinuationAdjacent_nonempty
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    ∃ raw : PlanarLensRawPhysicalResource (T := T),
      FullPrunedSharedCotreeDualHullContinuationAdjacent
        axis hn2 hn3 hT assignment slot raw := by
  let F := fullPrunedSharedCotreeDualHullForest axis hn2 hn3 hT assignment
  let child := fullPrunedSharedCotreeDualHullMergerSlotChildEmbedding
    axis hn2 hn3 hT assignment slot
  let above := F.rootAbove child
  let activeRoot : ↥F.roots := ⟨above.1, above.2.2⟩
  let ambientRoot := fullPrunedSharedCotreeDualHullRootEmbedding
    axis hn2 hn3 hT assignment activeRoot
  let boundary := fullPrunedSharedCotreeDualRootBoundary
    axis hn2 hn3 hT assignment ambientRoot
  let port := BoundaryTransitionOccurrence.outerPort
    (fullPrunedSharedCotreeDualEdgeTransition axis hn2 hn3 hT assignment)
    hn2 hn2 boundary
  refine ⟨.inl port, ⟨{
    terminal := activeRoot.1
    reached := above.2.1
    exposes := ?_ }⟩⟩
  have hcarrier : activeRoot.1.1 = .inr (.inr (.inr boundary)) := by
    exact fullPrunedSharedCotreeDualRootBoundary_spec
      axis hn2 hn3 hT assignment ambientRoot
  let boundaryVertex : FullPrunedSharedCotreeDualHullCarrier
      axis hn2 hn3 hT assignment :=
    ⟨.inr (.inr (.inr boundary)), by
      rw [← hcarrier]
      exact activeRoot.1.2⟩
  have hvertex : activeRoot.1 = boundaryVertex := Subtype.ext hcarrier
  rw [hvertex]
  rfl

end

end CanonicalExpandedContourForest

end GridGraphs
