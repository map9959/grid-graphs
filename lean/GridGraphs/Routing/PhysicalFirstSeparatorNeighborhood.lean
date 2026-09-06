import GridGraphs.Routing.CanonicalReconvergenceLens

/-!
# Physical first-separator neighborhoods

This module makes the local source of a cotree-hull merger slot explicit.  A
slot is represented by its actual immediate child sector, not merely by a
cardinality index.  The sector carries its exact descendant start group and the
set of raw component labels occurring in that group.

Candidate neighborhoods contain only residual physical resources: an
unreserved split port, an unreserved retained internal edge, or a free raw
component.  Occurrence labels are retained on the source side and never enter
the resource type.  Equality of selected resources is reduced to the exact
same-component nested exception already isolated by the canonical hull
geometry.
-/

namespace GridGraphs

open Finset

namespace ParentForest

variable {V Start Component : Type*} [Fintype V] [DecidableEq V]
  [Fintype Start] [DecidableEq Start] [DecidableEq Component]

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- One exact immediate child sector at a parent vertex. -/
abbrev ChildSector (F : ParentForest V) (parent : V) :=
  ↥(F.children parent)

/-- The selected child sector represented by a merger-excess slot.  The
membership proof records the actual parent/child incidence. -/
noncomputable def mergerSlotChildSector
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    (slot : F.MergerSlot) : F.ChildSector slot.1 := by
  let child := F.localMergerSlotPhysicalChildEmbedding
    physical hghost slot.1 slot.2
  exact ⟨child.1, (Finset.mem_filter.mp child.2).1⟩

@[simp] theorem mergerSlotChildSector_val
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    (slot : F.MergerSlot) :
    (F.mergerSlotChildSector physical hghost slot).1 =
      (F.mergerSlotPhysicalChildEmbedding physical hghost slot).1 := by
  rfl

/-- Different global merger slots select different physical child sectors.
This is stronger than local `Fin`-index injectivity: parent uniqueness rules
out reuse at another merger. -/
theorem mergerSlotChildSector_val_injective
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1) :
    Function.Injective
      (fun slot : F.MergerSlot =>
        (F.mergerSlotChildSector physical hghost slot).1) := by
  intro a b hab
  apply (F.mergerSlotPhysicalChildEmbedding physical hghost).injective
  apply Subtype.ext
  simpa using hab

/-- Selected starts whose parent chain enters one exact child sector. -/
def descendantStartGroup
    (F : ParentForest V) (start : Start ↪ ↥F.leaves)
    {parent : V} (sector : F.ChildSector parent) : Finset Start :=
  Finset.univ.filter fun source =>
    Relation.ReflTransGen F.ParentStep (start source).1 sector.1

omit [DecidableEq Start] in
theorem mem_descendantStartGroup_iff
    (F : ParentForest V) (start : Start ↪ ↥F.leaves)
    {parent : V} (sector : F.ChildSector parent) (source : Start) :
    source ∈ F.descendantStartGroup start sector ↔
      Relation.ReflTransGen F.ParentStep (start source).1 sector.1 := by
  simp [descendantStartGroup]

/-- Exact raw component labels represented among a sector's descendant start
group.  This is an image set, so repeated occurrences of one component consume
one label rather than manufacturing component capacity. -/
def descendantComponentLabels
    (F : ParentForest V) (start : Start ↪ ↥F.leaves)
    (component : Start → Component) {parent : V}
    (sector : F.ChildSector parent) : Finset Component :=
  (F.descendantStartGroup start sector).image component

omit [DecidableEq Start] in
theorem mem_descendantComponentLabels_iff
    (F : ParentForest V) (start : Start ↪ ↥F.leaves)
    (component : Start → Component) {parent : V}
    (sector : F.ChildSector parent) (label : Component) :
    label ∈ F.descendantComponentLabels start component sector ↔
      ∃ source, source ∈ F.descendantStartGroup start sector ∧
        component source = label := by
  simp [descendantComponentLabels]

/-- Two merger-slot child sectors are nested when the inner sector reaches the
outer sector along the parent chain.  The slots remain distinct occurrences;
equality of a later physical stop does not identify them. -/
structure NestedMergerSlotChildSectors (F : ParentForest V) where
  inner : F.MergerSlot
  outer : F.MergerSlot
  innerSector : F.ChildSector inner.1
  outerSector : F.ChildSector outer.1
  distinct : inner ≠ outer
  nested : Relation.ReflTransGen F.ParentStep innerSector.1 outerSector.1

/-- The outer branch vertex is an intervening branch-excess obligation exposed
by two nested child sectors.  Thus a repeated stop on the inner walk cannot be
treated as a second copy of one component resource: the downstream ledger must
also retain the outer merger occurrence (or a root debt above it). -/
theorem NestedMergerSlotChildSectors.reaches_outer_obligation
    (F : ParentForest V) (pair : NestedMergerSlotChildSectors F) :
    Relation.ReflTransGen F.ParentStep pair.innerSector.1 pair.outer.1 := by
  have hstep : F.ParentStep pair.outerSector.1 pair.outer.1 := by
    have hmem := pair.outerSector.2
    change pair.outerSector.1 ∈
      (Finset.univ.filter fun child => F.parent child = some pair.outer.1) at hmem
    exact (Finset.mem_filter.mp hmem).2
  exact Relation.ReflTransGen.tail pair.nested hstep

/-- Every start in the inner nested sector belongs to the descendant group of
the exposed outer branch obligation. -/
theorem NestedMergerSlotChildSectors.descendantStartGroup_subset_outer
    (F : ParentForest V) (start : Start ↪ ↥F.leaves)
    (pair : NestedMergerSlotChildSectors F) :
    F.descendantStartGroup start pair.innerSector ⊆
      F.descendantStartGroup start pair.outerSector := by
  intro source hsource
  rw [F.mem_descendantStartGroup_iff] at hsource
  rw [F.mem_descendantStartGroup_iff]
  exact hsource.trans pair.nested

end

end ParentForest

namespace CanonicalExpandedContourForest

open ParentForest

variable {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
  {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
  (hT : IsSpanningSubtree (gridGraph n n) T)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The exact immediate child sector assigned to a merger slot in the global
shared component-cotree hull. -/
noncomputable def canonicalHullMergerSlotSector
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :=
  (fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment)
    |>.mergerSlotChildSector
      (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
        (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
      (fullPrunedComponentCotreeDualHull_nonphysicalChildren_card_le_one
        axis hn2 hn3 hT assignment) slot

/-- Descendant inward-collision starts in the selected exact child sector. -/
noncomputable def canonicalHullMergerSlotDescendantStartGroup
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    Finset (FullPrunedInwardCollision axis hn2 hn3 hT) :=
  let F := fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment
  F.descendantStartGroup
    (fullPrunedComponentCotreeDualHullLeafEquiv
      axis hn2 hn3 hT assignment).toEmbedding
    (canonicalHullMergerSlotSector axis hn2 hn3 hT assignment slot)

/-- Raw component labels of the exact descendant start group.  Labels are
physical component identities, not contact or occurrence labels. -/
noncomputable def canonicalHullMergerSlotDescendantComponentLabels
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    Finset (ContactRawComponent (T := T)) :=
  let F := fullPrunedComponentCotreeDualHullForest axis hn2 hn3 hT assignment
  F.descendantComponentLabels
    (fullPrunedComponentCotreeDualHullLeafEquiv
      axis hn2 hn3 hT assignment).toEmbedding
    assignment.component
    (canonicalHullMergerSlotSector axis hn2 hn3 hT assignment slot)

/-! #### Global shared-hull multiplicity -/

/-- Multiplicity obligations are exactly active merger slots of the global
shared hull, refined per represented descendant component.  Root debt is absent
because the active root-port map is injective. -/
abbrev SharedHullMultiplicityObligation
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root) :=
  FullPrunedSharedCotreeDualHullMergerComponentObligation
    axis hn2 hn3 hT assignment

/-- Exact descendant provenance in the selected component fiber. -/
noncomputable def sharedHullMultiplicityDescendantGroup
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (obligation : SharedHullMultiplicityObligation
      axis hn2 hn3 hT assignment) :
    Finset (FullPrunedInwardCollision axis hn2 hn3 hT) :=
  (fullPrunedSharedCotreeDualHullDescendantSources
    axis hn2 hn3 hT assignment obligation.1.1).filter fun source =>
      assignment.component source = obligation.2.1

/-- Multiplicity Hall for equal-component stops in the shared hull.  For every
finite fiber of `k` obligations with one raw stop component, the union of their
downstream physical neighborhoods contains at least `k` resources.  This is the
capacity statement needed for repeated nested stops; pointwise equality of the
first stop is intentionally allowed. -/
def SharedHullMultiplicityHall
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    {R : Type*} [DecidableEq R]
    (downstreamNeighborhood : SharedHullMultiplicityObligation
      axis hn2 hn3 hT assignment → Finset R) : Prop :=
  ∀ raw (S : Finset (SharedHullMultiplicityObligation
      axis hn2 hn3 hT assignment)),
    (∀ obligation ∈ S,
      fullPrunedSharedCotreeDualHullMergerObligationComponent
        axis hn2 hn3 hT obligation = raw) →
      S.card ≤ (S.biUnion downstreamNeighborhood).card

/-- The advertised `k`-stop form of multiplicity Hall. -/
theorem sharedHullMultiplicityHall_k_resources
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    {R : Type*} [DecidableEq R]
    (downstreamNeighborhood : SharedHullMultiplicityObligation
      axis hn2 hn3 hT assignment → Finset R)
    (hHall : SharedHullMultiplicityHall axis hn2 hn3 hT assignment
      downstreamNeighborhood)
    (raw : ContactRawComponent (T := T))
    (S : Finset (SharedHullMultiplicityObligation
      axis hn2 hn3 hT assignment))
    (k : Nat) (hcard : S.card = k)
    (hsame : ∀ obligation ∈ S,
      fullPrunedSharedCotreeDualHullMergerObligationComponent
        axis hn2 hn3 hT obligation = raw) :
    k ≤ (S.biUnion downstreamNeighborhood).card := by
  rw [← hcard]
  exact hHall raw S hsame

/-- Exact fiber Hall, not pointwise first-stop injectivity, is sufficient and
necessary once every downstream resource selected for an obligation preserves
its stop component. Resources outside merger neighborhoods may remain
unclassified. -/
theorem sharedHullMultiplicityHall_iff_localizedHall
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    {R : Type*} [DecidableEq R]
    (resourceComponent : R → Option (ContactRawComponent (T := T)))
    (downstreamNeighborhood : SharedHullMultiplicityObligation
      axis hn2 hn3 hT assignment → Finset R)
    (hpreserve : ∀ obligation {resource},
      resource ∈ downstreamNeighborhood obligation →
        resourceComponent resource = some
          (fullPrunedSharedCotreeDualHullMergerObligationComponent
            axis hn2 hn3 hT obligation)) :
    SharedHullMultiplicityHall axis hn2 hn3 hT assignment
        downstreamNeighborhood ↔
      LocalizedHall downstreamNeighborhood := by
  constructor
  · intro hfiber
    apply localizedHall_of_fiberwise_of_neighborhood_disjoint
      (fullPrunedSharedCotreeDualHullMergerObligationComponent
        axis hn2 hn3 hT)
        downstreamNeighborhood hfiber
    intro a b hab
    rw [Finset.disjoint_left]
    intro resource ha hb
    apply hab
    exact Option.some.inj ((hpreserve a ha).symm.trans (hpreserve b hb))
  · intro hHall raw S _hsame
    exact hHall S

/-- Consequently the fiber inequalities are exactly what is needed to choose
distinct downstream resources for all shared branch/root-debt obligations. -/
theorem sharedHullMultiplicityHall_iff_exists_routing
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    {R : Type*} [DecidableEq R]
    (resourceComponent : R → Option (ContactRawComponent (T := T)))
    (downstreamNeighborhood : SharedHullMultiplicityObligation
      axis hn2 hn3 hT assignment → Finset R)
    (hpreserve : ∀ obligation {resource},
      resource ∈ downstreamNeighborhood obligation →
        resourceComponent resource = some
          (fullPrunedSharedCotreeDualHullMergerObligationComponent
            axis hn2 hn3 hT obligation)) :
    SharedHullMultiplicityHall axis hn2 hn3 hT assignment
        downstreamNeighborhood ↔
      Nonempty (LocalizedRouting downstreamNeighborhood) := by
  rw [sharedHullMultiplicityHall_iff_localizedHall axis hn2 hn3 hT assignment
    resourceComponent downstreamNeighborhood hpreserve,
    localizedHall_iff_nonempty_routing]

/-- The explicit downstream multiplicity inequality is sufficient for the
merger-slot/component branch of active grouped residual Hall.  No global target
cardinality or pointwise injectivity assumption is used. -/
theorem sharedCanonicalGroupedResidualHall_mergerBranch
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment)
    (resourceComponent : BoundaryGapResidualPhysicalResource axis hn2 hn3 hT →
      Option (ContactRawComponent (T := T)))
    (hmultiplicity : SharedHullMultiplicityHall axis hn2 hn3 hT assignment
      (sharedCanonicalMergerComponentNeighborhood
        axis hn2 hn3 hT neighborhoods resourceComponent)) :
    LocalizedHall (sharedCanonicalMergerComponentNeighborhood
      axis hn2 hn3 hT neighborhoods resourceComponent) := by
  exact (sharedHullMultiplicityHall_iff_localizedHall
    axis hn2 hn3 hT assignment resourceComponent _
      (sharedCanonicalMergerComponentNeighborhood_component
        axis hn2 hn3 hT neighborhoods resourceComponent)).mp hmultiplicity

/-- Exact descendant Euler accounting can discharge the remaining geometric
gate only after it is related to the cardinality of the actual downstream
physical union.  This theorem records that precise, and unavoidable, bridge. -/
theorem sharedHullMultiplicityHall_of_descendantEuler_capacity
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    {R : Type*} [DecidableEq R]
    (downstreamNeighborhood : SharedHullMultiplicityObligation
      axis hn2 hn3 hT assignment → Finset R)
    (hEulerCapacity : ∀ raw
      (S : Finset (SharedHullMultiplicityObligation
        axis hn2 hn3 hT assignment)),
      (∀ obligation ∈ S,
        fullPrunedSharedCotreeDualHullMergerObligationComponent
          axis hn2 hn3 hT obligation = raw) →
      S.card ≤ (S.biUnion downstreamNeighborhood).card) :
    SharedHullMultiplicityHall axis hn2 hn3 hT assignment
      downstreamNeighborhood :=
  hEulerCapacity

/-! #### Active shared Hall composition -/

/-- The smallest remaining geometric package for the active shared grouped
Hall proof. Each actual source class has a localized physical routing, and the
three selected images are pairwise separated. Unused alternatives may overlap;
requiring whole-neighborhood disjointness would be stronger than Hall needs. -/
structure SharedCanonicalGroupedResidualGeometry
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment) where
  reservedProvenanceRouting : LocalizedRouting
    (fun port => (neighborhoods.reservedUsedPort port).resources)
  mergerRouting : LocalizedRouting
    (fun slot => (neighborhoods.mergerSlot slot).resources)
  outerRouting : LocalizedRouting
    (fun collision => (neighborhoods.outerCollision collision).resources)
  reserved_merger_ne : ∀ port slot,
    reservedProvenanceRouting port ≠ mergerRouting slot
  reserved_outer_ne : ∀ port collision,
    reservedProvenanceRouting port ≠ outerRouting collision
  merger_outer_ne : ∀ slot collision,
    mergerRouting slot ≠ outerRouting collision

/-- Automatic unreserved ports are excluded from the residual source type.
The three classwise routings and selected-image separation compose to active
shared Hall. -/
theorem sharedCanonicalGroupedResidualHall_of_geometry
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment)
    (geometry : SharedCanonicalGroupedResidualGeometry
      axis hn2 hn3 hT assignment neighborhoods) :
    SharedCanonicalGroupedResidualHall axis hn2 hn3 hT neighborhoods := by
  let tail := geometry.mergerRouting.sumOfSelectedNe geometry.outerRouting
    geometry.merger_outer_ne
  let routing := geometry.reservedProvenanceRouting.sumOfSelectedNe tail (by
    intro port source
    rcases source with slot | collision
    · exact geometry.reserved_merger_ne port slot
    · exact geometry.reserved_outer_ne port collision)
  apply (sharedCanonicalGroupedResidualHall_iff_nonempty_routing
    axis hn2 hn3 hT neighborhoods).mpr
  exact ⟨
    { toEmbedding := routing.toEmbedding
      mem_neighborhood := by
        intro source
        rcases source with port | slot | collision
        · exact routing.mem_neighborhood (.inl port)
        · exact routing.mem_neighborhood (.inr (.inl slot))
        · exact routing.mem_neighborhood (.inr (.inr collision)) }⟩

/-- Complete theorem chain from the exact remaining geometric predicate to the
active residual collision bound. -/
theorem sharedCanonicalGroupedResidualGeometry_residualBound
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (neighborhoods : SharedCanonicalGroupedPhysicalNeighborhoods
      axis hn2 hn3 hT assignment)
    (geometry : SharedCanonicalGroupedResidualGeometry
      axis hn2 hn3 hT assignment neighborhoods) :
    Fintype.card (FullPrunedInwardCollision axis hn2 hn3 hT) +
        Fintype.card (FullPrunedOuterCollision axis hn2 hn3 hT) ≤
      Fintype.card (UnreservedCanonicalBoundaryPort axis hn2 hT) +
        Fintype.card (BoundaryGapResidualInternalResource axis hn2 hn3 hT) +
          Fintype.card (BoundaryGapResidualComponentResource axis hn2 hn3 hT) :=
  sharedCanonicalGroupedResidualHall_residualBound axis hn2 hn3 hT neighborhoods
    (sharedCanonicalGroupedResidualHall_of_geometry
      axis hn2 hn3 hT assignment neighborhoods geometry)

/-- A physical first-separator neighborhood for one merger slot.  The complete
canonical walk starts in the slot's exact child sector.  A successful stop is a
singleton containing its real residual resource; a reserved terminal supplies
no candidate. -/
noncomputable def canonicalHullPhysicalFirstSeparatorNeighborhood
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot) :
    Finset (BoundaryGapResidualPhysicalResource axis hn2 hn3 hT) :=
  canonicalActiveBranchNeighborhood axis hn2 hn3 hT assignment
    (canonicalHullFirstSeparatingClassification axis hn2 hn3 hT assignment) slot

/-- Local correctness: membership means equality to the actual first residual
resource returned by the parent-chain walk.  Reserved endpoints have an empty
neighborhood. -/
theorem mem_canonicalHullPhysicalFirstSeparatorNeighborhood_iff
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot)
    (resource : BoundaryGapResidualPhysicalResource axis hn2 hn3 hT) :
    resource ∈ canonicalHullPhysicalFirstSeparatorNeighborhood
        axis hn2 hn3 hT assignment slot ↔
      ∃ candidate : CanonicalHullFirstSeparatingCandidate axis hn2 hn3 hT,
        canonicalHullFirstSeparatingClassification axis hn2 hn3 hT assignment
            ((fullPrunedComponentCotreeDualHullForest
              axis hn2 hn3 hT assignment).mergerSlotPhysicalChildEmbedding
                (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
                  (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
                (fullPrunedComponentCotreeDualHull_nonphysicalChildren_card_le_one
                  axis hn2 hn3 hT assignment) slot) = .residual candidate ∧
          resource = canonicalHullFirstSeparatingCandidateEquiv
            axis hn2 hn3 hT candidate := by
  simp only [canonicalHullPhysicalFirstSeparatorNeighborhood,
    canonicalActiveBranchNeighborhood]
  split
  · rename_i candidate heq
    simp only [Finset.mem_singleton]
    constructor
    · intro hresource
      exact ⟨candidate, heq, hresource⟩
    · rintro ⟨other, hother, hresource⟩
      rw [heq] at hother
      cases hother
      exact hresource
  · rename_i remaining heq
    simp only [Finset.notMem_empty, false_iff]
    rintro ⟨candidate, hcandidate, _⟩
    rw [heq] at hcandidate
    cases hcandidate

/-- Neighborhood candidates are genuine physical resources.  Component
candidates forget directly to one raw free component; there is no constructor
for an occurrence label. -/
theorem canonicalHullPhysicalFirstSeparatorNeighborhood_component
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (slot : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot)
    (component : BoundaryGapResidualComponentResource axis hn2 hn3 hT)
    (hmem : (Sum.inr (Sum.inr component) :
      BoundaryGapResidualPhysicalResource axis hn2 hn3 hT) ∈
        canonicalHullPhysicalFirstSeparatorNeighborhood
          axis hn2 hn3 hT assignment slot) :
    canonicalHullFirstSeparatingClassification axis hn2 hn3 hT assignment
        ((fullPrunedComponentCotreeDualHullForest
          axis hn2 hn3 hT assignment).mergerSlotPhysicalChildEmbedding
            (FullPrunedComponentCotreeDualHullCarrier.IsPhysical
              (axis := axis) (hn2 := hn2) (hn3 := hn3) (hT := hT))
            (fullPrunedComponentCotreeDualHull_nonphysicalChildren_card_le_one
              axis hn2 hn3 hT assignment) slot) =
      .residual (.inr (.inr component)) := by
  obtain ⟨candidate, hresult, hresource⟩ :=
    (mem_canonicalHullPhysicalFirstSeparatorNeighborhood_iff
      axis hn2 hn3 hT assignment slot _).mp hmem
  have hc : candidate = .inr (.inr component) := by
    apply (canonicalHullFirstSeparatingCandidateEquiv axis hn2 hn3 hT).injective
    exact hresource.symm
  simpa [hc] using hresult

/-- Collision theorem for physical neighborhoods.  Under the established
port, internal-edge, component-label, and nonalternation inputs, equal actual
first separators identify the slots except in the exact repeated
same-component nested case. -/
theorem canonicalHullPhysicalFirstSeparator_eq_slot_or_sameComponentNested
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
          (canonicalHullMergerSlotSector axis hn2 hn3 hT assignment a).1
          (canonicalHullMergerSlotSector axis hn2 hn3 hT assignment b).1) →
      (¬Relation.ReflTransGen
          (fullPrunedComponentCotreeDualHullForest
            axis hn2 hn3 hT assignment).ParentStep
          (canonicalHullMergerSlotSector axis hn2 hn3 hT assignment b).1
          (canonicalHullMergerSlotSector axis hn2 hn3 hT assignment a).1) →
      a = b)
    {a b : (fullPrunedComponentCotreeDualHullForest
      axis hn2 hn3 hT assignment).MergerSlot}
    (heq : firstSeparating a = firstSeparating b) :
    a = b ∨ CanonicalHullSameComponentNestedException
      axis hn2 hn3 hT assignment firstSeparating a b := by
  apply canonicalHull_firstSeparating_eq_slot_or_sameComponentNested
    axis hn2 hn3 hT assignment firstSeparating hport hedge hcomponent
  · intro x y hlabel hxy hyx
    apply hnonalternating hlabel
    · simpa [canonicalHullMergerSlotSector,
        canonicalHullMergerSlotChild] using hxy
    · simpa [canonicalHullMergerSlotSector,
        canonicalHullMergerSlotChild] using hyx
  · exact heq

end

end CanonicalExpandedContourForest

end GridGraphs
