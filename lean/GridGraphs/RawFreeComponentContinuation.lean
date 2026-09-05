import GridGraphs.CanonicalReconvergenceLens
import GridGraphs.AlternatingTreeExchange

/-!
# Raw free-component continuation

This module records the relation justified when a continuation enters a raw
free component.  Contacts label occurrences; the only physical component
resource is the retained raw component.  Spatial gaps use the existing
ordinary/corner omitted-edge construction, and equal coordinate edges remain
distinct in the occurrence-labelled cotree-dual carrier.

The relation is deliberately partial.  In particular, it does not assert that
another boundary contact exists, that a dual branch reaches the outer face, or
that any resulting family satisfies Hall.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace CanonicalExpandedContourForest

variable {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
  {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
  (hT : IsSpanningSubtree (gridGraph n n) T)

noncomputable section

/-- A boundary contact occurrence over one raw component.  The component,
rather than this contact label, is the physical resource. -/
structure RawFreeComponentBoundaryContact
    (component : ContactRawComponent (T := T)) where
  resource : FreeComponentContactResource (T := T)
  component_eq : resource.component = component
  boundary : IsGridBoundary resource.contact.1
  retainedDart : GridDirectionalDart T
  retainedDart_source : retainedDart.source = resource.contact.1
  retainedDart_target_mem_support : retainedDart.target ∈
    supportFinset (gridGraph n n \ T)

namespace RawFreeComponentBoundaryContact

theorem contact_mem
    {component : ContactRawComponent (T := T)}
    (contact : RawFreeComponentBoundaryContact (T := T) component) :
    contact.resource.contact ∈ component.supp := by
  simpa [← contact.component_eq] using contact.resource.contact_mem

/-- The concrete retained tree edge attached at this contact. -/
def retainedTreeContactEdge
    {component : ContactRawComponent (T := T)}
    (contact : RawFreeComponentBoundaryContact (T := T) component) :
    GridDirectionalDart T :=
  contact.retainedDart

@[simp] theorem retainedTreeContactEdge_source
    {component : ContactRawComponent (T := T)}
    (contact : RawFreeComponentBoundaryContact (T := T) component) :
    contact.retainedTreeContactEdge.source = contact.resource.contact.1 :=
  contact.retainedDart_source

theorem retainedTreeContactEdge_target_mem_support
    {component : ContactRawComponent (T := T)}
    (contact : RawFreeComponentBoundaryContact (T := T) component) :
    contact.retainedTreeContactEdge.target ∈
      supportFinset (gridGraph n n \ T) :=
  contact.retainedDart_target_mem_support

end RawFreeComponentBoundaryContact

/-- A component spatial gap carries its existing ordinary/corner occurrence
to the omitted transition selected by the boundary-cell construction. -/
noncomputable def rawFreeComponentOmittedTransition
    {component : ContactRawComponent (T := T)}
    (gap : ComponentSpatialGap axis hn2 hT component) :
    LabelledCotreeTransition T :=
  componentOmittedEdgeTransition axis hn2 hn3 hT
    (componentSpatialGapEquivOrdinarySumDuplicatedCorner axis hn2 hT component gap)

theorem componentSpatialGap_current_mem
    {component : ContactRawComponent (T := T)}
    (gap : ComponentSpatialGap axis hn2 hT component) :
    gap.1.1.contact ∈ component.supp := by
  simpa [← gap.1.2] using
    (ContactEnrichedCanonicalMergerToken.contact_mem_component
      axis hn2 hT gap.1.1)

theorem componentSpatialGap_predecessor_mem
    {component : ContactRawComponent (T := T)}
    (gap : ComponentSpatialGap axis hn2 hT component) :
    (componentSpatialGapPredecessor axis hn2 hT gap).1.contact ∈
      component.supp := by
  simpa [← (componentSpatialGapPredecessor axis hn2 hT gap).2] using
    (ContactEnrichedCanonicalMergerToken.contact_mem_component axis hn2 hT
      (componentSpatialGapPredecessor axis hn2 hT gap).1)

/-- Contacts are private occurrence labels and spatial gaps are omitted-edge
occurrences.  Face vertices support the opposite-face result of a certified
tree-basis exchange. -/
abbrev RawFreeComponentContinuationCarrier
    (component : ContactRawComponent (T := T)) :=
  OccurrenceLabelledCotreeDualCarrier
    (m := n) (n := n)
    (RawFreeComponentBoundaryContact (T := T) component)
    (ComponentSpatialGap axis hn2 hT component)

/-- A continuation state retains both debt provenance and its original entry
contact. -/
structure RawFreeComponentContinuationState
    (Origin : Type*) (component : ContactRawComponent (T := T)) where
  origin : Origin
  entry : RawFreeComponentBoundaryContact (T := T) component
  position : RawFreeComponentContinuationCarrier axis hn2 hT component

/-- A contact-labelled tree-basis exchange.  The contact and omitted edge are
provenance for the continuation; the state's raw component remains the sole
component resource. -/
structure RawFreeComponentTreeBasisExchange
    {Origin : Type*} {component : ContactRawComponent (T := T)}
    (state : RawFreeComponentContinuationState axis hn2 hT Origin component) where
  contact : RawFreeComponentBoundaryContact (T := T) component
  at_contact : state.position = .inl contact
  cotree : LabelledCotreeTransition T
  fundamentalPath : T.Walk cotree.1.primalEndpoints.1 cotree.1.primalEndpoints.2
  fundamentalPath_isPath : fundamentalPath.IsPath
  contactEdge_mem : contact.retainedTreeContactEdge.edgeSym2 ∈ fundamentalPath.edges
  enteredFace : GridFace n n
  entered_incident : enteredFace = cotree.1.dualEndpoints.1 ∨
    enteredFace = cotree.1.dualEndpoints.2

namespace RawFreeComponentTreeBasisExchange

variable {Origin : Type*} {component : ContactRawComponent (T := T)}
  {state : RawFreeComponentContinuationState axis hn2 hT Origin component}

theorem cotree_not_tree_adj
    (exchange : RawFreeComponentTreeBasisExchange axis hn2 hT state) :
    ¬T.Adj exchange.cotree.1.primalEndpoints.1
      exchange.cotree.1.primalEndpoints.2 := by
  have hmem := exchange.cotree.2
  rw [SimpleGraph.mem_edgeFinset] at hmem
  exact hmem.2

/-- Fundamental-path membership supplies exactly the basis-exchange
feasibility witness. -/
def alternatingTreeExchange
    (exchange : RawFreeComponentTreeBasisExchange axis hn2 hT state) :
    GridDirectionalDart.AlternatingTreeExchange Origin
      exchange.contact.retainedTreeContactEdge exchange.cotree.1 where
  origin := state.origin
  enteredFace := exchange.enteredFace
  entered_incident := exchange.entered_incident
  feasible := (GridDirectionalDart.BasisExchangeFeasible.iff_treeEdge_mem_fundamentalPath
    hT.isTree exchange.cotree_not_tree_adj exchange.fundamentalPath
      exchange.fundamentalPath_isPath).2 exchange.contactEdge_mem

/-- The path-containment hypothesis really yields cotree-port feasibility. -/
theorem exchange_feasible
    (exchange : RawFreeComponentTreeBasisExchange axis hn2 hT state) :
    GridDirectionalDart.BasisExchangeFeasible
      exchange.contact.retainedTreeContactEdge exchange.cotree.1 :=
  exchange.alternatingTreeExchange.feasible

/-- Continue at the opposite dual face of the inserted cotree edge. -/
def continuationState
    (exchange : RawFreeComponentTreeBasisExchange axis hn2 hT state) :
    RawFreeComponentContinuationState axis hn2 hT Origin component where
  origin := state.origin
  entry := state.entry
  position := .inr (.inr exchange.alternatingTreeExchange.oppositeFace)

@[simp] theorem continue_origin
    (exchange : RawFreeComponentTreeBasisExchange axis hn2 hT state) :
    exchange.continuationState.origin = state.origin := rfl

@[simp] theorem continue_entry
    (exchange : RawFreeComponentTreeBasisExchange axis hn2 hT state) :
    exchange.continuationState.entry = state.entry := rfl

@[simp] theorem continuationState_position
    (exchange : RawFreeComponentTreeBasisExchange axis hn2 hT state) :
    exchange.continuationState.position =
      .inr (.inr exchange.alternatingTreeExchange.oppositeFace) := rfl

/-- The concrete exchange preserves the grid spanning tree. -/
theorem isGridSpanningSubtree
    (exchange : RawFreeComponentTreeBasisExchange axis hn2 hT state) :
    IsSpanningSubtree (gridGraph n n)
      (exchange.contact.retainedTreeContactEdge.basisExchange exchange.cotree.1) :=
  exchange.alternatingTreeExchange.isGridSpanningSubtree hT

end RawFreeComponentTreeBasisExchange

/-- Sound, partial continuation across one raw component.  Every constructor
requires the relevant support-membership proofs.  A contact move must use a
different concrete boundary vertex; a gap move retains its occurrence; and an
exchange move requires fundamental-path containment before entering the
labelled cotree edge's opposite face. -/
inductive RawFreeComponentContinuation {Origin : Type*}
    {component : ContactRawComponent (T := T)} :
    RawFreeComponentContinuationState axis hn2 hT Origin component →
      RawFreeComponentContinuationState axis hn2 hT Origin component → Prop
  | toContact
      (state : RawFreeComponentContinuationState axis hn2 hT Origin component)
      (exit : RawFreeComponentBoundaryContact (T := T) component)
      (entry_mem : state.entry.resource.contact ∈ component.supp)
      (exit_mem : exit.resource.contact ∈ component.supp)
      (contacts_ne : exit.resource.contact.1 ≠ state.entry.resource.contact.1) :
      RawFreeComponentContinuation state
        { origin := state.origin
          entry := state.entry
          position := .inl exit }
  | toOmittedEdge
      (state : RawFreeComponentContinuationState axis hn2 hT Origin component)
      (gap : ComponentSpatialGap axis hn2 hT component)
      (entry_mem : state.entry.resource.contact ∈ component.supp)
      (previous_mem :
        (componentSpatialGapPredecessor axis hn2 hT gap).1.contact ∈ component.supp)
      (current_mem : gap.1.1.contact ∈ component.supp) :
      RawFreeComponentContinuation state
        { origin := state.origin
          entry := state.entry
          position := .inr (.inl gap) }
  | treeBasisExchange
      (state : RawFreeComponentContinuationState axis hn2 hT Origin component)
      (exchange : RawFreeComponentTreeBasisExchange axis hn2 hT state) :
      RawFreeComponentContinuation state exchange.continuationState

namespace RawFreeComponentContinuation

variable {Origin : Type*} {component : ContactRawComponent (T := T)}
  {x y : RawFreeComponentContinuationState axis hn2 hT Origin component}

theorem origin_eq (hxy : RawFreeComponentContinuation axis hn2 hT x y) :
    y.origin = x.origin := by
  cases hxy <;> rfl

theorem entry_eq (hxy : RawFreeComponentContinuation axis hn2 hT x y) :
    y.entry = x.entry := by
  cases hxy <;> rfl

/-- A continuation step cannot change the underlying raw component resource. -/
theorem raw_component_eq
    (hxy : RawFreeComponentContinuation axis hn2 hT x y) :
    y.entry.resource.component = x.entry.resource.component := by
  rw [entry_eq axis hn2 hT hxy]

/-- Raw-component identity and origin provenance survive every finite chain. -/
theorem origin_eq_of_reflTransGen
    (hxy : Relation.ReflTransGen
      (RawFreeComponentContinuation axis hn2 hT) x y) :
    y.origin = x.origin := by
  induction hxy with
  | refl => rfl
  | tail _ hstep ih => exact (origin_eq axis hn2 hT hstep).trans ih

theorem raw_component_eq_of_reflTransGen
    (hxy : Relation.ReflTransGen
      (RawFreeComponentContinuation axis hn2 hT) x y) :
    y.entry.resource.component = x.entry.resource.component := by
  induction hxy with
  | refl => rfl
  | tail _ hstep ih => exact (raw_component_eq axis hn2 hT hstep).trans ih

/-- Reconvergence of occurrence-labelled chains does not merge origins. -/
theorem origins_eq_of_common_descendant
    {z : RawFreeComponentContinuationState axis hn2 hT Origin component}
    (hxz : Relation.ReflTransGen
      (RawFreeComponentContinuation axis hn2 hT) x z)
    (hyz : Relation.ReflTransGen
      (RawFreeComponentContinuation axis hn2 hT) y z) :
    x.origin = y.origin := by
  exact (origin_eq_of_reflTransGen axis hn2 hT hxz).symm.trans
    (origin_eq_of_reflTransGen axis hn2 hT hyz)

end RawFreeComponentContinuation

end

end CanonicalExpandedContourForest

end GridGraphs
