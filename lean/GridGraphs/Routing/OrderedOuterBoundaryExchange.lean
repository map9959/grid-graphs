import GridGraphs.Routing.AutomaticOwnershipDisplacement
import GridGraphs.Geometry.GridCrosscutCycle

/-!
# Ordered exchange on split outer boundary ports

Split outer ports are ordered by the vertices at which their outward stubs meet
the one-cell collar.  Thus the two incidences at a corner remain distinct.  A
reserved port displaces its unique canonical exit owner and advances in one of
the two cyclic directions.  A genuinely unreserved port is terminal.

Termination is deliberately conditional on an explicit witness that the exit
reservation is not full.  This module contains no Hall assertion.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace CanonicalExpandedContourForest

variable {n : Nat} {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## Geometric cyclic order -/

/-- The collar vertex reached by the outward stub of a split outer port. -/
def splitOuterPortCollarVertex (hn2 : 2 ≤ n) (port : GridCotreeOuterPort T) :
    GridVertex (n + 2) (n + 2) :=
  match port.side with
  | .top => (⟨0, by omega⟩, ⟨port.vertex.2.val + 1, by omega⟩)
  | .bottom => (⟨n + 1, by omega⟩, ⟨port.vertex.2.val + 1, by omega⟩)
  | .left => (⟨port.vertex.1.val + 1, by omega⟩, ⟨0, by omega⟩)
  | .right => (⟨port.vertex.1.val + 1, by omega⟩, ⟨n + 1, by omega⟩)

theorem splitOuterPortCollarVertex_isBoundary (hn2 : 2 ≤ n)
    (port : GridCotreeOuterPort T) :
    IsGridBoundary (splitOuterPortCollarVertex hn2 port) := by
  rcases port with port | port | port | port <;>
    simp [splitOuterPortCollarVertex, OuterBoundaryPort.side, IsGridBoundary]

theorem splitOuterPortCollarVertex_injective (hn2 : 2 ≤ n) :
    Function.Injective (splitOuterPortCollarVertex hn2 (T := T)) := by
  intro a b hab
  have hs : a.side = b.side := by
    rcases a with a | a | a | a <;> rcases b with b | b | b | b <;>
      simp [OuterBoundaryPort.side, splitOuterPortCollarVertex] at hab ⊢
    all_goals
      have h := congrArg (fun v => (v.1.val, v.2.val)) hab
      simp at h
      try omega
  apply OuterBoundaryPort.ext
  · rcases a with a | a | a | a <;> rcases b with b | b | b | b <;>
      simp [OuterBoundaryPort.side] at hs
    all_goals
      apply Prod.ext <;> apply Fin.ext
      all_goals
        have ha := (Finset.mem_filter.mp a.2).2
        have hb := (Finset.mem_filter.mp b.2).2
        have h := congrArg (fun v => (v.1.val, v.2.val)) hab
        simp [splitOuterPortCollarVertex, OuterBoundaryPort.side,
          OuterBoundaryPort.vertex] at h
        simp [OuterBoundaryPort.vertex]
        omega
  · exact hs

/-- Clockwise collar-boundary occurrence occupied by a split outer port. -/
def splitOuterPortPosition (hn2 : 2 ≤ n) (port : GridCotreeOuterPort T) :
    GridBoundaryPosition (n + 2) (n + 2) :=
  collarBoundaryPosition (splitOuterPortCollarVertex hn2 port)
    (splitOuterPortCollarVertex_isBoundary hn2 port)

@[simp] theorem gridBoundaryVertex_splitOuterPortPosition
    (hn2 : 2 ≤ n) (port : GridCotreeOuterPort T) :
    gridBoundaryVertex (by omega) (by omega) (splitOuterPortPosition hn2 port) =
      splitOuterPortCollarVertex hn2 port :=
  gridBoundaryVertex_collarBoundaryPosition _ _

theorem splitOuterPortPosition_injective (hn2 : 2 ≤ n) :
    Function.Injective (splitOuterPortPosition hn2 (T := T)) := by
  intro a b hab
  apply splitOuterPortCollarVertex_injective hn2
  rw [← gridBoundaryVertex_splitOuterPortPosition hn2 a,
    ← gridBoundaryVertex_splitOuterPortPosition hn2 b, hab]

/-- The split-boundary occurrence order factors through its canonical physical
port. -/
def boundaryOccurrencePosition
    (hn2 : 2 ≤ n) {O : Type*} (transition : O → LabelledCotreeTransition T)
    (occurrence : BoundaryTransitionOccurrence transition) :
    GridBoundaryPosition (n + 2) (n + 2) :=
  splitOuterPortPosition hn2
    (BoundaryTransitionOccurrence.outerPort transition hn2 hn2 occurrence)

theorem boundaryOccurrencePosition_injective
    {O : Type*} (transition : O → LabelledCotreeTransition T)
    (hchoice : BoundaryTransitionOccurrence.PortChoiceInjective
      transition hn2 hn2) :
    Function.Injective
      (boundaryOccurrencePosition hn2 (T := T) transition) := by
  intro a b hab
  apply hchoice
  apply splitOuterPortPosition_injective hn2
  exact hab

private def reverseFinEquiv (k : Nat) : Fin k ≃ Fin k where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_involutive
  right_inv := Fin.rev_involutive

/-- Direction in which the ordered alternating search scans split ports. -/
inductive OuterTraversalDirection
  | clockwise
  | counterclockwise
  deriving DecidableEq

/-- Increasing enumeration of ports by collar position, reversed in the
counterclockwise case. -/
def orderedOuterPortEquiv (hn2 : 2 ≤ n) (direction : OuterTraversalDirection) :
    Fin (Fintype.card (GridCotreeOuterPort T)) ≃ GridCotreeOuterPort T := by
  letI : LinearOrder (GridCotreeOuterPort T) :=
    LinearOrder.lift' (splitOuterPortPosition hn2 (T := T))
      (splitOuterPortPosition_injective hn2)
  let ordered := (monoEquivOfFin (GridCotreeOuterPort T) rfl).toEquiv
  exact match direction with
    | .clockwise => ordered
    | .counterclockwise => (reverseFinEquiv _).trans ordered

theorem outerPort_card_pos (hn2 : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    0 < Fintype.card (GridCotreeOuterPort T) :=
  Fintype.card_pos_iff.mpr (outerPort_nonempty hn2 hT)

variable (axis : ShoreSweepAxis) (hn2 : 2 ≤ n)
  (hT : IsSpanningSubtree (gridGraph n n) T)

/-- Port reached after `steps` scans in the selected cyclic direction. -/
def orderedOuterPortAt (direction : OuterTraversalDirection)
    (start : GridCotreeOuterPort T) (steps : Nat) : GridCotreeOuterPort T :=
  orderedOuterPortEquiv hn2 (T := T) direction
    (cyclicOffset (outerPort_card_pos hn2 hT)
      ((orderedOuterPortEquiv hn2 (T := T) direction).symm start) steps)

@[simp] theorem orderedOuterPortAt_zero (direction : OuterTraversalDirection)
    (start : GridCotreeOuterPort T) :
    orderedOuterPortAt hn2 hT direction start 0 = start := by
  simp [orderedOuterPortAt, cyclicOffset, Nat.mod_eq_of_lt]

theorem orderedOuterPortAt_succ (direction : OuterTraversalDirection)
    (start : GridCotreeOuterPort T) (steps : Nat) :
    orderedOuterPortAt hn2 hT direction start (steps + 1) =
      orderedOuterPortAt hn2 hT direction
        (orderedOuterPortAt hn2 hT direction start steps) 1 := by
  simp only [orderedOuterPortAt]
  simp only [Equiv.symm_apply_apply]
  congr 1
  apply Fin.ext
  change
    (((orderedOuterPortEquiv hn2 (T := T) direction).symm start).val +
        (steps + 1)) % Fintype.card (GridCotreeOuterPort T) =
      ((((orderedOuterPortEquiv hn2 (T := T) direction).symm start).val +
          steps) % Fintype.card (GridCotreeOuterPort T) + 1) %
        Fintype.card (GridCotreeOuterPort T)
  rw [show
    ((orderedOuterPortEquiv hn2 (T := T) direction).symm start).val +
        (steps + 1) =
      (((orderedOuterPortEquiv hn2 (T := T) direction).symm start).val +
        steps) + 1 by omega, Nat.add_mod]
  simp

/-! ## Reserved displacement and terminal states -/

/-- A traversal state retains the occurrence that initiated the search. -/
structure OrderedOuterTraversalState (Origin : Type*) where
  origin : Origin
  port : GridCotreeOuterPort T

abbrev ClockwiseOuterTraversalState (Origin : Type*) :=
  OrderedOuterTraversalState (T := T) Origin

abbrev CounterclockwiseOuterTraversalState (Origin : Type*) :=
  OrderedOuterTraversalState (T := T) Origin

/-- One reserved step displaces the exit which uniquely owns the current port,
then advances one port in the chosen cyclic direction. -/
inductive OrderedOuterTraversalStep (direction : OuterTraversalDirection)
    {Origin : Type*} :
    OrderedOuterTraversalState (T := T) Origin →
      OrderedOuterTraversalState (T := T) Origin → Prop
  | reserved (state) (owner : ↥(planeChannelForest axis hn2 hT).exits)
      (owns : exitEmbedding axis hn2 hT owner = state.port) :
      OrderedOuterTraversalStep direction state
        ⟨state.origin, orderedOuterPortAt hn2 hT direction state.port 1⟩

abbrev ClockwiseOuterTraversalStep {Origin : Type*} :=
  OrderedOuterTraversalStep axis hn2 hT .clockwise
    (Origin := Origin)

abbrev CounterclockwiseOuterTraversalStep {Origin : Type*} :=
  OrderedOuterTraversalStep axis hn2 hT .counterclockwise
    (Origin := Origin)

/-- Any exit displaced at a reserved step is unique. -/
theorem orderedOuterTraversalStep_owner_unique
    {Origin : Type*} {source : OrderedOuterTraversalState (T := T) Origin}
    {a b : ↥(planeChannelForest axis hn2 hT).exits}
    (ha : exitEmbedding axis hn2 hT a = source.port)
    (hb : exitEmbedding axis hn2 hT b = source.port) : a = b :=
  (exitEmbedding axis hn2 hT).injective (ha.trans hb.symm)

/-- Free states are exactly states whose current port has the existing
unreserved-port type. -/
def OrderedOuterTraversalState.IsFree {Origin : Type*}
    (state : OrderedOuterTraversalState (T := T) Origin) : Prop :=
  state.port ∉ Set.range (exitEmbedding axis hn2 hT)

theorem orderedOuterTraversalStep_origin_eq
    (direction : OuterTraversalDirection) {Origin : Type*}
    {source target : OrderedOuterTraversalState (T := T) Origin}
    (step : OrderedOuterTraversalStep axis hn2 hT direction source target) :
    target.origin = source.origin := by
  cases step
  rfl

theorem origin_eq_of_orderedOuterTraversalPath
    (direction : OuterTraversalDirection) {Origin : Type*}
    {source target : OrderedOuterTraversalState (T := T) Origin}
    (path : Relation.ReflTransGen
      (OrderedOuterTraversalStep axis hn2 hT direction) source target) :
    target.origin = source.origin := by
  induction path with
  | refl => rfl
  | tail _ step ih =>
      exact (orderedOuterTraversalStep_origin_eq axis hn2 hT direction step).trans ih

/-- A free port has no outgoing displacement step. -/
theorem OrderedOuterTraversalState.no_step_of_free
    (direction : OuterTraversalDirection) {Origin : Type*}
    (state : OrderedOuterTraversalState (T := T) Origin)
    (hfree : state.IsFree axis hn2 hT) :
    ¬∃ next, OrderedOuterTraversalStep axis hn2 hT direction state next := by
  rintro ⟨next, step⟩
  cases step with
  | reserved owner owns => exact hfree ⟨owner, owns⟩

/-- Explicit hypothesis under which a boundary scan may terminate. -/
abbrev ExitReservationNotFull : Prop :=
  Nonempty (UnreservedCanonicalBoundaryPort axis hn2 hT)

/-- Complete finite execution certificate.  Every earlier port is reserved,
the path consists of the corresponding unique-owner displacement steps, and
the endpoint is free. -/
structure OrderedOuterTraversalTermination (direction : OuterTraversalDirection)
    {Origin : Type*} (initial : OrderedOuterTraversalState (T := T) Origin) where
  steps : Nat
  steps_lt : steps < Fintype.card (GridCotreeOuterPort T)
  terminal : OrderedOuterTraversalState (T := T) Origin
  terminal_eq : terminal =
    ⟨initial.origin, orderedOuterPortAt hn2 hT direction initial.port steps⟩
  earlier_reserved : ∀ i < steps,
    orderedOuterPortAt hn2 hT direction initial.port i ∈
      Set.range (exitEmbedding axis hn2 hT)
  reached : Relation.ReflTransGen
    (OrderedOuterTraversalStep axis hn2 hT direction) initial terminal
  terminal_free : terminal.IsFree axis hn2 hT

private theorem exists_free_orderedOuterPortAt
    (direction : OuterTraversalDirection) (start : GridCotreeOuterPort T)
    (hnotFull : ExitReservationNotFull axis hn2 hT) :
    ∃ steps < Fintype.card (GridCotreeOuterPort T),
      orderedOuterPortAt hn2 hT direction start steps ∉
        Set.range (exitEmbedding axis hn2 hT) := by
  let free : UnreservedCanonicalBoundaryPort axis hn2 hT :=
    Classical.choice hnotFull
  let freePort : GridCotreeOuterPort T := free.1
  let startIndex := (orderedOuterPortEquiv hn2 (T := T) direction).symm start
  let freeIndex := (orderedOuterPortEquiv hn2 (T := T) direction).symm freePort
  let steps := cyclicForwardDistance (outerPort_card_pos hn2 hT) startIndex freeIndex
  refine ⟨steps, cyclicForwardDistance_lt _ _ _, ?_⟩
  have hat : orderedOuterPortAt hn2 hT direction start steps = freePort := by
    simp only [orderedOuterPortAt]
    rw [show freePort = orderedOuterPortEquiv hn2 (T := T) direction freeIndex by
      simp [freeIndex]]
    congr 1
    simpa [startIndex, freeIndex, steps] using
      cyclicOffset_forwardDistance (outerPort_card_pos hn2 hT) startIndex freeIndex
  rw [hat]
  exact free.2

private theorem reached_orderedOuterPortAt
    (direction : OuterTraversalDirection) {Origin : Type*}
    (initial : OrderedOuterTraversalState (T := T) Origin) (steps : Nat)
    (hreserved : ∀ i < steps,
      orderedOuterPortAt hn2 hT direction initial.port i ∈
        Set.range (exitEmbedding axis hn2 hT)) :
    Relation.ReflTransGen (OrderedOuterTraversalStep axis hn2 hT direction)
      initial ⟨initial.origin,
        orderedOuterPortAt hn2 hT direction initial.port steps⟩ := by
  induction steps with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ steps ih =>
      have hprefix := ih (fun i hi => hreserved i (by omega))
      obtain ⟨owner, howner⟩ := hreserved steps (by omega)
      have hstep : OrderedOuterTraversalStep axis hn2 hT direction
          (⟨initial.origin, orderedOuterPortAt hn2 hT direction initial.port steps⟩)
          (⟨initial.origin,
            orderedOuterPortAt hn2 hT direction
              (orderedOuterPortAt hn2 hT direction initial.port steps) 1⟩) :=
        .reserved _ owner howner
      rw [← orderedOuterPortAt_succ hn2 hT direction initial.port steps] at hstep
      exact hprefix.tail hstep

/-- Clockwise or counterclockwise scanning reaches a free port in fewer than
one full pass, provided explicitly that the canonical exit reservation is not
full. -/
noncomputable def orderedOuterTraversal_terminates
    (direction : OuterTraversalDirection) {Origin : Type*}
    (initial : OrderedOuterTraversalState (T := T) Origin)
    (hnotFull : ExitReservationNotFull axis hn2 hT) :
    OrderedOuterTraversalTermination axis hn2 hT direction initial := by
  let witness := exists_free_orderedOuterPortAt axis hn2 hT direction
    initial.port hnotFull
  let steps := Nat.find witness
  have hspec := Nat.find_spec witness
  have hminimal : ∀ i < steps,
      orderedOuterPortAt hn2 hT direction initial.port i ∈
        Set.range (exitEmbedding axis hn2 hT) := by
    intro i hi
    by_contra hfree
    exact (Nat.find_min witness hi) ⟨by omega, hfree⟩
  let terminal : OrderedOuterTraversalState (T := T) Origin :=
    ⟨initial.origin, orderedOuterPortAt hn2 hT direction initial.port steps⟩
  exact
    { steps := steps
      steps_lt := hspec.1
      terminal := terminal
      terminal_eq := rfl
      earlier_reserved := hminimal
      reached := reached_orderedOuterPortAt axis hn2 hT direction initial steps hminimal
      terminal_free := hspec.2 }

end

end CanonicalExpandedContourForest

end GridGraphs
