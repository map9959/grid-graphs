import GridGraphs.Geometry.GridTriangleFree

/-!
# Sequential finite delete/add surgery

This file records the bookkeeping common to finite surgery arguments.  It is
independent of the geometry used to choose the deletions and new owners.
-/

namespace GridGraphs

open Finset SimpleGraph

variable {V : Type*}

/-- One surgery step deletes vertices from the current state and inserts a
genuinely new owner. -/
structure SurgeryStep [DecidableEq V] (state : Finset V) where
  deletion : Finset V
  owner : V
  deletion_subset : deletion ⊆ state
  owner_not_mem : owner ∉ state

namespace SurgeryStep

variable [DecidableEq V] {state : Finset V}

/-- The state produced by a surgery step. -/
def next (step : SurgeryStep state) : Finset V :=
  insert step.owner (state \ step.deletion)

theorem owner_not_mem_remainder (step : SurgeryStep state) :
    step.owner ∉ state \ step.deletion := by
  intro h
  exact step.owner_not_mem (Finset.mem_sdiff.mp h).1

/-- Exact one-step accounting: one owner is gained and every listed deletion
is lost. -/
theorem card_next_add_card_deletion (step : SurgeryStep state) :
    step.next.card + step.deletion.card = state.card + 1 := by
  rw [next, Finset.card_insert_of_notMem step.owner_not_mem_remainder]
  have hdelete := Finset.card_sdiff_add_card_eq_card step.deletion_subset
  omega

theorem coe_next (step : SurgeryStep state) :
    (↑step.next : Set V) =
      insert step.owner (↑(state \ step.deletion) : Set V) := by
  simp only [next, Finset.coe_insert]

end SurgeryStep

/-- A grid surgery step together with the geometric facts supplied by the
triangle-free tooth deletion. -/
structure GridToothSurgeryStep {m n : Nat}
    (state : Finset (GridVertex m n)) (owner : GridVertex m n) where
  step : SurgeryStep state
  step_owner : step.owner = owner
  deletion_disjoint_owner :
    Disjoint (↑step.deletion : Set (GridVertex m n))
      ((gridGraph m n).neighborSet owner)
  deletion_card_le : step.deletion.card ≤ 3
  insertion : ForcedInsertionCondition (gridGraph m n)
    (↑(state \ step.deletion) : Set (GridVertex m n)) owner
  next_isAcyclic :
    (forcedEdgeGraph (gridGraph m n)
      (↑step.next : Set (GridVertex m n))).IsAcyclic

/-- Every fresh owner of an acyclic forced grid state admits a tooth surgery
step deleting at most three non-neighbors from the state. -/
theorem exists_gridToothSurgeryStep {m n : Nat}
    (state : Finset (GridVertex m n)) (owner : GridVertex m n)
    (howner : owner ∉ state)
    (hstate : (forcedEdgeGraph (gridGraph m n)
      (↑state : Set (GridVertex m n))).IsAcyclic) :
    Nonempty (GridToothSurgeryStep state owner) := by
  classical
  obtain ⟨deletion, hsubset, hdisjoint, hcard, hnext⟩ :=
    exists_grid_deletion_for_forcedEdgeGraph_insert_isAcyclic
      (↑state : Set (GridVertex m n)) owner howner hstate
  let step : SurgeryStep state := {
    deletion := deletion
    owner := owner
    deletion_subset := hsubset
    owner_not_mem := howner
  }
  have hdeleted :
      (forcedEdgeGraph (gridGraph m n)
        (↑(state \ deletion) : Set (GridVertex m n))).IsAcyclic := by
    rw [show (↑(state \ deletion) : Set (GridVertex m n)) =
      (↑state : Set (GridVertex m n)) \ (↑deletion : Set (GridVertex m n)) by
        ext
        simp]
    exact forcedEdgeGraph_diff_isAcyclic (gridGraph m n) hstate _
  have howner_remainder :
      owner ∉ (↑(state \ deletion) : Set (GridVertex m n)) := by
    intro h
    exact howner (Finset.mem_sdiff.mp h).1
  have hinsertion : ForcedInsertionCondition (gridGraph m n)
      (↑(state \ deletion) : Set (GridVertex m n)) owner := by
    apply (forcedEdgeGraph_insert_isAcyclic_iff
      howner_remainder hdeleted).mp
    simpa only [Finset.coe_sdiff] using hnext
  refine ⟨{
    step := step
    step_owner := rfl
    deletion_disjoint_owner := hdisjoint
    deletion_card_le := hcard
    insertion := hinsertion
    next_isAcyclic := ?_
  }⟩
  simpa only [step, SurgeryStep.coe_next, Finset.coe_sdiff] using hnext

/-- Exact cardinal gain for the certified grid step. -/
theorem GridToothSurgeryStep.card_next_add_card_deletion {m n : Nat}
    {state : Finset (GridVertex m n)} {owner : GridVertex m n}
    (certificate : GridToothSurgeryStep state owner) :
    certificate.step.next.card + certificate.step.deletion.card =
      state.card + 1 :=
  certificate.step.card_next_add_card_deletion

/-- A dependent trace: the tail starts at exactly the state produced by its
head step, so valid transitions are part of the certificate. -/
inductive SurgeryTrace [DecidableEq V] : Finset V → Type _ where
  | nil (state : Finset V) : SurgeryTrace state
  | cons {state : Finset V} (step : SurgeryStep state)
      (tail : SurgeryTrace step.next) : SurgeryTrace state

namespace SurgeryTrace

variable [DecidableEq V]

/-- All states in a trace, including both endpoints. -/
def states {state : Finset V} : SurgeryTrace state → List (Finset V)
  | .nil _ => [state]
  | .cons _ tail => state :: tail.states

/-- The deletion made at each transition. -/
def deletions {state : Finset V} : SurgeryTrace state → List (Finset V)
  | .nil _ => []
  | .cons step tail => step.deletion :: tail.deletions

/-- The owner inserted at each transition. -/
def owners {state : Finset V} : SurgeryTrace state → List V
  | .nil _ => []
  | .cons step tail => step.owner :: tail.owners

/-- The final state of a trace. -/
def final {state : Finset V} : SurgeryTrace state → Finset V
  | .nil _ => state
  | .cons _ tail => tail.final

/-- Deletions are counted with multiplicity across the trace. -/
def deletionCost {state : Finset V} (trace : SurgeryTrace state) : Nat :=
  match trace with
  | .nil _ => 0
  | .cons step tail => step.deletion.card + tail.deletionCost

/-- Per-step conditions certifying that each insertion preserves forced-edge
acyclicity after its deletion. -/
def AcyclicInsertions [Fintype V] (G : SimpleGraph V) :
    ∀ {state : Finset V}, SurgeryTrace state → Prop
  | _, .nil _ => True
  | state, .cons step tail =>
      ForcedInsertionCondition G
          ((↑(state \ step.deletion) : Set V)) step.owner ∧
        AcyclicInsertions G tail

/-- Exact telescoping accounting for the whole trace. -/
theorem card_final_add_deletionCost {state : Finset V}
    (trace : SurgeryTrace state) :
    trace.final.card + trace.deletionCost = state.card + trace.owners.length := by
  induction trace with
  | nil state => simp [final, deletionCost, owners]
  | @cons state step tail ih =>
      rw [final, deletionCost, owners]
      simp only [List.length_cons]
      have hstep := step.card_next_add_card_deletion
      omega

/-- Initial forced-edge acyclicity and the insertion certificate imply
acyclicity at the final state. -/
theorem forcedEdgeGraph_final_isAcyclic [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {state : Finset V} (trace : SurgeryTrace state)
    (hstate : (forcedEdgeGraph G (↑state : Set V)).IsAcyclic)
    (hinsert : AcyclicInsertions G trace) :
    (forcedEdgeGraph G (↑trace.final : Set V)).IsAcyclic := by
  induction trace with
  | nil state => simpa [final]
  | @cons state step tail ih =>
      have hdeleted :
          (forcedEdgeGraph G
            ((↑(state \ step.deletion) : Set V))).IsAcyclic := by
        rw [show (↑(state \ step.deletion) : Set V) =
            (↑state : Set V) \ (↑step.deletion : Set V) by ext; simp]
        exact forcedEdgeGraph_diff_isAcyclic G hstate _
      have hnext :
          (forcedEdgeGraph G (↑step.next : Set V)).IsAcyclic := by
        rw [step.coe_next]
        exact (forcedEdgeGraph_insert_isAcyclic_iff
          step.owner_not_mem_remainder hdeleted).mpr hinsert.1
      exact ih hnext hinsert.2

end SurgeryTrace

/-- Dependent freshness for a proposed owner list.  The tail must remain
eligible after every certified bounded step chosen for the current owner. -/
def GridSurgeryEligible {m n : Nat} :
    (state : Finset (GridVertex m n)) → List (GridVertex m n) → Prop
  | _, [] => True
  | state, owner :: owners =>
      owner ∉ state ∧
        ∀ certificate : GridToothSurgeryStep state owner,
          GridSurgeryEligible certificate.step.next owners

/-- A dependently eligible owner list generates a bounded tooth-surgery trace
whose insertion certificates and final forced-edge acyclicity are explicit. -/
theorem exists_grid_tooth_surgery_trace {m n : Nat}
    (owners : List (GridVertex m n)) :
    ∀ (state : Finset (GridVertex m n)),
      (forcedEdgeGraph (gridGraph m n)
        (↑state : Set (GridVertex m n))).IsAcyclic →
      GridSurgeryEligible state owners →
      ∃ trace : SurgeryTrace state,
        trace.owners = owners ∧
        trace.AcyclicInsertions (gridGraph m n) ∧
        (forcedEdgeGraph (gridGraph m n)
          (↑trace.final : Set (GridVertex m n))).IsAcyclic := by
  induction owners with
  | nil =>
      intro state hstate _
      exact ⟨.nil state, rfl, trivial, hstate⟩
  | cons owner owners ih =>
      intro state hstate heligible
      obtain ⟨certificate⟩ :=
        exists_gridToothSurgeryStep state owner heligible.1 hstate
      obtain ⟨tail, howners, hacyclic, hfinal⟩ :=
        ih certificate.step.next certificate.next_isAcyclic
          (heligible.2 certificate)
      refine ⟨.cons certificate.step tail, ?_, ?_, ?_⟩
      · rw [SurgeryTrace.owners, howners, certificate.step_owner]
      · constructor
        · rw [certificate.step_owner]
          exact certificate.insertion
        · exact hacyclic
      · exact hfinal

/-- Vertices of the initial state absent from the final state. -/
def finalDeleted [DecidableEq V] (initial final : Finset V) : Finset V :=
  initial \ final

/-- Vertices of the final state absent from the initial state. -/
def finalAdded [DecidableEq V] (initial final : Finset V) : Finset V :=
  final \ initial

/-- Canonical normalization of a final finite state relative to its initial
state. -/
theorem final_eq_initial_sdiff_finalDeleted_union_finalAdded [DecidableEq V]
    (initial final : Finset V) :
    final = (initial \ finalDeleted initial final) ∪ finalAdded initial final := by
  ext v
  simp [finalDeleted, finalAdded]
  tauto

/-- Exact cardinal accounting for the canonical initial/final normalization. -/
theorem card_final_add_card_finalDeleted [DecidableEq V]
    (initial final : Finset V) :
    final.card + (finalDeleted initial final).card =
      initial.card + (finalAdded initial final).card := by
  have hinitial := Finset.card_sdiff_add_card_inter initial final
  have hfinal := Finset.card_sdiff_add_card_inter final initial
  simp only [finalDeleted, finalAdded]
  rw [Finset.inter_comm] at hfinal
  omega

end GridGraphs
