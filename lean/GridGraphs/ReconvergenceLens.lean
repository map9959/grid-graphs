import GridGraphs.MarkedCycleFirstStop
import GridGraphs.ParentForestFirstStop

/-!
# Occurrence-level reconvergence lenses

This is the first combinatorial lens layer.  A merger slot is kept as an
occurrence even though binary mergers have a canonical underlying shared state.
The parent is the first later merger on that state's first-stop suffix.  No
resource cardinality, waste, or planar-region assertion is used.
-/

namespace GridGraphs

open Finset

namespace MarkedCycleFirstStop

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- An occurrence-level lens retains its concrete merger-excess slot together
with the canonical shared state, occurrence owner/start, and stop-distance. -/
structure ReconvergenceLens (F : MarkedCycleFirstStop X) where
  mergerSlot : F.forest.MergerSlot
  mergerState : F.MergerState
  mergerState_eq : mergerState = F.mergerSlotMergerStateEquiv mergerSlot
  ownerStart : ↥F.starts
  ownerStart_eq : ownerStart = F.mergerOwnerStart mergerState
  rank : Nat
  rank_eq : rank = F.distance mergerState.1.1

namespace ReconvergenceLens

variable {F : MarkedCycleFirstStop X}

/-- The lens associated to one concrete merger slot. -/
def ofSlot (s : F.forest.MergerSlot) : F.ReconvergenceLens where
  mergerSlot := s
  mergerState := F.mergerSlotMergerStateEquiv s
  mergerState_eq := rfl
  ownerStart := F.mergerOwnerStart (F.mergerSlotMergerStateEquiv s)
  ownerStart_eq := rfl
  rank := F.distance (F.mergerSlotMergerStateEquiv s).1.1
  rank_eq := rfl

@[ext] theorem ext {L K : F.ReconvergenceLens}
    (h : L.mergerSlot = K.mergerSlot) : L = K := by
  cases L with
  | mk ls lm hl lo hlo lr hlr =>
      cases K with
      | mk ks km hk ko hko kr hkr =>
          dsimp at h
          subst ks
          subst lm
          subst km
          subst lo
          subst ko
          subst lr
          subst kr
          rfl

instance : Fintype F.ReconvergenceLens :=
  Fintype.ofEquiv F.forest.MergerSlot
    { toFun := ofSlot
      invFun := mergerSlot
      left_inv := fun _ => rfl
      right_inv := fun L => ext (L := ofSlot L.mergerSlot) (K := L) rfl }

/-- A later merger occurrence lies on the unique shared suffix of `L`. -/
def OnSharedSuffix (L K : F.ReconvergenceLens) : Prop :=
  ∃ k, 0 < k ∧ k ≤ L.rank ∧
    ((F.f : X → X)^[k]) L.mergerState.1.1 = K.mergerState.1.1

/-- There is another merger after `L` and no later than its reached stop. -/
def HasNext (L : F.ReconvergenceLens) : Prop :=
  ∃ k, 0 < k ∧ k ≤ L.rank ∧
    ∃ K : F.MergerState,
      ((F.f : X → X)^[k]) L.mergerState.1.1 = K.1.1

/-- Least positive distance to a later merger on the shared suffix. -/
def nextDistance (L : F.ReconvergenceLens) (h : L.HasNext) : Nat :=
  Nat.find h

/-- The canonical merger state at the least later-merger distance. -/
def nextMergerState (L : F.ReconvergenceLens) (h : L.HasNext) : F.MergerState :=
  (Nat.find_spec h).2.2.choose

theorem nextMergerState_spec (L : F.ReconvergenceLens) (h : L.HasNext) :
    0 < L.nextDistance h ∧ L.nextDistance h ≤ L.rank ∧
      ((F.f : X → X)^[L.nextDistance h]) L.mergerState.1.1 =
        (L.nextMergerState h).1.1 :=
  ⟨(Nat.find_spec h).1, (Nat.find_spec h).2.1,
    (Nat.find_spec h).2.2.choose_spec⟩

/-- No merger occurs strictly earlier on the same suffix. -/
theorem nextDistance_minimal (L : F.ReconvergenceLens) (h : L.HasNext)
    {k : Nat} (hkpos : 0 < k) (hkle : k ≤ L.rank)
    {K : F.MergerState}
    (hK : ((F.f : X → X)^[k]) L.mergerState.1.1 = K.1.1) :
    L.nextDistance h ≤ k :=
  Nat.find_min' h ⟨hkpos, hkle, K, hK⟩

/-- The concrete slot at the next merger.  Binary first-stop mergers have one
slot, so the merger-state equivalence makes this choice canonical. -/
def nextSlot (L : F.ReconvergenceLens) (h : L.HasNext) :
    F.forest.MergerSlot :=
  F.mergerSlotMergerStateEquiv.symm (L.nextMergerState h)

/-- Partial parent map to the first later merger on the shared suffix. -/
def parent (L : F.ReconvergenceLens) : Option F.ReconvergenceLens :=
  if h : L.HasNext then some (ofSlot (L.nextSlot h)) else none

theorem mergerState_ofSlot (s : F.forest.MergerSlot) :
    (ofSlot s).mergerState = F.mergerSlotMergerStateEquiv s := rfl

theorem mergerState_nextSlot (L : F.ReconvergenceLens) (h : L.HasNext) :
    (ofSlot (L.nextSlot h)).mergerState = L.nextMergerState h := by
  exact F.mergerSlotMergerStateEquiv.apply_symm_apply _

/-- A parent is exactly the first later merger occurrence selected above. -/
theorem parent_eq_some_iff (L K : F.ReconvergenceLens) :
    L.parent = some K ↔
      ∃ h : L.HasNext, K = ofSlot (L.nextSlot h) := by
  unfold parent
  split
  · rename_i h
    constructor
    · intro hp
      exact ⟨h, Option.some.inj hp |>.symm⟩
    · rintro ⟨h', rfl⟩
      congr
  · rename_i h
    simp [h]

/-- The partial map is maximal: it is undefined exactly when the shared suffix
contains no later merger. -/
theorem parent_eq_none_iff (L : F.ReconvergenceLens) :
    L.parent = none ↔ ¬L.HasNext := by
  unfold parent
  split <;> simp_all

/-- Parent selection stays on the merger's shared first-stop suffix. -/
theorem onSharedSuffix_of_parent {L K : F.ReconvergenceLens}
    (hparent : L.parent = some K) : L.OnSharedSuffix K := by
  obtain ⟨h, rfl⟩ := (parent_eq_some_iff L K).mp hparent
  refine ⟨L.nextDistance h, (L.nextMergerState_spec h).1,
    (L.nextMergerState_spec h).2.1, ?_⟩
  rw [mergerState_nextSlot]
  exact (L.nextMergerState_spec h).2.2

/-- Any positive move along a first-stop suffix strictly lowers stop-distance. -/
theorem rank_lt_of_onSharedSuffix {L K : F.ReconvergenceLens}
    (hLK : L.OnSharedSuffix K) : K.rank < L.rank := by
  rcases hLK with ⟨k, hkpos, hkle, hiterate⟩
  rw [L.rank_eq] at hkle
  have hadd := F.distance_iterate_add L.mergerState.1.1 hkle hiterate
  rw [K.rank_eq, L.rank_eq]
  omega

/-- Strict rank decrease for the partial lens parent map. -/
theorem rank_parent {L K : F.ReconvergenceLens}
    (hparent : L.parent = some K) : K.rank < L.rank :=
  rank_lt_of_onSharedSuffix (onSharedSuffix_of_parent hparent)

/-- The occurrence-level lenses form a ranked parent forest. -/
def forest (F : MarkedCycleFirstStop X) : ParentForest F.ReconvergenceLens where
  parent := parent
  rank := fun L => L.rank
  rank_parent := rank_parent

/-- The canonical owner really occurs on the merger's first-stop interval. -/
theorem ownerStart_mem_origins (L : F.ReconvergenceLens) :
    L.ownerStart ∈ F.origins L.mergerState.1 := by
  rw [L.ownerStart_eq]
  by_cases hm : L.mergerState.1.1 ∈ F.stop
  · have hpre := (F.marked_mergerOwner_relation L.mergerState hm).1
    exact F.origins_mono_stateParent
      (F.stateParent_mergerPredecessor L.mergerState) hpre
  · apply (F.mem_origins_iff L.mergerState.1
      (F.mergerOwnerStart L.mergerState)).2
    refine ⟨0, Nat.zero_le _, ?_⟩
    simp only [Function.iterate_zero, id_eq]
    exact F.mergerOwner_eq_self_of_not_mem_stop L.mergerState hm

/-- Provenance can only accumulate when passing to a parent lens. -/
theorem origins_subset_of_parent {L K : F.ReconvergenceLens}
    (hparent : L.parent = some K) :
    F.origins L.mergerState.1 ⊆ F.origins K.mergerState.1 := by
  rcases onSharedSuffix_of_parent hparent with ⟨k, -, hkle, hiterate⟩
  rw [L.rank_eq] at hkle
  intro s hs
  rcases (F.mem_origins_iff L.mergerState.1 s).1 hs with ⟨j, hj, hjstate⟩
  apply (F.mem_origins_iff K.mergerState.1 s).2
  refine ⟨j + k, ?_, ?_⟩
  · have hadd := F.distance_iterate_add s.1 hj hjstate
    change j + k ≤ F.distance s.1
    omega
  · rw [add_comm j k, Function.iterate_add_apply, hjstate, hiterate]

/-- In particular, a child lens's occurrence owner remains provenance at its
parent merger. -/
theorem ownerStart_mem_parent_origins {L K : F.ReconvergenceLens}
    (hparent : L.parent = some K) :
    L.ownerStart ∈ F.origins K.mergerState.1 :=
  origins_subset_of_parent hparent (ownerStart_mem_origins L)

/-- The finite occurrence region of a lens consists of the starts whose
first-stop intervals have already reconverged at its merger state. -/
def originRegion (L : F.ReconvergenceLens) : Finset ↥F.starts :=
  F.origins L.mergerState.1

/-- The start occurrence introduced at a merger belongs to its region. -/
theorem mergerStart_mem_originRegion (L : F.ReconvergenceLens) :
    (⟨L.mergerState.1.1, L.mergerState.2.1⟩ : ↥F.starts) ∈ L.originRegion := by
  apply (F.mem_origins_iff L.mergerState.1 _).2
  exact ⟨0, Nat.zero_le _, by simp⟩

/-- A parent's own merger start cannot already occur in a child region.  The
two resulting positive first-stop distance decompositions would contradict
each other. -/
theorem mergerStart_not_mem_originRegion_of_parent
    {L K : F.ReconvergenceLens} (hparent : L.parent = some K) :
    (⟨K.mergerState.1.1, K.mergerState.2.1⟩ : ↥F.starts) ∉ L.originRegion := by
  intro hmem
  rcases (F.mem_origins_iff L.mergerState.1 _).1 hmem with
    ⟨j, hj, hKL⟩
  rcases onSharedSuffix_of_parent hparent with ⟨k, hkpos, hkle, hLK⟩
  rw [L.rank_eq] at hkle
  have hforward := F.distance_iterate_add L.mergerState.1.1 hkle hLK
  have hback := F.distance_iterate_add K.mergerState.1.1 hj hKL
  omega

/-- Parent passage strictly enlarges the finite occurrence region. -/
theorem originRegion_ssubset_of_parent {L K : F.ReconvergenceLens}
    (hparent : L.parent = some K) : L.originRegion ⊂ K.originRegion := by
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨origins_subset_of_parent hparent, ?_⟩
  intro heq
  exact mergerStart_not_mem_originRegion_of_parent hparent
    (heq ▸ mergerStart_mem_originRegion K)

/-- A lens is a root exactly when no later lens occurrence lies on its shared
first-stop suffix. -/
theorem parent_eq_none_iff_no_later_lens (L : F.ReconvergenceLens) :
    L.parent = none ↔ ¬∃ K : F.ReconvergenceLens, L.OnSharedSuffix K := by
  rw [parent_eq_none_iff]
  constructor
  · intro hnext ⟨K, k, hkpos, hkle, hk⟩
    exact hnext ⟨k, hkpos, hkle, K.mergerState, hk⟩
  · intro hlater ⟨k, hkpos, hkle, M, hM⟩
    apply hlater
    let K := ofSlot (F.mergerSlotMergerStateEquiv.symm M)
    refine ⟨K, k, hkpos, hkle, ?_⟩
    change ((F.f : X → X)^[k]) L.mergerState.1.1 =
      (F.mergerSlotMergerStateEquiv
        (F.mergerSlotMergerStateEquiv.symm M)).1.1
    rw [F.mergerSlotMergerStateEquiv.apply_symm_apply]
    exact hM

/-- Origins that meet at one shared state continue to the same first marked
state. -/
theorem terminalState_eq_of_mem_origins {x : F.State} {s t : ↥F.starts}
    (hs : s ∈ F.origins x) (ht : t ∈ F.origins x) :
    F.terminalState s = F.terminalState t := by
  rcases (F.mem_origins_iff x s).mp hs with ⟨j, hj, hjs⟩
  rcases (F.mem_origins_iff x t).mp ht with ⟨k, hk, hkt⟩
  have hsj := F.distance_iterate_add s.1 hj hjs
  have htk := F.distance_iterate_add t.1 hk hkt
  apply Subtype.ext
  change ((F.f : X → X)^[F.distance s.1]) s.1 =
    ((F.f : X → X)^[F.distance t.1]) t.1
  rw [← hsj, ← htk, Function.iterate_add_apply,
    Function.iterate_add_apply, hjs, hkt]

/-- The reached marked state on the shared suffix of a lens. -/
def reachedStop (L : F.ReconvergenceLens) : F.State :=
  F.terminalState L.ownerStart

theorem reachedStop_mem (L : F.ReconvergenceLens) :
    L.reachedStop ∈ F.reachedStops :=
  F.terminalState_mem_reachedStops L.ownerStart

/-- Following the shared suffix from the merger for its rank reaches the
lens's common first-stop terminal. -/
theorem iterate_rank_mergerState_eq_reachedStop (L : F.ReconvergenceLens) :
    ((F.f : X → X)^[L.rank]) L.mergerState.1.1 = L.reachedStop.1 := by
  rw [L.rank_eq]
  rcases (F.mem_origins_iff L.mergerState.1 L.ownerStart).1
      (ownerStart_mem_origins L) with ⟨j, hj, hstate⟩
  have hadd := F.distance_iterate_add L.ownerStart.1 hj hstate
  change ((F.f : X → X)^[F.distance L.mergerState.1.1])
      L.mergerState.1.1 =
    ((F.f : X → X)^[F.distance L.ownerStart.1]) L.ownerStart.1
  rw [← hadd, Function.iterate_add_apply, hstate]

/-- Every occurrence in a lens region has the lens's common first-stop
terminal. -/
theorem terminalState_eq_reachedStop_of_mem_originRegion
    (L : F.ReconvergenceLens) {s : ↥F.starts} (hs : s ∈ L.originRegion) :
    F.terminalState s = L.reachedStop :=
  terminalState_eq_of_mem_origins hs (ownerStart_mem_origins L)

/-- Child and parent lenses lie on one suffix and therefore reach the same
marked state. -/
theorem reachedStop_eq_of_parent {L K : F.ReconvergenceLens}
    (hparent : L.parent = some K) : L.reachedStop = K.reachedStop :=
  terminalState_eq_of_mem_origins
    (ownerStart_mem_parent_origins hparent) (ownerStart_mem_origins K)

/-- Rank decrease is the termination theorem for parent recursion. -/
theorem parentWellFounded (F : MarkedCycleFirstStop X) :
    WellFounded (fun K L : F.ReconvergenceLens => L.parent = some K) := by
  exact Subrelation.wf
    (r := InvImage (· < ·) rank)
    (q := fun K L : F.ReconvergenceLens => L.parent = some K)
    (fun hparent => rank_parent hparent)
    (InvImage.wf rank (Nat.lt_wfRel).2)

/-- The exact geometric statement not present in `MarkedCycleFirstStop`: a
later development must supply concrete collision occurrences and regions,
smallest-lens membership, laminarity, parent containment, and the outer-boundary
characterization of roots. -/
def GeometricLensObligation
    (Occurrence Region : Type*)
    (belongs : Occurrence → F.ReconvergenceLens → Prop)
    (region : F.ReconvergenceLens → Region)
    (Disjoint StrictlyContains : Region → Region → Prop)
    (reachesOuterBoundary : F.ReconvergenceLens → Prop) : Prop :=
  (∀ o, ∃ L, belongs o L ∧
      ∀ K, belongs o K → L = K ∨ StrictlyContains (region K) (region L)) ∧
  (∀ L K, L = K ∨ Disjoint (region L) (region K) ∨
      StrictlyContains (region L) (region K) ∨
      StrictlyContains (region K) (region L)) ∧
  (∀ L K, L.parent = some K → StrictlyContains (region K) (region L)) ∧
  (∀ L, L.parent = none ↔ reachesOuterBoundary L)

end ReconvergenceLens

/-! Kernel regression checks for the finite occurrence labels used by this
generic layer. -/

example : (0 : Fin 4) + 1 = 1 := by decide

example : (3 : Fin 4) + 1 = 0 := by decide

end

end MarkedCycleFirstStop

end GridGraphs
