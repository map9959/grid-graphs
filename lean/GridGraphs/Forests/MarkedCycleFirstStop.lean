import GridGraphs.Forests.PlaneChannelForest
import Mathlib.Data.Finset.Max

/-!
# First-stop forests for marked permutations

A finite collection of starts follows a permutation until it first reaches a
marked state.  Reached states are shared, so starts whose forward orbits merge
share the same suffix.  A private leaf is added for each start before packaging
the construction as a `PlaneChannelForest`.
-/

namespace GridGraphs

open Finset

/-- Data needed for the generic first-stop construction.  The direct
eventual-stop hypothesis avoids coupling the API to a particular cycle lemma. -/
structure MarkedCycleFirstStop (X : Type*) [Fintype X] [DecidableEq X] where
  f : X ≃ X
  stop : Finset X
  starts : Finset X
  stop_nonempty : stop.Nonempty
  eventually_stop : ∀ x, ∃ k, ((f : X → X)^[k]) x ∈ stop

namespace MarkedCycleFirstStop

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Least forward distance from `x` to a marked state. -/
def distance (F : MarkedCycleFirstStop X) (x : X) : Nat :=
  Nat.find (F.eventually_stop x)

/-- The state at the first-stop distance is marked. -/
theorem distance_spec (F : MarkedCycleFirstStop X) (x : X) :
    ((F.f : X → X)^[F.distance x]) x ∈ F.stop :=
  Nat.find_spec (F.eventually_stop x)

/-- No earlier forward iterate is marked. -/
theorem not_mem_stop_of_lt_distance (F : MarkedCycleFirstStop X) (x : X)
    {k : Nat} (hk : k < F.distance x) :
    ((F.f : X → X)^[k]) x ∉ F.stop := by
  intro hstop
  exact (Nat.not_lt_of_ge (Nat.find_min' (F.eventually_stop x) hstop)) hk

/-- The first-stop distance is no larger than any marked iterate. -/
theorem distance_minimal (F : MarkedCycleFirstStop X) (x : X) {k : Nat}
    (hk : ((F.f : X → X)^[k]) x ∈ F.stop) : F.distance x ≤ k :=
  Nat.find_min' (F.eventually_stop x) hk

@[simp] theorem distance_eq_zero_iff (F : MarkedCycleFirstStop X) (x : X) :
    F.distance x = 0 ↔ x ∈ F.stop := by
  constructor
  · intro h
    simpa [h] using F.distance_spec x
  · intro hx
    exact Nat.le_zero.mp (F.distance_minimal x (k := 0) (by simpa using hx))

/-- Moving forward from a nonmarked state removes exactly one step. -/
theorem distance_succ (F : MarkedCycleFirstStop X) {x : X}
    (hx : x ∉ F.stop) : F.distance (F.f x) + 1 = F.distance x := by
  have hpos : 0 < F.distance x := Nat.pos_of_ne_zero fun h =>
    hx ((F.distance_eq_zero_iff x).mp h)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hforward : ((F.f : X → X)^[n]) (F.f x) ∈ F.stop := by
    rw [← Function.iterate_succ_apply]
    simpa [hn] using F.distance_spec x
  have hle : F.distance (F.f x) ≤ n := F.distance_minimal (F.f x) hforward
  have hge : F.distance x ≤ F.distance (F.f x) + 1 := by
    apply F.distance_minimal x
    rw [Function.iterate_succ_apply]
    exact F.distance_spec (F.f x)
  omega

/-- First-stop distance strictly decreases at every nonmarked state. -/
theorem distance_f_lt (F : MarkedCycleFirstStop X) {x : X}
    (hx : x ∉ F.stop) : F.distance (F.f x) < F.distance x := by
  rw [← F.distance_succ hx]
  exact Nat.lt_succ_self _

/-- A state is used when it occurs no later than the first mark on the orbit of
some start.  This property identifies merged suffixes by their ambient state. -/
def Used (F : MarkedCycleFirstStop X) (x : X) : Prop :=
  ∃ s ∈ F.starts, ∃ k ≤ F.distance s, ((F.f : X → X)^[k]) s = x

/-- Shared ambient states reached from the starts up to their first marks. -/
def State (F : MarkedCycleFirstStop X) := {x : X // F.Used x}

instance stateFintype (F : MarkedCycleFirstStop X) : Fintype F.State :=
  Fintype.ofInjective (fun x : F.State => x.1) Subtype.val_injective

theorem used_f (F : MarkedCycleFirstStop X) {x : X} (hused : F.Used x)
    (hx : x ∉ F.stop) : F.Used (F.f x) := by
  rcases hused with ⟨s, hs, k, hk, rfl⟩
  refine ⟨s, hs, k + 1, ?_, ?_⟩
  · have hkne : k ≠ F.distance s := by
      intro h
      apply hx
      simpa [h] using F.distance_spec s
    omega
  · rw [Function.iterate_succ_apply']

/-- A start viewed as its shared reached state. -/
def stateOfStart (F : MarkedCycleFirstStop X) (s : ↥F.starts) : F.State :=
  ⟨s.1, s.1, s.2, 0, Nat.zero_le _, by simp⟩

/-- Starts whose orbit reaches `x` no later than its first marked state. -/
def origins (F : MarkedCycleFirstStop X) (x : F.State) : Finset ↥F.starts :=
  Finset.univ.filter fun s =>
    ∃ k ≤ F.distance s.1, ((F.f : X → X)^[k]) s.1 = x.1

@[simp] theorem mem_origins_iff (F : MarkedCycleFirstStop X) (x : F.State)
    (s : ↥F.starts) :
    s ∈ F.origins x ↔
      ∃ k ≤ F.distance s.1, ((F.f : X → X)^[k]) s.1 = x.1 := by
  simp [origins]

/-- Every used state retains at least one originating start. -/
theorem origins_nonempty (F : MarkedCycleFirstStop X) (x : F.State) :
    (F.origins x).Nonempty := by
  rcases x.2 with ⟨s, hs, k, hk, hsk⟩
  exact ⟨⟨s, hs⟩, (F.mem_origins_iff x ⟨s, hs⟩).2 ⟨k, hk, hsk⟩⟩

/-- The first marked state reached from a start. -/
def terminalState (F : MarkedCycleFirstStop X) (s : ↥F.starts) : F.State :=
  ⟨((F.f : X → X)^[F.distance s.1]) s.1,
    s.1, s.2, F.distance s.1, Nat.le_refl _, rfl⟩

theorem terminalState_mem_stop (F : MarkedCycleFirstStop X) (s : ↥F.starts) :
    (F.terminalState s).1 ∈ F.stop :=
  F.distance_spec s.1

theorem terminalState_mem_origins (F : MarkedCycleFirstStop X) (s : ↥F.starts) :
    s ∈ F.origins (F.terminalState s) :=
  (F.mem_origins_iff (F.terminalState s) s).2
    ⟨F.distance s.1, Nat.le_refl _, rfl⟩

/-- The reached marked states, equivalently the shared states underlying exits
and roots. -/
def reachedStops (F : MarkedCycleFirstStop X) : Finset F.State :=
  Finset.univ.filter fun x => x.1 ∈ F.stop

@[simp] theorem mem_reachedStops_iff (F : MarkedCycleFirstStop X) (x : F.State) :
    x ∈ F.reachedStops ↔ x.1 ∈ F.stop := by
  simp [reachedStops]

theorem terminalState_mem_reachedStops (F : MarkedCycleFirstStop X)
    (s : ↥F.starts) : F.terminalState s ∈ F.reachedStops :=
  (F.mem_reachedStops_iff _).2 (F.terminalState_mem_stop s)

/-- Along a first-stop interval, elapsed steps and remaining distance add to
the original start distance. -/
theorem distance_iterate_add (F : MarkedCycleFirstStop X) (s : X)
    {k : Nat} {x : X} (hk : k ≤ F.distance s)
    (hiterate : ((F.f : X → X)^[k]) s = x) :
    F.distance x + k = F.distance s := by
  induction k generalizing s with
  | zero =>
      subst x
      simp
  | succ k ih =>
      have hsnot : s ∉ F.stop := by
        simpa using F.not_mem_stop_of_lt_distance s (k := 0) (by omega)
      have hstep := F.distance_succ hsnot
      have hk' : k ≤ F.distance (F.f s) := by omega
      have hiterate' : ((F.f : X → X)^[k]) (F.f s) = x := by
        rw [Function.iterate_succ_apply'] at hiterate
        rw [← ((Function.Commute.refl (F.f : X → X)).iterate_right k).eq]
        exact hiterate
      have := ih (s := F.f s) hk' hiterate'
      omega

/-- At a reached mark, provenance is exactly the fiber of `terminalState`. -/
theorem mem_origins_of_mem_stop_iff (F : MarkedCycleFirstStop X)
    (x : F.State) (hx : x.1 ∈ F.stop) (s : ↥F.starts) :
    s ∈ F.origins x ↔ F.terminalState s = x := by
  constructor
  · intro hs
    rcases (F.mem_origins_iff x s).1 hs with ⟨k, hk, hiterate⟩
    have hadd := F.distance_iterate_add s.1 hk hiterate
    have hxzero := (F.distance_eq_zero_iff x.1).2 hx
    have hkdist : k = F.distance s.1 := by omega
    apply Subtype.ext
    simpa [terminalState, hkdist] using hiterate
  · intro h
    rw [← h]
    exact F.terminalState_mem_origins s

/-- Distinct reached marks have disjoint sets of originating starts. -/
theorem disjoint_origins_of_mem_stop (F : MarkedCycleFirstStop X)
    {x y : F.State} (hx : x.1 ∈ F.stop) (hy : y.1 ∈ F.stop) (hxy : x ≠ y) :
    Disjoint (F.origins x) (F.origins y) := by
  rw [Finset.disjoint_left]
  intro s hsx hsy
  apply hxy
  exact ((F.mem_origins_of_mem_stop_iff x hx s).1 hsx).symm.trans
    ((F.mem_origins_of_mem_stop_iff y hy s).1 hsy)

/-- Exit-origin sets partition all starts. -/
theorem biUnion_origins_reachedStops (F : MarkedCycleFirstStop X) :
    F.reachedStops.biUnion F.origins = Finset.univ := by
  ext s
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  exact ⟨F.terminalState s, F.terminalState_mem_reachedStops s,
    F.terminalState_mem_origins s⟩

/-- Weighted partition of starts by their reached marked state. -/
theorem sum_origins_reachedStops (F : MarkedCycleFirstStop X)
    (w : ↥F.starts → Nat) :
    ∑ x ∈ F.reachedStops, ∑ s ∈ F.origins x, w s = ∑ s, w s := by
  rw [← F.biUnion_origins_reachedStops, Finset.sum_biUnion]
  intro x hx y hy hxy
  exact F.disjoint_origins_of_mem_stop
    ((F.mem_reachedStops_iff x).1 hx) ((F.mem_reachedStops_iff y).1 hy) hxy

/-- Cardinality form of the terminal-state partition. -/
theorem sum_card_origins_reachedStops (F : MarkedCycleFirstStop X) :
    ∑ x ∈ F.reachedStops, (F.origins x).card = F.starts.card := by
  simpa using F.sum_origins_reachedStops (fun _ => 1)

/-- On one shared state, first-stop distance distinguishes its originating
starts. -/
theorem distance_injective_on_origins (F : MarkedCycleFirstStop X)
    (x : F.State) {s t : ↥F.starts} (hs : s ∈ F.origins x)
    (ht : t ∈ F.origins x) (hdist : F.distance s.1 = F.distance t.1) :
    s = t := by
  rcases (F.mem_origins_iff x s).mp hs with ⟨k, hk, hsk⟩
  rcases (F.mem_origins_iff x t).mp ht with ⟨l, hl, htl⟩
  have hsd := F.distance_iterate_add s.1 hk hsk
  have htd := F.distance_iterate_add t.1 hl htl
  have hkl : k = l := by omega
  subst l
  apply Subtype.ext
  exact (Function.Injective.iterate F.f.injective k) (hsk.trans htl.symm)

/-- The unique origin farthest from a shared state, i.e. the earliest start in
that first-stop interval. -/
noncomputable def earliestOriginStart (F : MarkedCycleFirstStop X)
    (x : F.State) : ↥F.starts :=
  Classical.choose (Finset.exists_max_image (F.origins x)
    (fun s : ↥F.starts => F.distance s.1) (F.origins_nonempty x))

theorem earliestOriginStart_mem (F : MarkedCycleFirstStop X) (x : F.State) :
    F.earliestOriginStart x ∈ F.origins x :=
  (Classical.choose_spec (Finset.exists_max_image (F.origins x)
    (fun s : ↥F.starts => F.distance s.1) (F.origins_nonempty x))).1

theorem distance_le_earliestOriginStart (F : MarkedCycleFirstStop X)
    (x : F.State) {s : ↥F.starts} (hs : s ∈ F.origins x) :
    F.distance s.1 ≤ F.distance (F.earliestOriginStart x).1 :=
  (Classical.choose_spec (Finset.exists_max_image (F.origins x)
    (fun s : ↥F.starts => F.distance s.1) (F.origins_nonempty x))).2 s hs

theorem eq_earliestOriginStart_of_maximal (F : MarkedCycleFirstStop X)
    (x : F.State) {s : ↥F.starts} (hs : s ∈ F.origins x)
    (hmax : ∀ t ∈ F.origins x, F.distance t.1 ≤ F.distance s.1) :
    s = F.earliestOriginStart x := by
  apply F.distance_injective_on_origins x hs (F.earliestOriginStart_mem x)
  exact Nat.le_antisymm (F.distance_le_earliestOriginStart x hs)
    (hmax _ (F.earliestOriginStart_mem x))

/-- Successor on shared states, cut at the first marked state. -/
def stateParent (F : MarkedCycleFirstStop X) (x : F.State) : Option F.State :=
  if hx : x.1 ∈ F.stop then none else some ⟨F.f x.1, used_f F x.2 hx⟩

@[simp] theorem stateParent_eq_none_iff (F : MarkedCycleFirstStop X) (x : F.State) :
    F.stateParent x = none ↔ x.1 ∈ F.stop := by
  unfold stateParent
  split <;> simp_all

/-- Origins can only accumulate while moving along a shared orbit suffix. -/
theorem origins_mono_stateParent (F : MarkedCycleFirstStop X) {x y : F.State}
    (hparent : F.stateParent x = some y) : F.origins x ⊆ F.origins y := by
  unfold stateParent at hparent
  split at hparent
  · simp at hparent
  · rename_i hx
    have hy : y.1 = F.f x.1 :=
      congrArg Subtype.val (Option.some.inj hparent.symm)
    intro s hs
    rcases (F.mem_origins_iff x s).1 hs with ⟨k, hk, hsk⟩
    apply (F.mem_origins_iff y s).2
    refine ⟨k + 1, ?_, ?_⟩
    · have hkne : k ≠ F.distance s.1 := by
        intro h
        apply hx
        rw [← hsk]
        simpa [h] using F.distance_spec s.1
      omega
    · rw [Function.iterate_succ_apply']
      rw [hsk, ← hy]

/-- On entering a state that is itself a start, its origins are exactly the
predecessor origins together with that start. -/
theorem origins_stateParent_eq_insert (F : MarkedCycleFirstStop X)
    {x y : F.State} (hparent : F.stateParent x = some y)
    (hyStart : y.1 ∈ F.starts) :
    F.origins y = insert (⟨y.1, hyStart⟩ : ↥F.starts) (F.origins x) := by
  have hy : y.1 = F.f x.1 := by
    unfold stateParent at hparent
    split at hparent
    · simp at hparent
    · exact congrArg Subtype.val (Option.some.inj hparent.symm)
  apply Finset.Subset.antisymm
  · intro s hs
    rcases (F.mem_origins_iff y s).1 hs with ⟨k, hk, hsk⟩
    by_cases hsy : s.1 = y.1
    · simp only [Finset.mem_insert]
      left
      apply Subtype.ext
      exact hsy
    · have hkpos : 0 < k := by
        apply Nat.pos_of_ne_zero
        intro hkzero
        apply hsy
        simpa [hkzero] using hsk
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
      have hpre : ((F.f : X → X)^[n]) s.1 = x.1 := by
        apply F.f.injective
        rw [Function.iterate_succ_apply'] at hsk
        rw [hsk, ← hy]
      simp only [Finset.mem_insert]
      exact Or.inr ((F.mem_origins_iff x s).2 ⟨n, by omega, hpre⟩)
  · intro s hs
    simp only [Finset.mem_insert] at hs
    rcases hs with hsy | hs
    · subst s
      exact (F.mem_origins_iff y ⟨y.1, hyStart⟩).2 ⟨0, Nat.zero_le _, by simp⟩
    · exact F.origins_mono_stateParent hparent hs

/-- The ranked forest on shared reached states, before private start leaves are
added. -/
def sharedForest (F : MarkedCycleFirstStop X) : ParentForest F.State where
  parent := F.stateParent
  rank x := F.distance x.1
  rank_parent := by
    intro x y hxy
    unfold stateParent at hxy
    split at hxy
    · simp at hxy
    · rename_i hx
      have hy : y.1 = F.f x.1 := congrArg Subtype.val (Option.some.inj hxy.symm)
      simpa [hy] using F.distance_f_lt hx

/-- Carrier with one private leaf for every start. -/
abbrev Carrier (F : MarkedCycleFirstStop X) := (↥F.starts) ⊕ F.State

instance carrierFintype (F : MarkedCycleFirstStop X) : Fintype F.Carrier := by
  unfold Carrier
  infer_instance

/-- Parent map after attaching each private start leaf. -/
def parent (F : MarkedCycleFirstStop X) : F.Carrier → Option F.Carrier
  | .inl s => some (.inr (F.stateOfStart s))
  | .inr x => (F.stateParent x).map Sum.inr

/-- Ranked parent forest with private start leaves and shared orbit suffixes. -/
def forest (F : MarkedCycleFirstStop X) : ParentForest F.Carrier where
  parent := F.parent
  rank
    | .inl s => F.distance s.1 + 1
    | .inr x => F.distance x.1
  rank_parent := by
    intro x y hxy
    cases x with
    | inl s =>
        simp only [parent, Option.some.injEq] at hxy
        subst y
        exact Nat.lt_succ_self _
    | inr x =>
        cases hstate : F.stateParent x with
        | none => simp [parent, hstate] at hxy
         | some z =>
             simp [parent, hstate] at hxy
             subst y
             exact F.sharedForest.rank_parent hstate

/-- Shared-state children of `x`, before accounting for its private start
child.  This finset has at most one element because `f` is a permutation. -/
def statePredecessors (F : MarkedCycleFirstStop X) (x : F.State) : Finset F.State :=
  Finset.univ.filter fun y => F.stateParent y = some x

theorem stateParent_injective_of_eq_some (F : MarkedCycleFirstStop X)
    {x y z : F.State} (hx : F.stateParent x = some z)
    (hy : F.stateParent y = some z) : x = y := by
  have hxval : F.f x.1 = z.1 := by
    unfold stateParent at hx
    split at hx
    · simp at hx
    · exact (congrArg Subtype.val (Option.some.inj hx.symm)).symm
  have hyval : F.f y.1 = z.1 := by
    unfold stateParent at hy
    split at hy
    · simp at hy
    · exact (congrArg Subtype.val (Option.some.inj hy.symm)).symm
  exact Subtype.ext (F.f.injective (hxval.trans hyval.symm))

theorem card_statePredecessors_le_one (F : MarkedCycleFirstStop X) (x : F.State) :
    (F.statePredecessors x).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro y hy z hz
  exact F.stateParent_injective_of_eq_some
    (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2

/-- Children of a shared state split into its optional private start child and
its (at most one) shared predecessor. -/
theorem children_inr_eq (F : MarkedCycleFirstStop X) (x : F.State) :
    F.forest.children (Sum.inr x) =
      (if hx : x.1 ∈ F.starts then
        {Sum.inl (⟨x.1, hx⟩ : ↥F.starts)}
      else ∅) ∪
        (F.statePredecessors x).map ⟨Sum.inr, Sum.inr_injective⟩ := by
  ext w
  simp only [ParentForest.children, Finset.mem_filter, Finset.mem_univ, true_and]
  cases w with
  | inl s =>
      simp only [forest, parent, Option.some.injEq, Finset.mem_union, Finset.mem_map]
      by_cases hx : x.1 ∈ F.starts
      · rw [dif_pos hx]
        simp only [Finset.mem_singleton]
        constructor
        · intro h
          left
          congr 1
          exact Subtype.ext (congrArg (fun z : F.State => z.1) (Sum.inr.inj h))
        · rintro (h | ⟨y, -, h⟩)
          · have hs : s = ⟨x.1, hx⟩ := Sum.inl.inj h
            subst s
            rfl
          · cases h
      · rw [dif_neg hx]
        simp only [Finset.notMem_empty, false_or]
        constructor
        · intro h
          apply (hx ?_).elim
          have hsx : s.1 = x.1 :=
            congrArg (fun z : F.State => z.1) (Sum.inr.inj h)
          simp [← hsx]
        · rintro ⟨y, -, h⟩
          cases h
  | inr y =>
      simp only [Finset.mem_union, Finset.mem_map, statePredecessors,
        Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [forest, parent]
      constructor
      · intro h
        right
        have hparent : F.stateParent y = some x := by
          cases hy : F.stateParent y with
          | none => simp [hy] at h
          | some z =>
              have hmapped := h
              rw [hy] at hmapped
              have hcarrier : (Sum.inr z : F.Carrier) = Sum.inr x :=
                Option.some.inj hmapped
              have hzx : z = x := Sum.inr.inj hcarrier
              simp [hzx]
        exact ⟨y, hparent, rfl⟩
      · rintro (h | ⟨z, hz, hzx⟩)
        · split at h <;> simp_all
        · have hzy : z = y := Sum.inr.inj hzx
          have hy : F.stateParent y = some x := by simpa [hzy] using hz
          simp [hy]

@[simp] theorem children_inl_eq_empty (F : MarkedCycleFirstStop X)
    (s : ↥F.starts) : F.forest.children (Sum.inl s) = ∅ := by
  ext w
  simp only [ParentForest.children, Finset.mem_filter, Finset.mem_univ, true_and]
  cases w <;> simp [forest, parent]

/-- A shared state is a merger precisely when it is itself a start and has a
used shared predecessor. -/
def IsMergerState (F : MarkedCycleFirstStop X) (x : F.State) : Prop :=
  x.1 ∈ F.starts ∧ (F.statePredecessors x).Nonempty

theorem childCount_inr_eq_two_iff (F : MarkedCycleFirstStop X) (x : F.State) :
    F.forest.childCount (Sum.inr x) = 2 ↔ F.IsMergerState x := by
  rw [ParentForest.childCount, F.children_inr_eq]
  have hdisjoint : Disjoint
      (if hx : x.1 ∈ F.starts then
        {Sum.inl (⟨x.1, hx⟩ : ↥F.starts)}
      else ∅)
      ((F.statePredecessors x).map ⟨Sum.inr, Sum.inr_injective⟩) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp hb
    split at ha <;> simp_all
  rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_map]
  have hle := F.card_statePredecessors_le_one x
  by_cases hx : x.1 ∈ F.starts
  · rw [dif_pos hx, Finset.card_singleton]
    simp only [IsMergerState, hx, true_and]
    rw [← Finset.card_pos]
    omega
  · rw [dif_neg hx, Finset.card_empty, zero_add]
    simp only [IsMergerState, hx, false_and]
    constructor
    · intro h
      omega
    · intro h
      contradiction

theorem childCount_le_two (F : MarkedCycleFirstStop X) (v : F.Carrier) :
    F.forest.childCount v ≤ 2 := by
  cases v with
  | inl s => simp [ParentForest.childCount]
  | inr x =>
      rw [ParentForest.childCount, F.children_inr_eq]
      have hdisjoint : Disjoint
          (if hx : x.1 ∈ F.starts then
            {Sum.inl (⟨x.1, hx⟩ : ↥F.starts)}
          else ∅)
          ((F.statePredecessors x).map ⟨Sum.inr, Sum.inr_injective⟩) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp hb
        split at ha <;> simp_all
      rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_map]
      have hle := F.card_statePredecessors_le_one x
      split
      · simp only [Finset.card_singleton]
        omega
      · simp only [Finset.card_empty, zero_add]
        omega

theorem mem_mergers_iff_isMergerState (F : MarkedCycleFirstStop X)
    (v : F.Carrier) :
    v ∈ F.forest.mergers ↔
      ∃ x : F.State, F.IsMergerState x ∧ v = Sum.inr x := by
  cases v with
  | inl s => simp [ParentForest.mem_mergers, ParentForest.childCount]
  | inr x =>
      rw [ParentForest.mem_mergers]
      have hle := F.childCount_le_two (Sum.inr x)
      have hrhs :
          (∃ y : F.State, F.IsMergerState y ∧
            (Sum.inr x : F.Carrier) = Sum.inr y) ↔
            F.IsMergerState x := by
        constructor
        · rintro ⟨y, hy, hxy⟩
          simpa [Sum.inr.inj hxy] using hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [hrhs]
      constructor
      · intro h
        exact (F.childCount_inr_eq_two_iff x).mp (Nat.le_antisymm hle h)
      · intro h
        rw [(F.childCount_inr_eq_two_iff x).mpr h]

/-- Every merger in a first-stop forest is binary. -/
theorem childCount_eq_two_of_mem_mergers (F : MarkedCycleFirstStop X)
    {v : F.Carrier} (hv : v ∈ F.forest.mergers) :
    F.forest.childCount v = 2 :=
  Nat.le_antisymm (F.childCount_le_two v) ((F.forest.mem_mergers v).mp hv)

/-- Shared states satisfying the exact local merger condition. -/
def MergerState (F : MarkedCycleFirstStop X) := {x : F.State // F.IsMergerState x}

theorem mergerSlot_mem_mergers (F : MarkedCycleFirstStop X)
    (s : F.forest.MergerSlot) : s.1 ∈ F.forest.mergers := by
  apply (F.forest.mergerExcessAt_pos_iff s.1).mp
  exact Nat.pos_of_ne_zero fun hzero => by
    have : IsEmpty (Fin (F.forest.mergerExcessAt s.1)) := by
      rw [hzero]
      infer_instance
    exact isEmptyElim s.2

/-- Binary mergers have exactly one excess slot, so slots are canonically the
merger vertices themselves. -/
noncomputable def mergerSlotMergerEquiv (F : MarkedCycleFirstStop X) :
    F.forest.MergerSlot ≃ ↥F.forest.mergers :=
  Equiv.ofBijective
    (fun s => ⟨s.1, F.mergerSlot_mem_mergers s⟩)
    ⟨by
      intro a b hab
      have hv : a.1 = b.1 := congrArg Subtype.val hab
      cases a with
      | mk av ai =>
          cases b with
          | mk bv bi =>
              dsimp at hv
              subst bv
              congr 1
              apply Fin.eq_of_val_eq
              have hai := ai.isLt
              have hbi := bi.isLt
              have hcount := F.childCount_eq_two_of_mem_mergers
                (F.mergerSlot_mem_mergers ⟨av, ai⟩)
              simp [ParentForest.mergerExcessAt, hcount] at hai hbi
              omega,
    by
      intro v
      have hpos : 0 < F.forest.mergerExcessAt v.1 :=
        (F.forest.mergerExcessAt_pos_iff v.1).mpr v.2
      exact ⟨⟨v.1, ⟨0, hpos⟩⟩, Subtype.ext rfl⟩⟩

/-- A merger vertex in this forest has a unique underlying shared state. -/
noncomputable def mergerVertexState (F : MarkedCycleFirstStop X)
    (v : ↥F.forest.mergers) : F.MergerState := by
  let h := (F.mem_mergers_iff_isMergerState v.1).mp v.2
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem mergerVertexState_spec (F : MarkedCycleFirstStop X)
    (v : ↥F.forest.mergers) :
    v.1 = Sum.inr (F.mergerVertexState v).1 := by
  exact (Classical.choose_spec
    ((F.mem_mergers_iff_isMergerState v.1).mp v.2)).2

/-- Canonical identification of concrete merger slots with the shared states
at which the binary mergers occur. -/
noncomputable def mergerSlotMergerStateEquiv (F : MarkedCycleFirstStop X) :
    F.forest.MergerSlot ≃ F.MergerState :=
  Equiv.ofBijective
    (fun s => F.mergerVertexState (F.mergerSlotMergerEquiv s))
    ⟨by
      intro a b hab
      apply F.mergerSlotMergerEquiv.injective
      apply Subtype.ext
      rw [F.mergerVertexState_spec, F.mergerVertexState_spec]
      exact congrArg (fun x : F.State => (Sum.inr x : F.Carrier))
        (congrArg Subtype.val hab),
    by
      intro x
      let v : ↥F.forest.mergers :=
        ⟨Sum.inr x.1, (F.mem_mergers_iff_isMergerState _).mpr ⟨x.1, x.2, rfl⟩⟩
      let s := F.mergerSlotMergerEquiv.symm v
      refine ⟨s, ?_⟩
      have hv := F.mergerVertexState_spec v
      have hs : F.mergerSlotMergerEquiv s = v := F.mergerSlotMergerEquiv.apply_symm_apply v
      change F.mergerVertexState (F.mergerSlotMergerEquiv s) = x
      rw [hs]
      apply Subtype.ext
      exact (Sum.inr.inj hv).symm⟩

/-- The unique used predecessor branch entering a merger state. -/
noncomputable def mergerPredecessor (F : MarkedCycleFirstStop X)
    (m : F.MergerState) : F.State :=
  Classical.choose m.2.2

theorem mergerPredecessor_mem (F : MarkedCycleFirstStop X)
    (m : F.MergerState) :
    F.mergerPredecessor m ∈ F.statePredecessors m.1 :=
  Classical.choose_spec m.2.2

theorem stateParent_mergerPredecessor (F : MarkedCycleFirstStop X)
    (m : F.MergerState) :
    F.stateParent (F.mergerPredecessor m) = some m.1 :=
  (Finset.mem_filter.mp (F.mergerPredecessor_mem m)).2

/-- The exact binary local picture: one private child for the merger's own
start and one used shared predecessor. -/
theorem children_mergerState_eq (F : MarkedCycleFirstStop X)
    (m : F.MergerState) :
    F.forest.children (Sum.inr m.1) =
      {Sum.inl (⟨m.1.1, m.2.1⟩ : ↥F.starts),
        Sum.inr (F.mergerPredecessor m)} := by
  rw [F.children_inr_eq, dif_pos m.2.1]
  have hpred : F.statePredecessors m.1 = {F.mergerPredecessor m} := by
    apply Finset.Subset.antisymm
    · intro z hz
      simp only [Finset.mem_singleton]
      exact F.stateParent_injective_of_eq_some
        (Finset.mem_filter.mp hz).2 (F.stateParent_mergerPredecessor m)
    · simp [F.mergerPredecessor_mem m]
  ext w
  simp [hpred]

theorem not_mem_stop_of_stateParent (F : MarkedCycleFirstStop X)
    {x y : F.State} (hparent : F.stateParent x = some y) : x.1 ∉ F.stop := by
  unfold stateParent at hparent
  split at hparent
  · simp at hparent
  · assumption

theorem f_eq_of_stateParent (F : MarkedCycleFirstStop X)
    {x y : F.State} (hparent : F.stateParent x = some y) : F.f x.1 = y.1 := by
  unfold stateParent at hparent
  split at hparent
  · simp at hparent
  · exact (congrArg Subtype.val (Option.some.inj hparent.symm)).symm

theorem earliestOriginStart_not_mem_stop_of_parent_marked
    (F : MarkedCycleFirstStop X) {x y : F.State}
    (hparent : F.stateParent y = some x) (_hx : x.1 ∈ F.stop) :
    (F.earliestOriginStart y).1 ∉ F.stop := by
  have hynot := F.not_mem_stop_of_stateParent hparent
  rcases (F.mem_origins_iff y (F.earliestOriginStart y)).mp
      (F.earliestOriginStart_mem y) with ⟨k, hk, hiterate⟩
  have hadd := F.distance_iterate_add _ hk hiterate
  have hypos : 0 < F.distance y.1 := by
    exact Nat.pos_of_ne_zero fun hzero =>
      hynot ((F.distance_eq_zero_iff y.1).mp hzero)
  intro hstop
  have hzero := (F.distance_eq_zero_iff (F.earliestOriginStart y).1).mpr hstop
  omega

/-- Orbit-local owner of a merger.  An unmarked merger owns its direct start;
a marked endpoint merger owns the earliest unmarked predecessor start in the
same first-stop interval. -/
noncomputable def mergerOwner (F : MarkedCycleFirstStop X)
    (m : F.MergerState) : ↥(F.starts \ F.stop) :=
  if hm : m.1.1 ∈ F.stop then
    let s := F.earliestOriginStart (F.mergerPredecessor m)
    ⟨s.1, Finset.mem_sdiff.mpr ⟨s.2,
      F.earliestOriginStart_not_mem_stop_of_parent_marked
        (F.stateParent_mergerPredecessor m) hm⟩⟩
  else
    ⟨m.1.1, Finset.mem_sdiff.mpr ⟨m.2.1, hm⟩⟩

theorem mergerOwner_eq_self_of_not_mem_stop (F : MarkedCycleFirstStop X)
    (m : F.MergerState) (hm : m.1.1 ∉ F.stop) :
    (F.mergerOwner m).1 = m.1.1 := by
  simp [mergerOwner, hm]

theorem mergerOwner_eq_earliest_of_mem_stop (F : MarkedCycleFirstStop X)
    (m : F.MergerState) (hm : m.1.1 ∈ F.stop) :
    (F.mergerOwner m).1 =
      (F.earliestOriginStart (F.mergerPredecessor m)).1 := by
  simp [mergerOwner, hm]

/-- Exact local relation for a marked owner: it lies in the predecessor
interval, is maximal by first-stop distance, and ends at the merger mark. -/
theorem marked_mergerOwner_relation (F : MarkedCycleFirstStop X)
    (m : F.MergerState) (hm : m.1.1 ∈ F.stop) :
    let y := F.mergerPredecessor m
    let s : ↥F.starts := ⟨(F.mergerOwner m).1,
      (Finset.mem_sdiff.mp (F.mergerOwner m).2).1⟩
    s ∈ F.origins y ∧
      (∀ t ∈ F.origins y, F.distance t.1 ≤ F.distance s.1) ∧
      ((F.f : X → X)^[F.distance s.1]) s.1 = m.1.1 := by
  dsimp
  have howner := F.mergerOwner_eq_earliest_of_mem_stop m hm
  let e := F.earliestOriginStart (F.mergerPredecessor m)
  have hs : (⟨(F.mergerOwner m).1,
      (Finset.mem_sdiff.mp (F.mergerOwner m).2).1⟩ : ↥F.starts) = e := by
    apply Subtype.ext
    exact howner
  refine ⟨by simpa [hs] using F.earliestOriginStart_mem (F.mergerPredecessor m), ?_, ?_⟩
  · intro t ht
    simpa [howner] using F.distance_le_earliestOriginStart
      (F.mergerPredecessor m) ht
  rcases (F.mem_origins_iff _ e).mp (F.earliestOriginStart_mem _) with
    ⟨k, hk, hiterate⟩
  have hparent := F.stateParent_mergerPredecessor m
  have hynot := F.not_mem_stop_of_stateParent hparent
  have hdisty := F.distance_succ hynot
  have hdistx : F.distance m.1.1 = 0 := (F.distance_eq_zero_iff m.1.1).mpr hm
  rw [F.f_eq_of_stateParent hparent] at hdisty
  have hdistyone : F.distance (F.mergerPredecessor m).1 = 1 := by omega
  have hdecomp := F.distance_iterate_add e.1 hk hiterate
  have hkdist : F.distance e.1 = k + 1 := by omega
  rw [howner]
  rw [hkdist, Function.iterate_succ_apply']
  rw [hiterate, F.f_eq_of_stateParent hparent]

/-- The owner, viewed without its proof of being unmarked. -/
noncomputable def mergerOwnerStart (F : MarkedCycleFirstStop X)
    (m : F.MergerState) : ↥F.starts :=
  ⟨(F.mergerOwner m).1, (Finset.mem_sdiff.mp (F.mergerOwner m).2).1⟩

theorem marked_mergerOwner_endpoint (F : MarkedCycleFirstStop X)
    (m : F.MergerState) (hm : m.1.1 ∈ F.stop) :
    ((F.f : X → X)^[F.distance (F.mergerOwnerStart m).1])
      (F.mergerOwnerStart m).1 = m.1.1 := by
  exact (F.marked_mergerOwner_relation m hm).2.2

/-- An earliest origin cannot itself be a merger: its used predecessor would
give a strictly farther origin in the same interval. -/
theorem earliestOriginStart_not_isMergerState (F : MarkedCycleFirstStop X)
    (y : F.State) :
    ¬F.IsMergerState (F.stateOfStart (F.earliestOriginStart y)) := by
  intro hmerge
  let m : F.MergerState := ⟨F.stateOfStart (F.earliestOriginStart y), hmerge⟩
  let z := F.mergerPredecessor m
  let e := F.earliestOriginStart y
  let t := F.earliestOriginStart z
  have hzy : F.stateParent z = some (F.stateOfStart e) :=
    F.stateParent_mergerPredecessor m
  have hznot := F.not_mem_stop_of_stateParent hzy
  have hfz : F.f z.1 = e.1 := by
    exact F.f_eq_of_stateParent hzy
  have hdistz := F.distance_succ hznot
  rw [hfz] at hdistz
  rcases (F.mem_origins_iff y e).mp (F.earliestOriginStart_mem y) with
    ⟨k, hk, he⟩
  rcases (F.mem_origins_iff z t).mp (F.earliestOriginStart_mem z) with
    ⟨l, hl, ht⟩
  have hde := F.distance_iterate_add e.1 hk he
  have hdt := F.distance_iterate_add t.1 hl ht
  have htOrigin : t ∈ F.origins y := by
    apply (F.mem_origins_iff y t).mpr
    refine ⟨k + 1 + l, ?_, ?_⟩
    · omega
    · rw [Function.iterate_add_apply, ht, Function.iterate_succ_apply, hfz, he]
  have hmax := F.distance_le_earliestOriginStart y htOrigin
  have hstrict : F.distance e.1 < F.distance t.1 := by omega
  have hmax' : F.distance t.1 ≤ F.distance e.1 := by simpa [e] using hmax
  exact (Nat.not_lt_of_ge hmax') hstrict

theorem marked_mergerOwner_not_isMergerState (F : MarkedCycleFirstStop X)
    (m : F.MergerState) (hm : m.1.1 ∈ F.stop) :
    ¬F.IsMergerState (F.stateOfStart (F.mergerOwnerStart m)) := by
  have hearly := F.earliestOriginStart_not_isMergerState
    (F.mergerPredecessor m)
  have howner : F.mergerOwnerStart m =
      F.earliestOriginStart (F.mergerPredecessor m) := by
    apply Subtype.ext
    exact F.mergerOwner_eq_earliest_of_mem_stop m hm
  simpa [howner] using hearly

/-- Orbit-local owners are distinct.  The three cases are direct starts,
distinct marked endpoints, and the mixed earliest-origin obstruction. -/
theorem mergerOwner_injective (F : MarkedCycleFirstStop X) :
    Function.Injective F.mergerOwner := by
  intro a b hab
  by_cases ha : a.1.1 ∈ F.stop
  · by_cases hb : b.1.1 ∈ F.stop
    · have hstart : F.mergerOwnerStart a = F.mergerOwnerStart b := by
        apply Subtype.ext
        exact congrArg (fun s : ↥(F.starts \ F.stop) => s.1) hab
      have hea := F.marked_mergerOwner_endpoint a ha
      have heb := F.marked_mergerOwner_endpoint b hb
      rw [hstart] at hea
      apply Subtype.ext
      apply Subtype.ext
      exact hea.symm.trans heb
    · exfalso
      apply F.marked_mergerOwner_not_isMergerState a ha
      have hstate : F.stateOfStart (F.mergerOwnerStart a) = b.1 := by
        apply Subtype.ext
        change (F.mergerOwner a).1 = b.1.1
        exact (congrArg (fun s : ↥(F.starts \ F.stop) => s.1) hab).trans
          (F.mergerOwner_eq_self_of_not_mem_stop b hb)
      simpa [hstate] using b.2
  · by_cases hb : b.1.1 ∈ F.stop
    · exfalso
      apply F.marked_mergerOwner_not_isMergerState b hb
      have hstate : F.stateOfStart (F.mergerOwnerStart b) = a.1 := by
        apply Subtype.ext
        change (F.mergerOwner b).1 = a.1.1
        exact (congrArg (fun s : ↥(F.starts \ F.stop) => s.1) hab.symm).trans
          (F.mergerOwner_eq_self_of_not_mem_stop a ha)
      simpa [hstate] using a.2
    · apply Subtype.ext
      apply Subtype.ext
      have haval := F.mergerOwner_eq_self_of_not_mem_stop a ha
      have hbval := F.mergerOwner_eq_self_of_not_mem_stop b hb
      exact haval.symm.trans
        ((congrArg (fun s : ↥(F.starts \ F.stop) => s.1) hab).trans hbval)

/-- Canonical orbit-local replacement for the cardinality-chosen embedding.
The existing `mergerSlotUnmarkedStartEmbedding` remains available unchanged. -/
noncomputable def canonicalMergerSlotUnmarkedStartEmbedding
    (F : MarkedCycleFirstStop X) :
    F.forest.MergerSlot ↪ ↥(F.starts \ F.stop) where
  toFun s := F.mergerOwner (F.mergerSlotMergerStateEquiv s)
  inj' := fun _ _ h => F.mergerSlotMergerStateEquiv.injective
    (F.mergerOwner_injective h)

/-- Private start leaves, used as channel demands. -/
def demands (F : MarkedCycleFirstStop X) : Finset F.Carrier :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

/-- Reached marked states, used as channel exits. -/
def exits (F : MarkedCycleFirstStop X) : Finset F.Carrier :=
  (Finset.univ.filter fun x : F.State => x.1 ∈ F.stop).map
    ⟨Sum.inr, Sum.inr_injective⟩

/-- Reached stops are precisely the shared states represented by exits. -/
theorem reachedStops_map_inr_eq_exits (F : MarkedCycleFirstStop X) :
    F.reachedStops.map ⟨Sum.inr, Sum.inr_injective⟩ = F.exits := by
  rfl

/-- Every start embeds as its distinct private demand leaf. -/
def demandEmbedding (F : MarkedCycleFirstStop X) : ↥F.starts ↪ ↥F.demands where
  toFun s := ⟨Sum.inl s, by simp [demands]⟩
  inj' := by
    intro s t h
    exact Sum.inl.inj (congrArg Subtype.val h)

/-- Private demands are leaves even when starts or orbit suffixes coincide. -/
theorem demands_subset_leaves (F : MarkedCycleFirstStop X) :
    F.demands ⊆ F.forest.leaves := by
  intro v hv
  obtain ⟨s, -, rfl⟩ := Finset.mem_map.mp hv
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by simp [ParentForest.childCount]⟩

/-- Every shared physical state has an incoming child in the augmented forest.
If the state is a start, its private demand is a child.  Otherwise a usage
witness has positive iterate index, and its preceding iterate is a used child. -/
theorem state_has_child (F : MarkedCycleFirstStop X) (x : F.State) :
    ∃ w : F.Carrier, F.forest.parent w = some (Sum.inr x) := by
  by_cases hxstart : x.1 ∈ F.starts
  · let s : ↥F.starts := ⟨x.1, hxstart⟩
    refine ⟨Sum.inl s, ?_⟩
    simp only [forest, parent]
    congr 2
  · rcases x.2 with ⟨s, hs, k, hk, hiterate⟩
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hkzero
      apply hxstart
      have hsx : s = x.1 := by simpa [hkzero] using hiterate
      simpa [← hsx] using hs
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
    have hnle : n ≤ F.distance s := by omega
    have hnlt : n < F.distance s := by omega
    have hnstop : ((F.f : X → X)^[n]) s ∉ F.stop :=
      F.not_mem_stop_of_lt_distance s hnlt
    let y : F.State :=
      ⟨((F.f : X → X)^[n]) s, s, hs, n, hnle, rfl⟩
    refine ⟨Sum.inr y, ?_⟩
    have hvalue : F.f y.1 = x.1 := by
      simpa [y, Function.iterate_succ_apply'] using hiterate
    change (F.stateParent y).map Sum.inr = some (Sum.inr x)
    have hy : F.stateParent y = some x := by
      rw [stateParent, dif_neg hnstop]
      exact congrArg some (Subtype.ext hvalue)
    rw [hy]
    rfl

/-- The private demands are exactly all leaves.  In particular, shared stopped
suffixes do not create additional leaves. -/
theorem leaves_eq_demands (F : MarkedCycleFirstStop X) :
    F.forest.leaves = F.demands := by
  apply Finset.Subset.antisymm
  · intro v hv
    cases v with
    | inl s => simp [demands]
    | inr x =>
        obtain ⟨w, hw⟩ := F.state_has_child x
        have hwchild : w ∈ F.forest.children (Sum.inr x) := by
          simp [ParentForest.children, hw]
        have hzero : F.forest.childCount (Sum.inr x) = 0 :=
          (Finset.mem_filter.mp hv).2
        have hempty : F.forest.children (Sum.inr x) = ∅ :=
          Finset.card_eq_zero.mp hzero
        simp [hempty] at hwchild
  · exact F.demands_subset_leaves

@[simp] theorem card_demands (F : MarkedCycleFirstStop X) :
    F.demands.card = F.starts.card := by
  simp [demands]

/-- Roots are exactly the reached marked states; no private or artificial roots
are introduced. -/
theorem mem_roots_iff (F : MarkedCycleFirstStop X) (v : F.Carrier) :
    v ∈ F.forest.roots ↔
      ∃ x : F.State, x.1 ∈ F.stop ∧ v = Sum.inr x := by
  simp only [ParentForest.roots, Finset.mem_filter, Finset.mem_univ, true_and]
  cases v with
  | inl s => simp [forest, parent]
  | inr x =>
      simp only [forest, parent, Option.map_eq_none_iff, stateParent_eq_none_iff]
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hxy⟩
        have h : x = y := Sum.inr.inj hxy
        simpa [h] using hy

theorem exits_subset_roots (F : MarkedCycleFirstStop X) :
    F.exits ⊆ F.forest.roots := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hv
  exact (F.mem_roots_iff _).mpr ⟨x, (Finset.mem_filter.mp hx).2, rfl⟩

/-- In fact every root is one of the designated reached marked exits. -/
theorem exits_eq_roots (F : MarkedCycleFirstStop X) :
    F.exits = F.forest.roots := by
  apply Finset.Subset.antisymm F.exits_subset_roots
  intro v hv
  rcases (F.mem_roots_iff v).mp hv with ⟨x, hx, rfl⟩
  exact Finset.mem_map.mpr ⟨x, by simp [hx], rfl⟩

/-- Reached stops also index exactly the roots of the augmented forest. -/
theorem reachedStops_map_inr_eq_roots (F : MarkedCycleFirstStop X) :
    F.reachedStops.map ⟨Sum.inr, Sum.inr_injective⟩ = F.forest.roots := by
  rw [F.reachedStops_map_inr_eq_exits, F.exits_eq_roots]

/-- Marked starts give distinct reached marked exits, even if other starts later
join their stopped suffixes. -/
def markedStartExitEmbedding (F : MarkedCycleFirstStop X) :
    ↥(F.starts ∩ F.stop) ↪ ↥F.exits where
  toFun s :=
    ⟨Sum.inr (F.stateOfStart ⟨s.1, (Finset.mem_inter.mp s.2).1⟩), by
      apply Finset.mem_map.mpr
      refine ⟨F.stateOfStart ⟨s.1, (Finset.mem_inter.mp s.2).1⟩, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (Finset.mem_inter.mp s.2).2⟩
  inj' := by
    intro s t h
    apply Subtype.ext
    have hstate := Sum.inr.inj (congrArg Subtype.val h)
    exact congrArg (fun z : F.State => z.1) hstate

/-- Exact merger excess: starts supply all leaves and reached marked states are
exactly the roots. -/
theorem branchExcess_eq_card_starts_sub_card_exits (F : MarkedCycleFirstStop X) :
    F.forest.branchExcess = F.starts.card - F.exits.card := by
  have hledger := F.forest.card_leaves_eq_card_roots_add_branchExcess
  rw [F.leaves_eq_demands, F.card_demands, ← F.exits_eq_roots] at hledger
  omega

/-- Exact cardinality of the concrete merger-slot type. -/
theorem card_mergerSlot_eq_card_starts_sub_card_exits
    (F : MarkedCycleFirstStop X) :
    Fintype.card F.forest.MergerSlot = F.starts.card - F.exits.card := by
  rw [F.forest.card_mergerSlot, F.branchExcess_eq_card_starts_sub_card_exits]

/-- Merger excess is bounded by the number of starts not already marked. -/
theorem branchExcess_le_card_starts_sdiff_stop (F : MarkedCycleFirstStop X) :
    F.forest.branchExcess ≤ (F.starts \ F.stop).card := by
  have hmarked : (F.starts ∩ F.stop).card ≤ F.exits.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective F.markedStartExitEmbedding
        F.markedStartExitEmbedding.injective
  have hpartition := Finset.card_sdiff_add_card_inter F.starts F.stop
  rw [F.branchExcess_eq_card_starts_sub_card_exits]
  omega

theorem card_mergerSlot_le_card_starts_sdiff_stop (F : MarkedCycleFirstStop X) :
    Fintype.card F.forest.MergerSlot ≤ (F.starts \ F.stop).card := by
  rw [F.forest.card_mergerSlot]
  exact F.branchExcess_le_card_starts_sdiff_stop

/-- A cardinality-chosen assignment of each merger slot to a distinct unmarked
start.  No canonical orbit representative is claimed. -/
noncomputable def mergerSlotUnmarkedStartEmbedding (F : MarkedCycleFirstStop X) :
    F.forest.MergerSlot ↪ ↥(F.starts \ F.stop) := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_coe] using F.card_mergerSlot_le_card_starts_sdiff_stop

/-- The generic first-stop construction packaged for channel counting. -/
def planeChannelForest (F : MarkedCycleFirstStop X) : PlaneChannelForest F.Carrier where
  forest := F.forest
  demand := F.demands
  exits := F.exits
  demand_leaf_or_exit := fun _ hv =>
    Finset.mem_union_left _ (F.demands_subset_leaves hv)

end

end MarkedCycleFirstStop

end GridGraphs
