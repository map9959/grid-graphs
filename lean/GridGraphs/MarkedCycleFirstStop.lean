import GridGraphs.PlaneChannelForest

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

/-- Successor on shared states, cut at the first marked state. -/
def stateParent (F : MarkedCycleFirstStop X) (x : F.State) : Option F.State :=
  if hx : x.1 ∈ F.stop then none else some ⟨F.f x.1, used_f F x.2 hx⟩

@[simp] theorem stateParent_eq_none_iff (F : MarkedCycleFirstStop X) (x : F.State) :
    F.stateParent x = none ↔ x.1 ∈ F.stop := by
  unfold stateParent
  split <;> simp_all

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
def Carrier (F : MarkedCycleFirstStop X) := (↥F.starts) ⊕ F.State

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
            exact (F.sharedForest.rank_parent hstate)

/-- Private start leaves, used as channel demands. -/
def demands (F : MarkedCycleFirstStop X) : Finset F.Carrier :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

/-- Reached marked states, used as channel exits. -/
def exits (F : MarkedCycleFirstStop X) : Finset F.Carrier :=
  (Finset.univ.filter fun x : F.State => x.1 ∈ F.stop).map
    ⟨Sum.inr, Sum.inr_injective⟩

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
  simp only [ParentForest.leaves, Finset.mem_filter, Finset.mem_univ, true_and,
    ParentForest.childCount, ParentForest.children]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hparent : F.forest.parent w = some (Sum.inl s) := (Finset.mem_filter.mp hw).2
  cases w <;> simp [forest, parent] at hparent

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
    simp only [forest, parent, stateParent, y, hnstop, ↓reduceDIte, Option.map_some,
      Option.some.injEq]
    congr 1
    exact Subtype.ext hvalue

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
  cases v with
  | inl s => simp [ParentForest.roots, forest, parent]
  | inr x =>
      simp only [ParentForest.roots, Finset.mem_filter, Finset.mem_univ, true_and,
        forest, parent, Option.map_eq_none_iff, stateParent_eq_none_iff]
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

/-- Marked starts give distinct reached marked exits, even if other starts later
join their stopped suffixes. -/
def markedStartExitEmbedding (F : MarkedCycleFirstStop X) :
    ↥(F.starts ∩ F.stop) ↪ ↥F.exits where
  toFun s :=
    ⟨Sum.inr (F.stateOfStart ⟨s.1, (Finset.mem_inter.mp s.2).1⟩), by
      apply Finset.mem_map.mpr
      refine ⟨F.stateOfStart ⟨s.1, (Finset.mem_inter.mp s.2).1⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, stateOfStart]
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
