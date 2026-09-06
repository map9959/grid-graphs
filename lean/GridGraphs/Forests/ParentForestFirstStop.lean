import GridGraphs.Forests.PlaneChannelForest

/-!
# Parent forests stopped at the first marked vertex

This module restricts a finite parent forest to the vertices reached by following
parent edges from a demand set, with no edge leaving a vertex satisfying a stop
predicate.  Reachability is a property of ambient vertices, so parent chains
which merge use the same vertex in the restricted forest.
-/

namespace GridGraphs

open Finset

namespace ParentForest

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A parent step which does not leave a stopped vertex. -/
def stoppedStep (F : ParentForest V) (stop : V → Prop) (v w : V) : Prop :=
  ¬stop v ∧ F.parent v = some w

/-- Ambient vertices reached from a demand without stepping past a stop. -/
def Used (F : ParentForest V) (demand : Finset V) (stop : V → Prop) (v : V) : Prop :=
  ∃ d ∈ demand, Relation.ReflTransGen (F.stoppedStep stop) d v

/-- The shared state space of all stopped parent chains from the demands. -/
def StoppedState (F : ParentForest V) (demand : Finset V) (stop : V → Prop) :=
  {v : V // F.Used demand stop v}

instance stoppedStateFintype
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop) :
    Fintype (F.StoppedState demand stop) := by
  exact Fintype.ofInjective (fun v : F.StoppedState demand stop => v.1)
    Subtype.val_injective

omit [Fintype V] [DecidableEq V] in
/-- A used non-stop vertex with a parent has a used parent. -/
theorem used_parent (F : ParentForest V) {demand : Finset V} {stop : V → Prop}
    {v w : V} (hv : F.Used demand stop v) (hstop : ¬stop v)
    (hparent : F.parent v = some w) :
    F.Used demand stop w := by
  rcases hv with ⟨d, hd, path⟩
  exact ⟨d, hd, path.tail ⟨hstop, hparent⟩⟩

/-- The original parent map, cut precisely at stopped vertices. -/
noncomputable def restrictedParent
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop) :
    F.StoppedState demand stop → Option (F.StoppedState demand stop) := fun v =>
  if hstop : stop v.1 then none
  else
    match hparent : F.parent v.1 with
    | none => none
    | some w => some ⟨w, F.used_parent v.2 hstop hparent⟩

omit [Fintype V] [DecidableEq V] in
theorem restrictedParent_eq_some
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop)
    (v w : F.StoppedState demand stop) :
    F.restrictedParent demand stop v = some w ↔
      ¬stop v.1 ∧ F.parent v.1 = some w.1 := by
  classical
  unfold restrictedParent
  split
  · simp_all
  · rename_i hstop
    split
    · rename_i hparent
      simp [hstop, hparent]
    · rename_i x hparent
      constructor
      · intro h
        have hxw : (⟨x, F.used_parent v.2 hstop hparent⟩ :
            F.StoppedState demand stop) = w := Option.some.inj h
        exact ⟨hstop,
          hparent.trans (congrArg Option.some (congrArg Subtype.val hxw))⟩
      · rintro ⟨_, h⟩
        have hxw : x = w.1 := Option.some.inj (hparent.symm.trans h)
        exact congrArg Option.some (Subtype.ext hxw)

omit [Fintype V] [DecidableEq V] in
theorem restrictedParent_eq_none
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop)
    (v : F.StoppedState demand stop) :
    F.restrictedParent demand stop v = none ↔
      stop v.1 ∨ F.parent v.1 = none := by
  classical
  unfold restrictedParent
  split
  · simp_all
  · rename_i hstop
    simp only [hstop, false_or]
    split <;> simp_all

/-- The parent forest induced on stopped reachable states. -/
noncomputable def firstStopForest
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop) :
    ParentForest (F.StoppedState demand stop) where
  parent := F.restrictedParent demand stop
  rank v := F.rank v.1
  rank_parent := by
    intro v w h
    exact F.rank_parent ((F.restrictedParent_eq_some demand stop v w).mp h).2

/-- Restricted states corresponding to original demands. -/
noncomputable def restrictedDemand
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop) :
    Finset (F.StoppedState demand stop) :=
  Finset.univ.filter fun v => v.1 ∈ demand

/-- Reached vertices at which traversal stopped. -/
noncomputable def exits
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop) :
    Finset (F.StoppedState demand stop) :=
  Finset.univ.filter fun v => stop v.1

omit [DecidableEq V] in
theorem exits_subset_roots
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop) :
    F.exits demand stop ⊆ (F.firstStopForest demand stop).roots := by
  classical
  intro v hv
  have hstop : stop v.1 := (Finset.mem_filter.mp hv).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change F.restrictedParent demand stop v = none
  exact (F.restrictedParent_eq_none demand stop v).mpr (Or.inl hstop)

omit [DecidableEq V] in
/-- There are no artificial roots: roots are exactly stops or inherited roots. -/
theorem mem_firstStopRoots
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop)
    (v : F.StoppedState demand stop) :
    v ∈ (F.firstStopForest demand stop).roots ↔
      stop v.1 ∨ v.1 ∈ F.roots := by
  classical
  unfold ParentForest.roots
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact F.restrictedParent_eq_none demand stop v

/-- Original demand leaves remain leaves after restriction. -/
theorem restrictedDemand_subset_leaves
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop)
    (hleaf : demand ⊆ F.leaves) :
    F.restrictedDemand demand stop ⊆ (F.firstStopForest demand stop).leaves := by
  classical
  intro v hv
  have hvd : v.1 ∈ demand := (Finset.mem_filter.mp hv).2
  have hvleaf := hleaf hvd
  have hchildren : F.children v.1 = ∅ := by
    apply Finset.card_eq_zero.mp
    exact (Finset.mem_filter.mp hvleaf).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hrestricted :
      (F.firstStopForest demand stop).parent w = some v :=
    (Finset.mem_filter.mp hw).2
  have hambient : F.parent w.1 = some v.1 :=
    ((F.restrictedParent_eq_some demand stop w v).mp hrestricted).2
  have hwchild : w.1 ∈ F.children v.1 := by
    simp [ParentForest.children, hambient]
  simp [hchildren] at hwchild

/-- Canonical embedding of original demands into the shared restricted states. -/
noncomputable def demandEmbedding
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop) :
    ↥demand ↪ ↥(F.restrictedDemand demand stop) where
  toFun d :=
    ⟨⟨d.1, ⟨d.1, d.2, Relation.ReflTransGen.refl⟩⟩, by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d.2⟩⟩
  inj' := by
    intro d e h
    exact Subtype.ext (congrArg (fun x => x.1.1) h)

/-- Package the first-stop restriction as an abstract channel forest. -/
noncomputable def firstStopPlaneChannelForest
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop)
    (hleaf : demand ⊆ F.leaves) :
    PlaneChannelForest (F.StoppedState demand stop) where
  forest := F.firstStopForest demand stop
  demand := F.restrictedDemand demand stop
  exits := F.exits demand stop
  demand_leaf_or_exit := by
    intro v hv
    exact Finset.mem_union_left _ (F.restrictedDemand_subset_leaves demand stop hleaf hv)

theorem firstStopPlaneChannelForest_demand_subset_leaves
    (F : ParentForest V) (demand : Finset V) (stop : V → Prop)
    (hleaf : demand ⊆ F.leaves) :
    (F.firstStopPlaneChannelForest demand stop hleaf).demand ⊆
      (F.firstStopPlaneChannelForest demand stop hleaf).forest.leaves :=
  F.restrictedDemand_subset_leaves demand stop hleaf

end

end ParentForest

end GridGraphs
