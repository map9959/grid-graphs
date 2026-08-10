import GridGraphs.MarkedCycleFirstStop
import GridGraphs.GridExpandedContour
import GridGraphs.CanonicalShoreContinuation
import GridGraphs.PerimeterWaste

/-!
# Canonical demands on the expanded contour

Canonical shore demands are launched in distinct expanded compass slots.  They
follow the single expanded contour cycle until first reaching an outer cotree
port.  The generic marked-cycle construction then gives private demand leaves
and reached outer ports as the exact roots.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace CanonicalExpandedContourForest

variable {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
  {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
  (hT : IsSpanningSubtree (gridGraph n n) T)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The expanded slot at which a canonical demand starts.  Direct demands use
their missing outward slot; all others use their retained inward dart. -/
def startSlot (q : CanonicalShoreDemand axis n) : GridCompassSlot n n :=
  if hq : q ∈ CanonicalShoreDemand.directExits axis hn2 T then
    GridExpandedContour.outerPortSlot
      (CanonicalShoreDemand.directExitOuterPort axis hn2 T ⟨q, hq⟩)
  else
    GridExpandedContour.slotOfDart
      (GridDirectionalDart.retainedCanonicalInwardDart axis hn2 hT
        ⟨q, Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hq⟩⟩)

theorem startSlot_not_occupied_of_mem_directExits
    (q : CanonicalShoreDemand axis n)
    (hq : q ∈ CanonicalShoreDemand.directExits axis hn2 T) :
    ¬GridExpandedContour.Occupied (T := T) (startSlot axis hn2 hT q) := by
  rw [startSlot, dif_pos hq]
  exact GridExpandedContour.outerPortSlot_not_occupied _

theorem startSlot_occupied_of_not_mem_directExits
    (q : CanonicalShoreDemand axis n)
    (hq : q ∉ CanonicalShoreDemand.directExits axis hn2 T) :
    GridExpandedContour.Occupied (T := T) (startSlot axis hn2 hT q) := by
  rw [startSlot, dif_neg hq]
  exact GridExpandedContour.occupied_slotOfDart _

/-- Canonical demands occupy distinct expanded slots.  In the mixed cases,
direct slots are unoccupied while continued slots are occupied. -/
theorem startSlot_injective (hn3 : 3 ≤ n) :
    Function.Injective (startSlot axis hn2 hT) := by
  intro a b hab
  by_cases ha : a ∈ CanonicalShoreDemand.directExits axis hn2 T <;>
    by_cases hb : b ∈ CanonicalShoreDemand.directExits axis hn2 T
  · have hp :
        CanonicalShoreDemand.directExitOuterPort axis hn2 T ⟨a, ha⟩ =
          CanonicalShoreDemand.directExitOuterPort axis hn2 T ⟨b, hb⟩ := by
      apply GridExpandedContour.outerPortSlot_injective
      simpa [startSlot, ha, hb] using hab
    exact congrArg Subtype.val
      ((CanonicalShoreDemand.directExitEmbedding axis hn2 T).injective hp)
  · exact False.elim ((startSlot_not_occupied_of_mem_directExits axis hn2 hT a ha)
      (hab ▸ startSlot_occupied_of_not_mem_directExits axis hn2 hT b hb))
  · exact False.elim ((startSlot_not_occupied_of_mem_directExits axis hn2 hT b hb)
      (hab.symm ▸ startSlot_occupied_of_not_mem_directExits axis hn2 hT a ha))
  · let qa : CanonicalShoreDemand.Unsupported axis hn2 T :=
      ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩
    let qb : CanonicalShoreDemand.Unsupported axis hn2 T :=
      ⟨b, Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hb⟩⟩
    have hdart :
        GridDirectionalDart.retainedCanonicalInwardDart axis hn2 hT qa =
          GridDirectionalDart.retainedCanonicalInwardDart axis hn2 hT qb := by
      apply GridExpandedContour.slotOfDart_injective
      simpa [startSlot, ha, hb, qa, qb] using hab
    apply CanonicalShoreDemand.inwardEdgeSym2_injective axis hn2 hn3
    rw [← GridDirectionalDart.retainedCanonicalInwardDart_edgeSym2 axis hn2 hT qa,
      ← GridDirectionalDart.retainedCanonicalInwardDart_edgeSym2 axis hn2 hT qb,
      hdart]

/-- Expanded slots corresponding to all split outer cotree ports. -/
def markedSlots : Finset (GridCompassSlot n n) :=
  Finset.univ.image (GridExpandedContour.outerPortSlot (T := T))

/-- Expanded slots corresponding to all canonical starts. -/
def startSlots : Finset (GridCompassSlot n n) :=
  Finset.univ.image (startSlot axis hn2 hT)

/-- An omitted perimeter edge supplies a supported boundary vertex and hence an
outer cotree port. -/
theorem outerPort_nonempty (hn2 : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    Nonempty (GridCotreeOuterPort T) := by
  obtain ⟨u, v, huv, hnot⟩ := exists_omitted_perimeter_edge hn2 hT
  have hu : u ∈ supportFinset (gridGraph n n \ T) := by
    rw [mem_supportFinset]
    exact Finset.card_pos.mpr ⟨v, by simpa using And.intro huv.1 hnot⟩
  rcases huv.2.1 with htop | hbottom | hleft | hright
  · exact ⟨Sum.inl ⟨u, Finset.mem_filter.mpr ⟨hu, htop⟩⟩⟩
  · exact ⟨Sum.inr (Sum.inl ⟨u, Finset.mem_filter.mpr ⟨hu, hbottom⟩⟩)⟩
  · exact ⟨Sum.inr (Sum.inr (Sum.inl
      ⟨u, Finset.mem_filter.mpr ⟨hu, hleft⟩⟩))⟩
  · exact ⟨Sum.inr (Sum.inr (Sum.inr
      ⟨u, Finset.mem_filter.mpr ⟨hu, hright⟩⟩))⟩

theorem markedSlots_nonempty (hn2 : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    (markedSlots (T := T)).Nonempty := by
  let p := Classical.choice (outerPort_nonempty hn2 hT)
  exact ⟨GridExpandedContour.outerPortSlot p, Finset.mem_image.mpr
    ⟨p, Finset.mem_univ p, rfl⟩⟩

/-- Every expanded slot eventually reaches an outer-port mark, because the
expanded contour of the spanning tree is one cycle. -/
theorem eventually_marked (hn2 : 2 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (s : GridCompassSlot n n) :
    ∃ k, ((GridExpandedContour.equiv (T := T) :
      GridCompassSlot n n → GridCompassSlot n n)^[k]) s ∈ markedSlots (T := T) := by
  let p := Classical.choice (outerPort_nonempty hn2 hT)
  have hcycle := GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
    hn2 hT s (GridExpandedContour.outerPortSlot p)
  obtain ⟨k, -, hk⟩ := hcycle.exists_pow_eq'
  refine ⟨k, ?_⟩
  change (GridExpandedContour.equiv (T := T) ^ k) s ∈ markedSlots (T := T)
  rw [hk]
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩

/-- The marked expanded-contour first-stop data. -/
def firstStop : MarkedCycleFirstStop (GridCompassSlot n n) where
  f := GridExpandedContour.equiv (T := T)
  stop := markedSlots (T := T)
  starts := startSlots axis hn2 hT
  stop_nonempty := markedSlots_nonempty hn2 hT
  eventually_stop := eventually_marked hn2 hT

/-- All canonical demands embed into the private demand leaves. -/
def demandEmbedding :
    CanonicalShoreDemand axis n ↪
      ↥(firstStop axis hn2 hT).demands := by
  let startEmbedding : CanonicalShoreDemand axis n ↪
      ↥(startSlots axis hn2 hT) :=
    { toFun := fun q => ⟨startSlot axis hn2 hT q, Finset.mem_image.mpr
        ⟨q, Finset.mem_univ q, rfl⟩⟩
      inj' := fun _ _ h => startSlot_injective axis hn2 hT hn3
        (congrArg Subtype.val h) }
  exact startEmbedding.trans (firstStop axis hn2 hT).demandEmbedding

/-- Recover the unique outer port represented by a marked expanded slot. -/
def outerPortOfMarkedSlot
    (s : ↥(markedSlots (T := T))) : GridCotreeOuterPort T :=
  (Finset.mem_image.mp s.2).choose

@[simp] theorem outerPortSlot_outerPortOfMarkedSlot
    (s : ↥(markedSlots (T := T))) :
    GridExpandedContour.outerPortSlot (outerPortOfMarkedSlot (T := T) s) = s.1 := by
  exact (Finset.mem_image.mp s.2).choose_spec.2

theorem outerPortOfMarkedSlot_injective :
    Function.Injective (outerPortOfMarkedSlot (T := T)) := by
  intro a b hab
  apply Subtype.ext
  rw [← outerPortSlot_outerPortOfMarkedSlot (T := T) a,
    ← outerPortSlot_outerPortOfMarkedSlot (T := T) b, hab]

/-- The shared reached state represented by an exit of the first-stop forest. -/
def exitState (e : ↥(firstStop axis hn2 hT).exits) :
    (firstStop axis hn2 hT).State :=
  (Finset.mem_map.mp e.2).choose

theorem exitState_mem_markedSlots
    (e : ↥(firstStop axis hn2 hT).exits) :
    (exitState axis hn2 hT e).1 ∈ markedSlots (T := T) := by
  exact (Finset.mem_filter.mp (Finset.mem_map.mp e.2).choose_spec.1).2

@[simp] theorem exit_value_eq
    (e : ↥(firstStop axis hn2 hT).exits) :
    e.1 = Sum.inr (exitState axis hn2 hT e) :=
  (Finset.mem_map.mp e.2).choose_spec.2.symm

/-- Each reached marked exit recovers its unique split outer cotree port. -/
def exitEmbedding :
    ↥(firstStop axis hn2 hT).exits ↪ GridCotreeOuterPort T where
  toFun e := outerPortOfMarkedSlot (T := T)
    ⟨(exitState axis hn2 hT e).1, exitState_mem_markedSlots axis hn2 hT e⟩
  inj' := by
    intro a b hab
    have hs : exitState axis hn2 hT a = exitState axis hn2 hT b := by
      have hslots : (exitState axis hn2 hT a).1 =
          (exitState axis hn2 hT b).1 :=
        congrArg (fun s : ↥(markedSlots (T := T)) => s.1)
          (outerPortOfMarkedSlot_injective (T := T) hab)
      exact Subtype.ext hslots
    apply Subtype.ext
    rw [exit_value_eq axis hn2 hT a, exit_value_eq axis hn2 hT b, hs]

/-- The canonical expanded-contour channel forest. -/
def planeChannelForest :
    PlaneChannelForest (firstStop axis hn2 hT).Carrier :=
  (firstStop axis hn2 hT).planeChannelForest

theorem demands_subset_leaves :
    (planeChannelForest axis hn2 hT).demand ⊆
      (planeChannelForest axis hn2 hT).forest.leaves :=
  (firstStop axis hn2 hT).demands_subset_leaves

theorem exits_eq_roots :
    (planeChannelForest axis hn2 hT).exits =
      (planeChannelForest axis hn2 hT).forest.roots :=
  (firstStop axis hn2 hT).exits_eq_roots

end

end CanonicalExpandedContourForest

end GridGraphs
