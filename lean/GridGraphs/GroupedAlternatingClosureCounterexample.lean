import GridGraphs.PhysicalFirstSeparatorNeighborhood

/-!
# Grouped alternating-closure counterexample

The parent-forest Euler identity, injective root ports, and pointwise existence
of merger continuations do not imply Hall.  Two distinct merger slots can still
expose the same physical continuation resource.
-/

namespace GridGraphs

open Finset

namespace ParentForest

/-- A root with three leaf children.  It has one root and two merger-excess
slots. -/
def threeLeafStarForest : ParentForest (Fin 4) where
  parent v := if v.1 = 3 then none else some 3
  rank v := if v.1 = 3 then 0 else 1
  rank_parent := by
    intro v w hparent
    by_cases hv : v.1 = 3
    · simp [hv] at hparent
    · have hparent' : some (3 : Fin 4) = some w := by simpa [hv] using hparent
      have hw : w = 3 := (Option.some.inj hparent').symm
      subst w
      simp [hv]

/-- The unique root port. -/
def threeLeafStarRootPort :
    ↥threeLeafStarForest.roots → Unit := fun _ => ()

abbrev ThreeLeafStarGroupedSource :=
  ↥(threeLeafStarForest.usedRootPorts threeLeafStarRootPort) ⊕
    threeLeafStarForest.MergerSlot

/-- The root sees resource `0`; both merger slots see resource `1`.  Resource
`2` exists but is outside both merger neighborhoods. -/
def threeLeafStarGroupedNeighborhood :
    ThreeLeafStarGroupedSource → Finset (Fin 3)
  | .inl _ => {0}
  | .inr _ => {1}

theorem threeLeafStarForest_card_leaves :
    threeLeafStarForest.leaves.card = 3 := by native_decide

theorem threeLeafStarForest_card_roots :
    threeLeafStarForest.roots.card = 1 := by native_decide

theorem threeLeafStarForest_branchExcess :
    threeLeafStarForest.branchExcess = 2 := by native_decide

theorem threeLeafStarRootPort_injective :
    Function.Injective threeLeafStarRootPort := by
  intro a b _
  have hcard : Fintype.card ↥threeLeafStarForest.roots ≤ 1 := by
    rw [Fintype.card_coe, threeLeafStarForest_card_roots]
  exact (Fintype.card_le_one_iff_subsingleton.mp hcard).elim a b

/-- This is exactly the proposed grouped Euler balance in the example. -/
theorem threeLeafStar_groupedEuler :
    threeLeafStarForest.leaves.card =
      (threeLeafStarForest.usedRootPorts threeLeafStarRootPort).card +
        threeLeafStarForest.branchExcess := by
  exact threeLeafStarForest.card_leaves_eq_usedRootPorts_add_debt_add_branchExcess
    threeLeafStarRootPort |>.trans (by
      rw [(threeLeafStarForest.rootPortDebt_eq_zero_iff_injective
        threeLeafStarRootPort).2 threeLeafStarRootPort_injective]
      omega)

/-- Every grouped source, in particular every merger slot, has a continuation
resource. -/
theorem threeLeafStarGroupedNeighborhood_nonempty
    (source : ThreeLeafStarGroupedSource) :
    (threeLeafStarGroupedNeighborhood source).Nonempty := by
  rcases source with source | source <;>
    simp [threeLeafStarGroupedNeighborhood]

/-- The two distinct merger slots have the same singleton physical
neighborhood. -/
theorem threeLeafStar_sameResourceMergerCollision
    (a b : threeLeafStarForest.MergerSlot) :
    threeLeafStarGroupedNeighborhood (.inr a) =
      threeLeafStarGroupedNeighborhood (.inr b) := rfl

/-- Pointwise continuation and exact total Euler balance still do not imply
Hall: the merger-slot subfamily has cardinality two and neighborhood cardinality
one. -/
theorem threeLeafStar_not_localizedHall :
    ¬LocalizedHall threeLeafStarGroupedNeighborhood := by
  intro hHall
  let mergers : Finset ThreeLeafStarGroupedSource :=
    Finset.univ.map Function.Embedding.inr
  have h := hHall mergers
  have hslotCard : Fintype.card threeLeafStarForest.MergerSlot = 2 := by
    rw [threeLeafStarForest.card_mergerSlot,
      threeLeafStarForest_branchExcess]
  have hmerger : Nonempty threeLeafStarForest.MergerSlot :=
    Fintype.card_pos_iff.mp (by omega)
  have hcard : mergers.card = 2 := by
    simp [mergers, hslotCard]
  have hunion : mergers.biUnion threeLeafStarGroupedNeighborhood = {1} := by
    ext resource
    constructor
    · simp [mergers, threeLeafStarGroupedNeighborhood]
    · intro hresource
      have : resource = 1 := by simpa using hresource
      subst resource
      obtain ⟨slot⟩ := hmerger
      exact Finset.mem_biUnion.mpr ⟨.inr slot, by simp [mergers], by
        simp [threeLeafStarGroupedNeighborhood]⟩
  rw [hcard, hunion] at h
  simp at h

/-- Combined no-go statement for the generic tree-exchange proposal. -/
theorem groupedEuler_injectiveRoots_pointwiseContinuation_not_sufficient :
    Function.Injective threeLeafStarRootPort ∧
      threeLeafStarForest.leaves.card =
        (threeLeafStarForest.usedRootPorts threeLeafStarRootPort).card +
          threeLeafStarForest.branchExcess ∧
      (∀ source : ThreeLeafStarGroupedSource,
        (threeLeafStarGroupedNeighborhood source).Nonempty) ∧
      ¬LocalizedHall threeLeafStarGroupedNeighborhood :=
  ⟨threeLeafStarRootPort_injective, threeLeafStar_groupedEuler,
    threeLeafStarGroupedNeighborhood_nonempty, threeLeafStar_not_localizedHall⟩

end ParentForest

end GridGraphs
