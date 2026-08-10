import GridGraphs.ResidueTwoExactRepair

/-!
# A cap-balanced stable residue-two family

At pump depth `t`, this construction inserts the bridge vertices
`(5,13+3j)` and deletes the cap vertices `(1,13+3j)`, for `j<t`.
Only set-theoretic and cardinal properties are established here.
-/

namespace GridGraphs

open Finset

set_option maxHeartbeats 4000000

/-- Bridge coordinate at seam `j`. -/
def residueTwoStableBridgeVertex (t : Nat) (j : Fin t) :
    GridVertex (20 + 3 * t) (20 + 3 * t) :=
  (⟨5, by omega⟩, ⟨13 + 3 * j.val, by have := j.isLt; omega⟩)

/-- Cap coordinate deleted at seam `j`. -/
def residueTwoStableCapVertex (t : Nat) (j : Fin t) :
    GridVertex (20 + 3 * t) (20 + 3 * t) :=
  (⟨1, by omega⟩, ⟨13 + 3 * j.val, by have := j.isLt; omega⟩)

def residueTwoStableBridges (t : Nat) :
    Finset (GridVertex (20 + 3 * t) (20 + 3 * t)) :=
  Finset.univ.image (residueTwoStableBridgeVertex t)

def residueTwoStableCapDeletions (t : Nat) :
    Finset (GridVertex (20 + 3 * t) (20 + 3 * t)) :=
  Finset.univ.image (residueTwoStableCapVertex t)

/-- The bridge and cap coordinates lie on the enlarged board. -/
theorem residueTwoStable_edit_coordinate_bounds (t : Nat) (j : Fin t) :
    5 < 20 + 3 * t ∧ 1 < 20 + 3 * t ∧
      13 + 3 * j.val < 20 + 3 * t := by
  have := j.isLt
  omega

theorem residueTwoStableBridgeVertex_injective (t : Nat) :
    Function.Injective (residueTwoStableBridgeVertex t) := by
  intro i j h
  apply Fin.ext
  have hc := congrArg (fun v => v.2.val) h
  simp only [residueTwoStableBridgeVertex] at hc
  omega

theorem residueTwoStableCapVertex_injective (t : Nat) :
    Function.Injective (residueTwoStableCapVertex t) := by
  intro i j h
  apply Fin.ext
  have hc := congrArg (fun v => v.2.val) h
  simp only [residueTwoStableCapVertex] at hc
  omega

@[simp] theorem residueTwoStableBridges_card (t : Nat) :
    (residueTwoStableBridges t).card = t := by
  classical
  rw [residueTwoStableBridges, card_image_of_injective _
    (residueTwoStableBridgeVertex_injective t), card_univ, Fintype.card_fin]

@[simp] theorem residueTwoStableCapDeletions_card (t : Nat) :
    (residueTwoStableCapDeletions t).card = t := by
  classical
  rw [residueTwoStableCapDeletions, card_image_of_injective _
    (residueTwoStableCapVertex_injective t), card_univ, Fintype.card_fin]

/-- The bridge set is absent from the raw pumped occurrence image. -/
theorem residueTwoStableBridges_disjoint_raw (t : Nat) :
    Disjoint (residueTwoStableBridges t) (residueTwoExactOccurrenceImage t) := by
  simpa only [residueTwoStableBridges, residueTwoStableBridgeVertex,
    residueTwoExactRepairAdded, residueTwoExactRepairAddedVertex] using
      residueTwoExactRepairAdded_disjoint_occurrences t

/-- Every cap deletion is the corresponding copy of the base vertex `(1,13)`. -/
theorem residueTwoStableCapDeletions_subset_raw (t : Nat) :
    residueTwoStableCapDeletions t ⊆ residueTwoExactOccurrenceImage t := by
  classical
  intro v hv
  simp only [residueTwoStableCapDeletions, Finset.mem_image, Finset.mem_univ,
    true_and] at hv
  obtain ⟨j, rfl⟩ := hv
  let copies :
      {p : Fin (residueTwoExactMultiplicity 5 t (⟨1, by omega⟩ : Fin 20)) ×
          Fin (residueTwoExactMultiplicity 11 t (⟨13, by omega⟩ : Fin 20)) //
        IsResidueTwoExactBase ⟨1, by omega⟩ ⟨13, by omega⟩} :=
    ⟨(⟨0, by simp [residueTwoExactMultiplicity]⟩,
      ⟨j.val, by simp [residueTwoExactMultiplicity]; omega⟩), by
        simp [IsResidueTwoExactBase, residueTwoExactBaseRow]⟩
  let x : ResidueTwoExactOccurrence t :=
    ⟨⟨1, by omega⟩, ⟨13, by omega⟩, copies⟩
  refine Finset.mem_image.mpr ⟨x, Finset.mem_univ _, ?_⟩
  apply Prod.ext <;> apply Fin.ext
  · simp [x, copies, residueTwoStableCapVertex,
      residueTwoExactVertex, residueTwoExactExpandIndex]
  · simp [x, copies, residueTwoStableCapVertex,
      residueTwoExactVertex, residueTwoExactExpandIndex]

theorem residueTwoStableBridges_disjoint_capDeletions (t : Nat) :
    Disjoint (residueTwoStableBridges t) (residueTwoStableCapDeletions t) := by
  classical
  rw [Finset.disjoint_left]
  intro v hb hd
  simp only [residueTwoStableBridges, residueTwoStableCapDeletions,
    Finset.mem_image, Finset.mem_univ, true_and] at hb hd
  obtain ⟨i, rfl⟩ := hb
  obtain ⟨j, h⟩ := hd
  have hr := congrArg (fun z => z.1.val) h
  simp [residueTwoStableBridgeVertex, residueTwoStableCapVertex] at hr

/-- Raw exact U, with bridges inserted and the same number of cap vertices removed. -/
def residueTwoStableCapAt (t : Nat) :
    Finset (GridVertex (20 + 3 * t) (20 + 3 * t)) :=
  (residueTwoExactOccurrenceImage t ∪ residueTwoStableBridges t) \
    residueTwoStableCapDeletions t

theorem residueTwoStableCapAt_card (t : Nat) :
    (residueTwoStableCapAt t).card =
      6 * (t + 1) ^ 2 + 65 * (t + 1) + 179 := by
  classical
  have hcap : residueTwoStableCapDeletions t ⊆
      residueTwoExactOccurrenceImage t ∪ residueTwoStableBridges t :=
    (residueTwoStableCapDeletions_subset_raw t).trans Finset.subset_union_left
  rw [residueTwoStableCapAt, card_sdiff,
    Finset.inter_eq_left.mpr hcap, card_union_of_disjoint
      (residueTwoStableBridges_disjoint_raw t).symm,
    residueTwoExactOccurrenceImage_card]
  simp

/-- The cap-balanced family on side `3k+2`, with `t=k-6`. -/
def uResidueTwoStableCap (k : Nat) :
    Finset (GridVertex (3 * k + 2) (3 * k + 2)) :=
  if hk : 6 ≤ k then
    let castVertex : GridVertex (20 + 3 * (k - 6)) (20 + 3 * (k - 6)) →
        GridVertex (3 * k + 2) (3 * k + 2) := fun x =>
      (⟨x.1.val, by have := x.1.isLt; omega⟩,
        ⟨x.2.val, by have := x.2.isLt; omega⟩)
    (residueTwoStableCapAt (k - 6)).image castVertex
  else ∅

theorem uResidueTwoStableCap_card (k : Nat) (hk : 6 ≤ k) :
    (uResidueTwoStableCap k).card = 6 * k ^ 2 + 5 * k + 4 := by
  classical
  simp only [uResidueTwoStableCap, dif_pos hk]
  rw [card_image_of_injective, residueTwoStableCapAt_card]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    simp
    ring
  · intro x y h
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun z => z.1.val) h
    · exact congrArg (fun z => z.2.val) h

/-- The forced-complement score is unchanged by the balanced edits. -/
theorem uResidueTwoStableCap_compl_card (k : Nat) (hk : 6 ≤ k) :
    ((Finset.univ : Finset (GridVertex (3 * k + 2) (3 * k + 2))) \
      uResidueTwoStableCap k).card = 3 * k ^ 2 + 7 * k := by
  rw [Finset.card_sdiff, Finset.inter_univ, uResidueTwoStableCap_card k hk]
  simp only [Finset.card_univ]
  unfold GridVertex
  simp only [Fintype.card_prod, Fintype.card_fin]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  ring_nf
  omega

@[simp] theorem residueTwoStableCapAt_zero :
    residueTwoStableCapAt 0 = residueTwoExactOccurrenceImage 0 := by
  simp [residueTwoStableCapAt, residueTwoStableBridges,
    residueTwoStableCapDeletions]

/-- At zero pumping the cap-balanced and raw exact representations agree. -/
theorem uResidueTwoStableCap_six_eq_raw :
    uResidueTwoStableCap 6 = uResidueTwoExact 6 := by
  simp [uResidueTwoStableCap, uResidueTwoExact, residueTwoStableCapAt_zero,
    residueTwoExactOccurrenceImage]

theorem uResidueTwoStableCap_six : uResidueTwoStableCap 6 = finiteU20 :=
  uResidueTwoStableCap_six_eq_raw.trans uResidueTwoExact_six

/-! ## Stable edit coordinates -/

/-- Vertex insertion with the same row and column cuts as
`residueTwoExactStepFace (t+6)`. -/
def residueTwoStableStepVertex (t : Nat) :
    GridVertex (20 + 3 * t) (20 + 3 * t) ↪
      GridVertex (20 + 3 * (t + 1)) (20 + 3 * (t + 1)) where
  toFun v :=
    (⟨if 5 + 3 * t ≤ v.1.val then v.1.val + 3 else v.1.val, by
        split <;> have := v.1.isLt <;> omega⟩,
      ⟨if 11 + 3 * t ≤ v.2.val then v.2.val + 3 else v.2.val, by
        split <;> have := v.2.isLt <;> omega⟩)
  inj' := by
    intro v w h
    apply Prod.ext <;> apply Fin.ext
    · have hr := congrArg (fun z => z.1.val) h
      simp only at hr
      split at hr <;> split at hr <;> omega
    · have hc := congrArg (fun z => z.2.val) h
      simp only at hc
      split at hc <;> split at hc <;> omega

theorem residueTwoStableStepVertex_bridge (t : Nat) (j : Fin t) :
    residueTwoStableStepVertex t (residueTwoStableBridgeVertex t j) =
      residueTwoStableBridgeVertex (t + 1) ⟨j.val, by omega⟩ := by
  have hj := j.isLt
  apply Prod.ext
  · apply Fin.ext
    simp [residueTwoStableStepVertex, residueTwoStableBridgeVertex,
      show ¬5 + 3 * t ≤ 5 by omega]
  · apply Fin.ext
    simp [residueTwoStableStepVertex, residueTwoStableBridgeVertex,
      show ¬11 + 3 * t ≤ 13 + 3 * j.val by omega]

theorem residueTwoStableStepVertex_cap (t : Nat) (j : Fin t) :
    residueTwoStableStepVertex t (residueTwoStableCapVertex t j) =
      residueTwoStableCapVertex (t + 1) ⟨j.val, by omega⟩ := by
  have hj := j.isLt
  apply Prod.ext
  · apply Fin.ext
    simp [residueTwoStableStepVertex, residueTwoStableCapVertex,
      show ¬5 + 3 * t ≤ 1 by omega]
  · apply Fin.ext
    simp [residueTwoStableStepVertex, residueTwoStableCapVertex,
      show ¬11 + 3 * t ≤ 13 + 3 * j.val by omega]

theorem residueTwoStableBridges_step_subset (t : Nat) :
    (residueTwoStableBridges t).image (residueTwoStableStepVertex t) ⊆
      residueTwoStableBridges (t + 1) := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hu
  rw [residueTwoStableStepVertex_bridge]
  exact Finset.mem_image.mpr ⟨⟨j.val, by omega⟩, Finset.mem_univ _, rfl⟩

theorem residueTwoStableCapDeletions_step_subset (t : Nat) :
    (residueTwoStableCapDeletions t).image (residueTwoStableStepVertex t) ⊆
      residueTwoStableCapDeletions (t + 1) := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hu
  rw [residueTwoStableStepVertex_cap]
  exact Finset.mem_image.mpr ⟨⟨j.val, by omega⟩, Finset.mem_univ _, rfl⟩

/-- Exactly one new bridge coordinate appears in a successor insertion. -/
theorem residueTwoStableBridges_step_difference_card (t : Nat) :
    (residueTwoStableBridges (t + 1) \
      (residueTwoStableBridges t).image (residueTwoStableStepVertex t)).card = 1 := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr
    (residueTwoStableBridges_step_subset t),
    Finset.card_image_of_injective _ (residueTwoStableStepVertex t).injective]
  simp

/-- Exactly one new cap deletion appears in a successor insertion. -/
theorem residueTwoStableCapDeletions_step_difference_card (t : Nat) :
    (residueTwoStableCapDeletions (t + 1) \
      (residueTwoStableCapDeletions t).image (residueTwoStableStepVertex t)).card = 1 := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr
    (residueTwoStableCapDeletions_step_subset t),
    Finset.card_image_of_injective _ (residueTwoStableStepVertex t).injective]
  simp

/-! ## Forced frame cardinal algebra -/

def forcedResidueTwoStableCapAt (t : Nat) :
    Finset (GridVertex (20 + 3 * t) (20 + 3 * t)) :=
  Finset.univ \ residueTwoStableCapAt t

def residueTwoStableForcedFrame (t : Nat) :
    Finset (GridVertex (20 + 3 * (t + 1)) (20 + 3 * (t + 1))) :=
  forcedResidueTwoStableCapAt (t + 1) \
    (forcedResidueTwoStableCapAt t).image (residueTwoStableStepVertex t)

theorem forcedResidueTwoStableCapAt_card (t : Nat) :
    (forcedResidueTwoStableCapAt t).card =
      3 * (t + 6) ^ 2 + 7 * (t + 6) := by
  rw [forcedResidueTwoStableCapAt, Finset.card_sdiff, Finset.inter_univ,
    residueTwoStableCapAt_card]
  simp only [Finset.card_univ]
  unfold GridVertex
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring_nf
  omega

/-- Once forced-coordinate persistence is supplied, finite cardinal algebra
gives a frame gain of twice the successor side length. -/
theorem residueTwoStableForcedFrame_card (t : Nat)
    (hpersist : (forcedResidueTwoStableCapAt t).image
        (residueTwoStableStepVertex t) ⊆ forcedResidueTwoStableCapAt (t + 1)) :
    (residueTwoStableForcedFrame t).card = 2 * (20 + 3 * (t + 1)) := by
  rw [residueTwoStableForcedFrame, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hpersist,
    Finset.card_image_of_injective _ (residueTwoStableStepVertex t).injective,
    forcedResidueTwoStableCapAt_card, forcedResidueTwoStableCapAt_card]
  ring_nf
  omega

end GridGraphs
