import GridGraphs.Constructions.ResidueTwo.ResidueTwoExactRepair

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
  exact residueTwoExactRepairAdded_disjoint_occurrences t

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
      ⟨j.val, by simp [residueTwoExactMultiplicity]⟩), by
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
    change (if 5 + 3 * t ≤ 5 then 5 + 3 else 5) = 5
    rw [if_neg (by omega)]
  · apply Fin.ext
    change (if 11 + 3 * t ≤ 13 + 3 * j.val then
      13 + 3 * j.val + 3 else 13 + 3 * j.val) = 13 + 3 * j.val
    rw [if_neg (by omega)]

theorem residueTwoStableStepVertex_cap (t : Nat) (j : Fin t) :
    residueTwoStableStepVertex t (residueTwoStableCapVertex t j) =
      residueTwoStableCapVertex (t + 1) ⟨j.val, by omega⟩ := by
  have hj := j.isLt
  apply Prod.ext
  · apply Fin.ext
    change (if 5 + 3 * t ≤ 1 then 1 + 3 else 1) = 1
    rw [if_neg (by omega)]
  · apply Fin.ext
    change (if 11 + 3 * t ≤ 13 + 3 * j.val then
      13 + 3 * j.val + 3 else 13 + 3 * j.val) = 13 + 3 * j.val
    rw [if_neg (by omega)]

/-- An old symbolic occurrence remains a raw occurrence after insertion. -/
theorem residueTwoExactOccurrenceImage_step_subset (t : Nat) :
    (residueTwoExactOccurrenceImage t).image (residueTwoStableStepVertex t) ⊆
      residueTwoExactOccurrenceImage (t + 1) := by
  classical
  intro z hz
  obtain ⟨v, hv, hz⟩ := Finset.mem_image.mp hz
  subst z
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
  let ri : Fin (residueTwoExactMultiplicity 5 (t + 1) x.1) :=
    ⟨if 5 ≤ x.1.val ∧ x.1.val < 8 ∧ x.2.2.val.1.val = t then
        x.2.2.val.1.val + 1 else x.2.2.val.1.val, by
      have hc := x.2.2.val.1.isLt
      by_cases hp : 5 ≤ x.1.val ∧ x.1.val < 8
      · simp [residueTwoExactMultiplicity, hp] at hc ⊢
        by_cases heq : x.2.2.val.1.val = t
        · simp [hp, heq]
        · simp [hp, heq]
          omega
      · have hn : ¬(5 ≤ x.1.val ∧ x.1.val < 8 ∧ x.2.2.val.1.val = t) :=
          fun h => hp ⟨h.1, h.2.1⟩
        simp only [residueTwoExactMultiplicity, if_neg hp] at hc ⊢
        rw [if_neg hn]
        exact hc⟩
  let ci : Fin (residueTwoExactMultiplicity 11 (t + 1) x.2.1) :=
    ⟨if 11 ≤ x.2.1.val ∧ x.2.1.val < 14 ∧ x.2.2.val.2.val = t then
        x.2.2.val.2.val + 1 else x.2.2.val.2.val, by
      have hc := x.2.2.val.2.isLt
      by_cases hp : 11 ≤ x.2.1.val ∧ x.2.1.val < 14
      · simp [residueTwoExactMultiplicity, hp] at hc ⊢
        by_cases heq : x.2.2.val.2.val = t
        · simp [hp, heq]
        · simp [hp, heq]
          omega
      · have hn : ¬(11 ≤ x.2.1.val ∧ x.2.1.val < 14 ∧ x.2.2.val.2.val = t) :=
          fun h => hp ⟨h.1, h.2.1⟩
        simp only [residueTwoExactMultiplicity, if_neg hp] at hc ⊢
        rw [if_neg hn]
        exact hc⟩
  let copies :
      {p : Fin (residueTwoExactMultiplicity 5 (t + 1) x.1) ×
          Fin (residueTwoExactMultiplicity 11 (t + 1) x.2.1) //
        IsResidueTwoExactBase x.1 x.2.1} :=
    ⟨(ri, ci), x.2.2.property⟩
  let y : ResidueTwoExactOccurrence (t + 1) := ⟨x.1, x.2.1, copies⟩
  refine Finset.mem_image.mpr ⟨y, Finset.mem_univ _, ?_⟩
  apply Prod.ext <;> apply Fin.ext
  · symm
    simp only [y, copies, residueTwoStableStepVertex, residueTwoExactVertex]
    change (if 5 + 3 * t ≤
        (residueTwoExactExpandIndex 5 t (by omega) _).val then
          (residueTwoExactExpandIndex 5 t (by omega) _).val + 3 else
          (residueTwoExactExpandIndex 5 t (by omega) _).val) = _
    by_cases hp : 5 ≤ x.1.val ∧ x.1.val < 8
    · rw [residueTwoExactExpandIndex_of_pump 5 t (by omega) _ hp,
        residueTwoExactExpandIndex_of_pump 5 (t + 1) (by omega) _ hp]
      have hc := x.2.2.val.1.isLt
      simp [residueTwoExactMultiplicity, hp] at hc
      simp only [ri]
      split_ifs with h <;> omega
    · by_cases ha : 8 ≤ x.1.val
      · rw [residueTwoExactExpandIndex_of_above 5 t (by omega) _ hp ha,
          residueTwoExactExpandIndex_of_above 5 (t + 1) (by omega) _ hp ha]
        change (if 5 + 3 * t ≤ x.1.val + 3 * t then
          x.1.val + 3 * t + 3 else x.1.val + 3 * t) =
            x.1.val + 3 * (t + 1)
        split <;> omega
      · rw [residueTwoExactExpandIndex_of_below 5 t (by omega) _ hp ha,
          residueTwoExactExpandIndex_of_below 5 (t + 1) (by omega) _ hp ha]
        change (if 5 + 3 * t ≤ x.1.val then x.1.val + 3 else x.1.val) =
          x.1.val
        split <;> omega
  · symm
    simp only [y, copies, residueTwoStableStepVertex, residueTwoExactVertex]
    change (if 11 + 3 * t ≤
        (residueTwoExactExpandIndex 11 t (by omega) _).val then
          (residueTwoExactExpandIndex 11 t (by omega) _).val + 3 else
          (residueTwoExactExpandIndex 11 t (by omega) _).val) = _
    by_cases hp : 11 ≤ x.2.1.val ∧ x.2.1.val < 14
    · rw [residueTwoExactExpandIndex_of_pump 11 t (by omega) _ hp,
        residueTwoExactExpandIndex_of_pump 11 (t + 1) (by omega) _ hp]
      have hc := x.2.2.val.2.isLt
      simp [residueTwoExactMultiplicity, hp] at hc
      simp only [ci]
      split_ifs with h <;> omega
    · by_cases ha : 14 ≤ x.2.1.val
      · rw [residueTwoExactExpandIndex_of_above 11 t (by omega) _ hp ha,
          residueTwoExactExpandIndex_of_above 11 (t + 1) (by omega) _ hp ha]
        change (if 11 + 3 * t ≤ x.2.1.val + 3 * t then
          x.2.1.val + 3 * t + 3 else x.2.1.val + 3 * t) =
            x.2.1.val + 3 * (t + 1)
        split <;> omega
      · rw [residueTwoExactExpandIndex_of_below 11 t (by omega) _ hp ha,
          residueTwoExactExpandIndex_of_below 11 (t + 1) (by omega) _ hp ha]
        change (if 11 + 3 * t ≤ x.2.1.val then x.2.1.val + 3 else x.2.1.val) =
          x.2.1.val
        split <;> omega

/-- A successor expanded index lying in the old-coordinate image has an old
symbolic copy with the same base coordinate. -/
private theorem residueTwoStableExpandIndex_preimage
    (cut t : Nat) (hcut : cut + 3 ≤ 20)
    (x : ResidueTwoExactIndex cut (t + 1)) (a : Fin (20 + 3 * t))
    (h : (if cut + 3 * t ≤ a.val then a.val + 3 else a.val) =
      (residueTwoExactExpandIndex cut (t + 1) hcut x).val) :
    ∃ copy : Fin (residueTwoExactMultiplicity cut t x.base),
      residueTwoExactExpandIndex cut t hcut ⟨x.base, copy⟩ = a := by
  by_cases hp : cut ≤ x.base.val ∧ x.base.val < cut + 3
  · rw [residueTwoExactExpandIndex_of_pump cut (t + 1) hcut x hp] at h
    have hc := x.copy.isLt
    simp only [residueTwoExactMultiplicity, if_pos hp] at hc
    by_cases hlo : x.copy.val < t
    · let copy : Fin (residueTwoExactMultiplicity cut t x.base) :=
        ⟨x.copy.val, by simp [residueTwoExactMultiplicity, hp]; omega⟩
      refine ⟨copy, Fin.ext ?_⟩
      rw [residueTwoExactExpandIndex_of_pump cut t hcut _ hp]
      simp only [copy]
      split at h <;> omega
    · have hne : x.copy.val ≠ t := by
        intro heq
        split at h <;> omega
      let copy : Fin (residueTwoExactMultiplicity cut t x.base) :=
        ⟨t, by simp [residueTwoExactMultiplicity, hp]⟩
      refine ⟨copy, Fin.ext ?_⟩
      rw [residueTwoExactExpandIndex_of_pump cut t hcut _ hp]
      simp only [copy]
      split at h <;> omega
  · by_cases ha : cut + 3 ≤ x.base.val
    · rw [residueTwoExactExpandIndex_of_above cut (t + 1) hcut x hp ha] at h
      let copy : Fin (residueTwoExactMultiplicity cut t x.base) :=
        ⟨0, by simp [residueTwoExactMultiplicity, hp]⟩
      refine ⟨copy, Fin.ext ?_⟩
      rw [residueTwoExactExpandIndex_of_above cut t hcut _ hp ha]
      change x.base.val + 3 * t = a.val
      split at h <;> omega
    · rw [residueTwoExactExpandIndex_of_below cut (t + 1) hcut x hp ha] at h
      let copy : Fin (residueTwoExactMultiplicity cut t x.base) :=
        ⟨0, by simp [residueTwoExactMultiplicity, hp]⟩
      refine ⟨copy, Fin.ext ?_⟩
      rw [residueTwoExactExpandIndex_of_below cut t hcut _ hp ha]
      change x.base.val = a.val
      split at h <;> omega

/-- Raw occurrence membership is reflected as well as preserved by the stable
step embedding. -/
theorem residueTwoExactOccurrenceImage_step_mem_iff (t : Nat)
    (v : GridVertex (20 + 3 * t) (20 + 3 * t)) :
    residueTwoStableStepVertex t v ∈ residueTwoExactOccurrenceImage (t + 1) ↔
      v ∈ residueTwoExactOccurrenceImage t := by
  classical
  constructor
  · intro hv
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hv
    have hr := congrArg (fun z => z.1.val) hx
    have hc := congrArg (fun z => z.2.val) hx
    simp only [residueTwoStableStepVertex, residueTwoExactVertex] at hr hc
    obtain ⟨ri, hri⟩ := residueTwoStableExpandIndex_preimage 5 t (by omega)
      ⟨x.1, x.2.2.val.1⟩ v.1 hr.symm
    obtain ⟨ci, hci⟩ := residueTwoStableExpandIndex_preimage 11 t (by omega)
      ⟨x.2.1, x.2.2.val.2⟩ v.2 hc.symm
    let copies :
        {p : Fin (residueTwoExactMultiplicity 5 t x.1) ×
            Fin (residueTwoExactMultiplicity 11 t x.2.1) //
          IsResidueTwoExactBase x.1 x.2.1} :=
      ⟨(ri, ci), x.2.2.property⟩
    let y : ResidueTwoExactOccurrence t := ⟨x.1, x.2.1, copies⟩
    refine Finset.mem_image.mpr ⟨y, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · simpa [y, copies, residueTwoExactVertex] using hri
    · simpa [y, copies, residueTwoExactVertex] using hci
  · intro hv
    exact residueTwoExactOccurrenceImage_step_subset t
      (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

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

theorem residueTwoStableBridges_step_mem_iff (t : Nat)
    (v : GridVertex (20 + 3 * t) (20 + 3 * t)) :
    residueTwoStableStepVertex t v ∈ residueTwoStableBridges (t + 1) ↔
      v ∈ residueTwoStableBridges t := by
  classical
  constructor
  · intro hv
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hv
    have hc := congrArg (fun z => z.2.val) hj
    change 13 + 3 * j.val =
      (if 11 + 3 * t ≤ v.2.val then v.2.val + 3 else v.2.val) at hc
    have hjlt : j.val < t := by
      have := j.isLt
      split at hc <;> omega
    let i : Fin t := ⟨j.val, hjlt⟩
    let i' : Fin (t + 1) := ⟨i.val, by omega⟩
    have hij : residueTwoStableBridgeVertex (t + 1) i' =
        residueTwoStableBridgeVertex (t + 1) j := by
      apply Prod.ext <;> apply Fin.ext <;>
        simp [residueTwoStableBridgeVertex, i', i]
    have heq : residueTwoStableStepVertex t
        (residueTwoStableBridgeVertex t i) = residueTwoStableStepVertex t v :=
      (residueTwoStableStepVertex_bridge t i).trans (by simpa [i'] using hij.trans hj)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _,
      (residueTwoStableStepVertex t).injective heq⟩
  · intro hv
    exact residueTwoStableBridges_step_subset t
      (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

theorem residueTwoStableCapDeletions_step_mem_iff (t : Nat)
    (v : GridVertex (20 + 3 * t) (20 + 3 * t)) :
    residueTwoStableStepVertex t v ∈ residueTwoStableCapDeletions (t + 1) ↔
      v ∈ residueTwoStableCapDeletions t := by
  classical
  constructor
  · intro hv
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hv
    have hc := congrArg (fun z => z.2.val) hj
    change 13 + 3 * j.val =
      (if 11 + 3 * t ≤ v.2.val then v.2.val + 3 else v.2.val) at hc
    have hjlt : j.val < t := by
      have := j.isLt
      split at hc <;> omega
    let i : Fin t := ⟨j.val, hjlt⟩
    let i' : Fin (t + 1) := ⟨i.val, by omega⟩
    have hij : residueTwoStableCapVertex (t + 1) i' =
        residueTwoStableCapVertex (t + 1) j := by
      apply Prod.ext <;> apply Fin.ext <;>
        simp [residueTwoStableCapVertex, i', i]
    have heq : residueTwoStableStepVertex t
        (residueTwoStableCapVertex t i) = residueTwoStableStepVertex t v :=
      (residueTwoStableStepVertex_cap t i).trans (by simpa [i'] using hij.trans hj)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _,
      (residueTwoStableStepVertex t).injective heq⟩
  · intro hv
    exact residueTwoStableCapDeletions_step_subset t
      (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

/-- Stable-cap U membership is exactly preserved on old coordinates. -/
theorem residueTwoStableCapAt_step_mem_iff (t : Nat)
    (v : GridVertex (20 + 3 * t) (20 + 3 * t)) :
    residueTwoStableStepVertex t v ∈ residueTwoStableCapAt (t + 1) ↔
      v ∈ residueTwoStableCapAt t := by
  simp only [residueTwoStableCapAt, Finset.mem_sdiff, Finset.mem_union]
  rw [residueTwoExactOccurrenceImage_step_mem_iff,
    residueTwoStableBridges_step_mem_iff,
    residueTwoStableCapDeletions_step_mem_iff]

theorem residueTwoStableCapAt_step_subset (t : Nat) :
    (residueTwoStableCapAt t).image (residueTwoStableStepVertex t) ⊆
      residueTwoStableCapAt (t + 1) := by
  intro z hz
  obtain ⟨v, hv, hz⟩ := Finset.mem_image.mp hz
  subst z
  exact (residueTwoStableCapAt_step_mem_iff t v).2 hv

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

/-- Forced-complement membership is exactly preserved on old coordinates. -/
theorem forcedResidueTwoStableCapAt_step_mem_iff (t : Nat)
    (v : GridVertex (20 + 3 * t) (20 + 3 * t)) :
    residueTwoStableStepVertex t v ∈ forcedResidueTwoStableCapAt (t + 1) ↔
      v ∈ forcedResidueTwoStableCapAt t := by
  simp [forcedResidueTwoStableCapAt, residueTwoStableCapAt_step_mem_iff]

theorem forcedResidueTwoStableCapAt_step_subset (t : Nat) :
    (forcedResidueTwoStableCapAt t).image (residueTwoStableStepVertex t) ⊆
      forcedResidueTwoStableCapAt (t + 1) := by
  intro z hz
  obtain ⟨v, hv, hz⟩ := Finset.mem_image.mp hz
  subst z
  exact (forcedResidueTwoStableCapAt_step_mem_iff t v).2 hv

/-- The successor forced set is exactly the old forced image plus its frame. -/
theorem residueTwoStableForcedFrame_coverage (t : Nat) :
    (forcedResidueTwoStableCapAt t).image (residueTwoStableStepVertex t) ∪
        residueTwoStableForcedFrame t =
      forcedResidueTwoStableCapAt (t + 1) := by
  ext v
  simp only [Finset.mem_union, residueTwoStableForcedFrame, Finset.mem_sdiff]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact forcedResidueTwoStableCapAt_step_subset t h
    · exact h
  · intro h
    by_cases hold : v ∈ (forcedResidueTwoStableCapAt t).image
        (residueTwoStableStepVertex t)
    · exact Or.inl hold
    · exact Or.inr ⟨h, hold⟩

/-- The carried forced coordinates and the new frame are disjoint. -/
theorem residueTwoStableForcedFrame_disjoint (t : Nat) :
    Disjoint
      ((forcedResidueTwoStableCapAt t).image (residueTwoStableStepVertex t))
      (residueTwoStableForcedFrame t) := by
  rw [Finset.disjoint_left]
  intro v hold hframe
  simp only [residueTwoStableForcedFrame, Finset.mem_sdiff] at hframe
  exact hframe.2 hold

/-- Compatibility form of the frame cardinal theorem for callers that already
have a persistence proof. -/
theorem residueTwoStableForcedFrame_card_of_persistence (t : Nat)
    (hpersist : (forcedResidueTwoStableCapAt t).image
        (residueTwoStableStepVertex t) ⊆ forcedResidueTwoStableCapAt (t + 1)) :
    (residueTwoStableForcedFrame t).card = 2 * (20 + 3 * (t + 1)) := by
  rw [residueTwoStableForcedFrame, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hpersist,
    Finset.card_image_of_injective _ (residueTwoStableStepVertex t).injective,
    forcedResidueTwoStableCapAt_card, forcedResidueTwoStableCapAt_card]
  ring_nf
  omega

/-- The stable forced frame gains twice the successor side length. -/
theorem residueTwoStableForcedFrame_card (t : Nat) :
    (residueTwoStableForcedFrame t).card = 2 * (20 + 3 * (t + 1)) :=
  residueTwoStableForcedFrame_card_of_persistence t
    (forcedResidueTwoStableCapAt_step_subset t)

end GridGraphs
