import GridGraphs.Constructions.ResidueTwo.ResidueTwoExactStep

/-!
# The repaired exact residue-two family

At copy seam `j` the old pump leaves the face `(4,13+3j)` isolated.  The
vertex `(5,13+3j)` closes that checkerboard.  To keep the exact cost this
construction removes the newly carried copy `(6+3j,8)` of the base vertex
`(6,8)`.  That deletion creates a separate two-face dual obstruction, proved
in `RepairDisconnected`.
-/

namespace GridGraphs

open Finset

set_option maxHeartbeats 4000000

/-- The vertex inserted at repeated-column seam `j`. -/
def residueTwoExactRepairAddedVertex (t : Nat) (j : Fin t) :
    GridVertex (20 + 3 * t) (20 + 3 * t) :=
  (⟨5, by omega⟩, ⟨13 + 3 * j.val, by have := j.isLt; omega⟩)

/-- The cost-balancing row-copy removed at seam `j`. -/
def residueTwoExactRepairDeletedVertex (t : Nat) (j : Fin t) :
    GridVertex (20 + 3 * t) (20 + 3 * t) :=
  (⟨6 + 3 * j.val, by have := j.isLt; omega⟩, ⟨8, by omega⟩)

def residueTwoExactRepairAdded (t : Nat) :
    Finset (GridVertex (20 + 3 * t) (20 + 3 * t)) :=
  Finset.univ.image (residueTwoExactRepairAddedVertex t)

def residueTwoExactRepairDeleted (t : Nat) :
    Finset (GridVertex (20 + 3 * t) (20 + 3 * t)) :=
  Finset.univ.image (residueTwoExactRepairDeletedVertex t)

/-- The unrepaired occurrence image on the enlarged board. -/
def residueTwoExactOccurrenceImage (t : Nat) :
    Finset (GridVertex (20 + 3 * t) (20 + 3 * t)) :=
  (residueTwoExactOccurrences t).image (residueTwoExactVertex t)

/-- Repair at pump depth `t`. -/
def residueTwoExactRepairAt (t : Nat) :
    Finset (GridVertex (20 + 3 * t) (20 + 3 * t)) :=
  (residueTwoExactOccurrenceImage t \ residueTwoExactRepairDeleted t) ∪
    residueTwoExactRepairAdded t

/-- The repaired exact-cost pattern on side `3k+2`. -/
def uResidueTwoExactRepair (k : Nat) :
    Finset (GridVertex (3 * k + 2) (3 * k + 2)) :=
  if hk : 6 ≤ k then
    let castVertex : GridVertex (20 + 3 * (k - 6)) (20 + 3 * (k - 6)) →
        GridVertex (3 * k + 2) (3 * k + 2) := fun x =>
      (⟨x.1.val, by have := x.1.isLt; omega⟩,
        ⟨x.2.val, by have := x.2.isLt; omega⟩)
    (residueTwoExactRepairAt (k - 6)).image castVertex
  else ∅

theorem residueTwoExactRepairAddedVertex_injective (t : Nat) :
    Function.Injective (residueTwoExactRepairAddedVertex t) := by
  intro i j h
  apply Fin.ext
  have hc := congrArg (fun v => v.2.val) h
  simp only [residueTwoExactRepairAddedVertex] at hc
  omega

theorem residueTwoExactRepairDeletedVertex_injective (t : Nat) :
    Function.Injective (residueTwoExactRepairDeletedVertex t) := by
  intro i j h
  apply Fin.ext
  have hr := congrArg (fun v => v.1.val) h
  simp only [residueTwoExactRepairDeletedVertex] at hr
  omega

theorem residueTwoExactRepairAdded_card (t : Nat) :
    (residueTwoExactRepairAdded t).card = t := by
  classical
  rw [residueTwoExactRepairAdded, card_image_of_injective _
    (residueTwoExactRepairAddedVertex_injective t), card_univ, Fintype.card_fin]

theorem residueTwoExactRepairDeleted_card (t : Nat) :
    (residueTwoExactRepairDeleted t).card = t := by
  classical
  rw [residueTwoExactRepairDeleted, card_image_of_injective _
    (residueTwoExactRepairDeletedVertex_injective t), card_univ, Fintype.card_fin]

/-- Every deleted vertex is the indicated symbolic occurrence of `(6,8)`. -/
theorem residueTwoExactRepairDeleted_subset (t : Nat) :
    residueTwoExactRepairDeleted t ⊆ residueTwoExactOccurrenceImage t := by
  classical
  intro v hv
  simp only [residueTwoExactRepairDeleted, Finset.mem_image, Finset.mem_univ,
    true_and] at hv
  obtain ⟨j, rfl⟩ := hv
  let copies :
      {p : Fin (residueTwoExactMultiplicity 5 t (⟨6, by omega⟩ : Fin 20)) ×
          Fin (residueTwoExactMultiplicity 11 t (⟨8, by omega⟩ : Fin 20)) //
        IsResidueTwoExactBase ⟨6, by omega⟩ ⟨8, by omega⟩} :=
    ⟨(⟨j.val, by simp [residueTwoExactMultiplicity]⟩,
      ⟨0, by simp [residueTwoExactMultiplicity]⟩), by
        simp [IsResidueTwoExactBase, residueTwoExactBaseRow]⟩
  let x : ResidueTwoExactOccurrence t :=
    ⟨⟨6, by omega⟩, ⟨8, by omega⟩, copies⟩
  refine Finset.mem_image.mpr ⟨x, Finset.mem_univ _, ?_⟩
  apply Prod.ext <;> apply Fin.ext
  · simp [x, copies, residueTwoExactRepairDeletedVertex,
      residueTwoExactVertex, residueTwoExactExpandIndex]
  · simp [x, copies, residueTwoExactRepairDeletedVertex,
      residueTwoExactVertex, residueTwoExactExpandIndex]

/-- Added seam vertices were precisely the absent `(5,13)` base entries. -/
theorem residueTwoExactRepairAdded_disjoint_occurrences (t : Nat) :
    Disjoint (residueTwoExactRepairAdded t) (residueTwoExactOccurrenceImage t) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvadd hvold
  simp only [residueTwoExactRepairAdded, Finset.mem_image, Finset.mem_univ,
    true_and] at hvadd
  obtain ⟨j, rfl⟩ := hvadd
  simp only [residueTwoExactOccurrenceImage, Finset.mem_image,
    residueTwoExactOccurrences, Finset.mem_univ, true_and] at hvold
  obtain ⟨x, hx⟩ := hvold
  have hc : residueTwoExactExpandIndex 11 t (by omega)
      ⟨x.2.1, x.2.2.val.2⟩ =
      residueTwoExactExpandIndex 11 t (by omega)
        ⟨⟨13, by omega⟩, ⟨j.val, by
          simp [residueTwoExactMultiplicity]⟩⟩ := by
    apply Fin.ext
    have h := congrArg (fun z => z.2.val) hx
    simpa [residueTwoExactVertex, residueTwoExactRepairAddedVertex,
      residueTwoExactExpandIndex] using h
  have hi := residueTwoExactExpandIndex_injective 11 t (by omega) hc
  have hbase : x.2.1 = (⟨13, by omega⟩ : Fin 20) :=
    congrArg ResidueTwoExactIndex.base hi
  have hxbase := x.2.2.property
  rw [hbase] at hxbase
  have hrexp : residueTwoExactExpandIndex 5 t (by omega)
      ⟨x.1, x.2.2.val.1⟩ =
      residueTwoExactExpandIndex 5 t (by omega)
        ⟨⟨5, by omega⟩, ⟨0, by
          simp [residueTwoExactMultiplicity]⟩⟩ := by
    apply Fin.ext
    have h := congrArg (fun z => z.1.val) hx
    simpa [residueTwoExactVertex, residueTwoExactRepairAddedVertex,
      residueTwoExactExpandIndex] using h
  have hri := residueTwoExactExpandIndex_injective 5 t (by omega) hrexp
  have hr : x.1 = (⟨5, by omega⟩ : Fin 20) :=
    congrArg ResidueTwoExactIndex.base hri
  rw [hr] at hxbase
  simp [IsResidueTwoExactBase, residueTwoExactBaseRow] at hxbase

theorem residueTwoExactRepairAdded_disjoint_deleted (t : Nat) :
    Disjoint (residueTwoExactRepairAdded t) (residueTwoExactRepairDeleted t) := by
  classical
  rw [Finset.disjoint_left]
  intro v ha hd
  simp only [residueTwoExactRepairAdded, residueTwoExactRepairDeleted,
    Finset.mem_image, Finset.mem_univ, true_and] at ha hd
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, h⟩ := hd
  have hc := congrArg (fun z => z.2.val) h
  simp [residueTwoExactRepairAddedVertex,
    residueTwoExactRepairDeletedVertex] at hc
  omega

theorem residueTwoExactOccurrenceImage_card (t : Nat) :
    (residueTwoExactOccurrenceImage t).card =
      6 * (t + 1) ^ 2 + 65 * (t + 1) + 179 := by
  classical
  rw [residueTwoExactOccurrenceImage, card_image_of_injective _
    (residueTwoExactVertex_injective t), residueTwoExactOccurrences_card,
    residueTwoExact_weighted_base]

theorem residueTwoExactRepairAt_card (t : Nat) :
    (residueTwoExactRepairAt t).card =
      6 * (t + 1) ^ 2 + 65 * (t + 1) + 179 := by
  classical
  have hdisj : Disjoint
      (residueTwoExactOccurrenceImage t \ residueTwoExactRepairDeleted t)
      (residueTwoExactRepairAdded t) :=
    (residueTwoExactRepairAdded_disjoint_occurrences t).symm.mono_left
      Finset.sdiff_subset
  rw [residueTwoExactRepairAt, card_union_of_disjoint hdisj,
    card_sdiff,
    Finset.inter_eq_left.mpr (residueTwoExactRepairDeleted_subset t),
    residueTwoExactOccurrenceImage_card, residueTwoExactRepairDeleted_card,
    residueTwoExactRepairAdded_card]
  omega

/-- The repair has exactly the required U-cardinality. -/
theorem uResidueTwoExactRepair_card (k : Nat) (hk : 6 ≤ k) :
    (uResidueTwoExactRepair k).card = 6 * k ^ 2 + 5 * k + 4 := by
  classical
  simp only [uResidueTwoExactRepair, dif_pos hk]
  rw [card_image_of_injective, residueTwoExactRepairAt_card]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    simp
    ring
  · intro x y h
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun z => z.1.val) h
    · exact congrArg (fun z => z.2.val) h

/-- Exact complement count of the repaired family. -/
theorem uResidueTwoExactRepair_compl_card (k : Nat) (hk : 6 ≤ k) :
    ((Finset.univ : Finset (GridVertex (3 * k + 2) (3 * k + 2))) \
      uResidueTwoExactRepair k).card = 3 * k ^ 2 + 7 * k := by
  rw [Finset.card_sdiff, Finset.inter_univ,
    uResidueTwoExactRepair_card k hk]
  have htotal :
      Fintype.card (GridVertex (3 * k + 2) (3 * k + 2)) =
        (3 * k + 2) * (3 * k + 2) := by
    unfold GridVertex
    simp
  rw [Finset.card_univ, htotal]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  ring_nf
  omega

/-- At `t=0` there are no seam edits. -/
theorem residueTwoExactRepairAt_zero :
    residueTwoExactRepairAt 0 = residueTwoExactOccurrenceImage 0 := by
  simp [residueTwoExactRepairAt, residueTwoExactRepairAdded,
    residueTwoExactRepairDeleted]

/-- The repaired family leaves the proved twenty-by-twenty base unchanged. -/
theorem uResidueTwoExactRepair_six : uResidueTwoExactRepair 6 = finiteU20 := by
  rw [show uResidueTwoExactRepair 6 = uResidueTwoExact 6 by
    simp [uResidueTwoExactRepair, uResidueTwoExact,
      residueTwoExactRepairAt_zero, residueTwoExactOccurrenceImage]]
  exact uResidueTwoExact_six

end GridGraphs
