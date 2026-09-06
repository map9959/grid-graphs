import GridGraphs.Constructions.ResidueTwo.ResidueTwoExactRepair

/-!
# Local seam geometry for the repaired exact family
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 4000000

/-- An old symbolic occurrence whose physical column is not eight survives the
repair deletion. -/
theorem residueTwoExactVertex_mem_repairAt_of_col_ne_eight
    (t : Nat) (x : ResidueTwoExactOccurrence t)
    (hc : (residueTwoExactVertex t x).2.val ≠ 8) :
    residueTwoExactVertex t x ∈ residueTwoExactRepairAt t := by
  classical
  simp only [residueTwoExactRepairAt, Finset.mem_union, Finset.mem_sdiff]
  left
  constructor
  · exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  · intro hd
    simp only [residueTwoExactRepairDeleted, Finset.mem_image,
      Finset.mem_univ, true_and] at hd
    obtain ⟨j, hj⟩ := hd
    apply hc
    have h := congrArg (fun v => v.2.val) hj
    have : (residueTwoExactVertex t x).2.val = 8 := by
      simpa [residueTwoExactRepairDeletedVertex] using h.symm
    exact this

/-- Build a surviving repair member directly from base coordinates and copy
indices. -/
theorem residueTwoExactRepairAt_mem_of_base
    (t : Nat) (r c : Fin 20)
    (ri : Fin (residueTwoExactMultiplicity 5 t r))
    (ci : Fin (residueTwoExactMultiplicity 11 t c))
    (hbase : IsResidueTwoExactBase r c)
    (hc : (residueTwoExactExpandIndex 11 t (by omega) ⟨c, ci⟩).val ≠ 8) :
    (residueTwoExactExpandIndex 5 t (by omega) ⟨r, ri⟩,
      residueTwoExactExpandIndex 11 t (by omega) ⟨c, ci⟩) ∈
        residueTwoExactRepairAt t := by
  let copies :
      {p : Fin (residueTwoExactMultiplicity 5 t r) ×
          Fin (residueTwoExactMultiplicity 11 t c) //
        IsResidueTwoExactBase r c} := ⟨(ri, ci), hbase⟩
  let x : ResidueTwoExactOccurrence t := ⟨r, c, copies⟩
  exact residueTwoExactVertex_mem_repairAt_of_col_ne_eight t x (by
    simpa [x, copies, residueTwoExactVertex] using hc)

/-- The repaired lower-left corner at seam `j`. -/
theorem residueTwoExactRepairAddedVertex_mem (t : Nat) (j : Fin t) :
    residueTwoExactRepairAddedVertex t j ∈ residueTwoExactRepairAt t := by
  classical
  simp [residueTwoExactRepairAt, residueTwoExactRepairAdded]

/-- The occupied upper endpoint supporting the repaired vertical edge. -/
theorem residueTwoExactRepair_seam_upper_mem (t : Nat) (j : Fin t) :
    (⟨4, by omega⟩, ⟨13 + 3 * j.val, by have := j.isLt; omega⟩) ∈
      residueTwoExactRepairAt t := by
  apply residueTwoExactRepairAt_mem_of_base t
      (⟨4, by omega⟩ : Fin 20) (⟨13, by omega⟩ : Fin 20)
      ⟨0, by simp [residueTwoExactMultiplicity]⟩
      ⟨j.val, by simp [residueTwoExactMultiplicity]; omega⟩
  · simp [IsResidueTwoExactBase, residueTwoExactBaseRow]
  · simp [residueTwoExactExpandIndex]
    omega

/-- The occupied vertex immediately left of an added seam vertex. -/
theorem residueTwoExactRepair_seam_left_mem (t : Nat) (j : Fin t) :
    (⟨5, by omega⟩, ⟨12 + 3 * j.val, by have := j.isLt; omega⟩) ∈
      residueTwoExactRepairAt t := by
  apply residueTwoExactRepairAt_mem_of_base t
      (⟨5, by omega⟩ : Fin 20) (⟨12, by omega⟩ : Fin 20)
      ⟨0, by simp [residueTwoExactMultiplicity]⟩
      ⟨j.val, by simp [residueTwoExactMultiplicity]; omega⟩
  · simp [IsResidueTwoExactBase, residueTwoExactBaseRow]
  · simp [residueTwoExactExpandIndex]
    omega

/-- The occupied first vertex of the copy to the right of seam `j`. -/
theorem residueTwoExactRepair_seam_right_mem (t : Nat) (j : Fin t) :
    (⟨5, by omega⟩, ⟨14 + 3 * j.val, by have := j.isLt; omega⟩) ∈
      residueTwoExactRepairAt t := by
  let ri : Fin (residueTwoExactMultiplicity 5 t (⟨5, by omega⟩ : Fin 20)) :=
    ⟨0, by simp [residueTwoExactMultiplicity]⟩
  let ci : Fin (residueTwoExactMultiplicity 11 t (⟨11, by omega⟩ : Fin 20)) :=
    ⟨j.val + 1, by simp [residueTwoExactMultiplicity]⟩
  have h := residueTwoExactRepairAt_mem_of_base t
    (⟨5, by omega⟩ : Fin 20) (⟨11, by omega⟩ : Fin 20) ri ci
    (by simp [IsResidueTwoExactBase, residueTwoExactBaseRow])
    (by simp [ci, residueTwoExactExpandIndex]; omega)
  convert h using 1
  apply Prod.ext <;> apply Fin.ext <;>
    simp [ri, ci, residueTwoExactExpandIndex] <;> omega

/-- The checkerboard face exposed by repeated-column seam `j`. -/
def residueTwoExactRepairSeamFace (t : Nat) (j : Fin t) :
    GridFace (20 + 3 * t) (20 + 3 * t) :=
  .cell ⟨4, by omega⟩ ⟨13 + 3 * j.val, by have := j.isLt; omega⟩

/-- The face immediately left of the repaired checkerboard. -/
def residueTwoExactRepairSeamLeftFace (t : Nat) (j : Fin t) :
    GridFace (20 + 3 * t) (20 + 3 * t) :=
  .cell ⟨4, by omega⟩ ⟨12 + 3 * j.val, by have := j.isLt; omega⟩

/-- The added vertex gives the formerly isolated face a vertical dual edge. -/
theorem residueTwoExactRepair_seam_adj_left (t : Nat) (j : Fin t) :
    (uuDualGraph (residueTwoExactRepairAt t)).Adj
      (residueTwoExactRepairSeamFace t j)
      (residueTwoExactRepairSeamLeftFace t j) := by
  let e : VerticalGridEdge (20 + 3 * t) (20 + 3 * t) :=
    ⟨⟨4, by omega⟩, ⟨13 + 3 * j.val, by have := j.isLt; omega⟩⟩
  refine ⟨by simp [residueTwoExactRepairSeamFace,
      residueTwoExactRepairSeamLeftFace], Or.inr ⟨e, ?_, ?_, ?_⟩⟩
  · simpa [e, verticalPrimalEndpoints] using
      residueTwoExactRepair_seam_upper_mem t j
  · simpa [e, verticalPrimalEndpoints, residueTwoExactRepairAddedVertex] using
      residueTwoExactRepairAddedVertex_mem t j
  · right
    constructor <;>
      simp [e, verticalDualEndpoints, residueTwoExactRepairSeamFace,
        residueTwoExactRepairSeamLeftFace, show 13 + 3 * j.val + 1 ≠
          20 + 3 * t by have := j.isLt; omega]

/-- The same added vertex also connects the checkerboard face downward through
the first vertex of the next repeated column block. -/
theorem residueTwoExactRepair_seam_adj_below (t : Nat) (j : Fin t) :
    (uuDualGraph (residueTwoExactRepairAt t)).Adj
      (residueTwoExactRepairSeamFace t j)
      (.cell ⟨5, by omega⟩
        ⟨13 + 3 * j.val, by have := j.isLt; omega⟩) := by
  let e : HorizontalGridEdge (20 + 3 * t) (20 + 3 * t) :=
    ⟨⟨5, by omega⟩, ⟨13 + 3 * j.val, by have := j.isLt; omega⟩⟩
  refine ⟨by simp [residueTwoExactRepairSeamFace], Or.inl ⟨e, ?_, ?_, ?_⟩⟩
  · simpa [e, horizontalPrimalEndpoints, residueTwoExactRepairAddedVertex] using
      residueTwoExactRepairAddedVertex_mem t j
  · convert residueTwoExactRepair_seam_right_mem t j using 1
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [e, horizontalPrimalEndpoints]
      omega
  · left
    constructor <;> simp [e, horizontalDualEndpoints,
      residueTwoExactRepairSeamFace, show 5 + 1 ≠ 20 + 3 * t by omega]

end GridGraphs
