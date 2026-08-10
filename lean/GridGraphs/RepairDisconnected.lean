import GridGraphs.ResidueTwoExactRepairLocal

/-!
# Disconnection of the exact residue-two repair

At every repeated-row seam, deleting `(6+3j,8)` closes a two-face cut rather
than preserving dual connectivity.  This file proves the obstruction directly
from symbolic occurrence membership, without evaluation of the finite graph.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 4000000

/-- A face in the two-face component created at repeated-row seam `j`. -/
def residueTwoExactRepairCutFace (t : Nat) (j : Fin t) (c : Fin 2) :
    GridFace (20 + 3 * t) (20 + 3 * t) :=
  .cell ⟨5 + 3 * j.val, by have := j.isLt; omega⟩
    ⟨6 + c.val, by omega⟩

/-- The two faces sealed off by the repair deletion at seam `j`. -/
def residueTwoExactRepairCut (t : Nat) (j : Fin t) :
    Set (GridFace (20 + 3 * t) (20 + 3 * t)) :=
  {residueTwoExactRepairCutFace t j 0,
    residueTwoExactRepairCutFace t j 1}

/-- An absent base entry below the column pump remains absent in every copy of
a pumped row. -/
theorem residueTwoExactOccurrenceImage_pumped_row_not_mem
    (t : Nat) (j : Fin t) (r c : Fin 20)
    (hr : 5 ≤ r.val ∧ r.val < 8)
    (hc : c.val < 11) (hbase : ¬IsResidueTwoExactBase r c) :
    (⟨r.val + 3 * j.val, by have := j.isLt; omega⟩,
      ⟨c.val, by omega⟩) ∉ residueTwoExactOccurrenceImage t := by
  classical
  simp only [residueTwoExactOccurrenceImage, Finset.mem_image,
    residueTwoExactOccurrences, Finset.mem_univ, true_and, not_exists]
  intro x hx
  have hrow := congrArg (fun z => z.1.val) hx
  have hcol := congrArg (fun z => z.2.val) hx
  simp only [residueTwoExactVertex] at hrow hcol
  have hxrow := x.1.isLt
  have hxcol := x.2.1.isLt
  have hj := j.isLt
  have hrowbase : x.1 = r := by
    apply Fin.ext
    by_cases hp : 5 ≤ x.1.val ∧ x.1.val < 5 + 3
    · rw [residueTwoExactExpandIndex_of_pump 5 t (by omega) _ hp] at hrow
      have hcopy := x.2.2.val.1.isLt
      simp [residueTwoExactMultiplicity, hp] at hcopy
      simp only at hrow
      omega
    · by_cases ha : 5 + 3 ≤ x.1.val
      · rw [residueTwoExactExpandIndex_of_above 5 t (by omega) _ hp ha] at hrow
        simp only at hrow
        omega
      · rw [residueTwoExactExpandIndex_of_below 5 t (by omega) _ hp ha] at hrow
        simp only at hrow
        omega
  have hcolbase : x.2.1 = c := by
    apply Fin.ext
    by_cases hp : 11 ≤ x.2.1.val ∧ x.2.1.val < 11 + 3
    · rw [residueTwoExactExpandIndex_of_pump 11 t (by omega) _ hp] at hcol
      have hcopy := x.2.2.val.2.isLt
      simp [residueTwoExactMultiplicity, hp] at hcopy
      simp only at hcol
      omega
    · by_cases ha : 11 + 3 ≤ x.2.1.val
      · rw [residueTwoExactExpandIndex_of_above 11 t (by omega) _ hp ha] at hcol
        simp only at hcol
        omega
      · rw [residueTwoExactExpandIndex_of_below 11 t (by omega) _ hp ha] at hcol
        simp only at hcol
        omega
  exact hbase (hrowbase ▸ hcolbase ▸ x.2.2.property)

/-- A vertex absent from the occurrence image and lying left of every added
repair vertex is absent from the repaired set. -/
theorem residueTwoExactRepairAt_not_mem_of_occurrence_of_col_lt_thirteen
    (t : Nat) (v : GridVertex (20 + 3 * t) (20 + 3 * t))
    (hvold : v ∉ residueTwoExactOccurrenceImage t) (hc : v.2.val < 13) :
    v ∉ residueTwoExactRepairAt t := by
  classical
  simp only [residueTwoExactRepairAt, Finset.mem_union, Finset.mem_sdiff,
    not_or]
  constructor
  · exact fun h => hvold h.1
  · simp only [residueTwoExactRepairAdded, Finset.mem_image,
      Finset.mem_univ, true_and, not_exists]
    intro i hi
    have hcol := congrArg (fun z => z.2.val) hi
    simp [residueTwoExactRepairAddedVertex] at hcol
    omega

theorem residueTwoExactRepair_rowFive_colSix_not_mem
    (t : Nat) (j : Fin t) :
    (⟨5 + 3 * j.val, by have := j.isLt; omega⟩, ⟨6, by omega⟩) ∉
      residueTwoExactRepairAt t := by
  apply residueTwoExactRepairAt_not_mem_of_occurrence_of_col_lt_thirteen
  · apply residueTwoExactOccurrenceImage_pumped_row_not_mem t j
      (⟨5, by omega⟩ : Fin 20) (⟨6, by omega⟩ : Fin 20)
    · norm_num
    · norm_num
    · simp [IsResidueTwoExactBase, residueTwoExactBaseRow]
  · simp

theorem residueTwoExactRepair_rowFive_colEight_not_mem
    (t : Nat) (j : Fin t) :
    (⟨5 + 3 * j.val, by have := j.isLt; omega⟩, ⟨8, by omega⟩) ∉
      residueTwoExactRepairAt t := by
  apply residueTwoExactRepairAt_not_mem_of_occurrence_of_col_lt_thirteen
  · apply residueTwoExactOccurrenceImage_pumped_row_not_mem t j
      (⟨5, by omega⟩ : Fin 20) (⟨8, by omega⟩ : Fin 20)
    · norm_num
    · norm_num
    · simp [IsResidueTwoExactBase, residueTwoExactBaseRow]
  · simp

theorem residueTwoExactRepair_rowSix_colSix_not_mem
    (t : Nat) (j : Fin t) :
    (⟨6 + 3 * j.val, by have := j.isLt; omega⟩, ⟨6, by omega⟩) ∉
      residueTwoExactRepairAt t := by
  apply residueTwoExactRepairAt_not_mem_of_occurrence_of_col_lt_thirteen
  · apply residueTwoExactOccurrenceImage_pumped_row_not_mem t j
      (⟨6, by omega⟩ : Fin 20) (⟨6, by omega⟩ : Fin 20)
    · norm_num
    · norm_num
    · simp [IsResidueTwoExactBase, residueTwoExactBaseRow]
  · simp

/-- The cost-balancing deletion is genuinely absent from the repaired set. -/
theorem residueTwoExactRepairDeletedVertex_not_mem
    (t : Nat) (j : Fin t) :
    residueTwoExactRepairDeletedVertex t j ∉ residueTwoExactRepairAt t := by
  classical
  have hd : residueTwoExactRepairDeletedVertex t j ∈
      residueTwoExactRepairDeleted t := by
    simp [residueTwoExactRepairDeleted]
  have ha : residueTwoExactRepairDeletedVertex t j ∉
      residueTwoExactRepairAdded t := by
    intro h
    exact Finset.disjoint_left.mp
      (residueTwoExactRepairAdded_disjoint_deleted t) h hd
  simp [residueTwoExactRepairAt, hd, ha]

/-- Every horizontal U-U dual adjacency stays on one side of the two-face
cut. -/
theorem residueTwoExactRepairCut_horizontal
    (t : Nat) (j : Fin t) (e : HorizontalGridEdge (20 + 3 * t) (20 + 3 * t))
    (he₁ : (horizontalPrimalEndpoints e).1 ∈ residueTwoExactRepairAt t)
    (he₂ : (horizontalPrimalEndpoints e).2 ∈ residueTwoExactRepairAt t) :
    (horizontalDualEndpoints e).1 ∈ residueTwoExactRepairCut t j ↔
      (horizontalDualEndpoints e).2 ∈ residueTwoExactRepairCut t j := by
  have hj := j.isLt
  by_cases htop : e.row.val = 0
  · simp [residueTwoExactRepairCut, residueTwoExactRepairCutFace,
      horizontalDualEndpoints, htop, show 1 ≠ 20 + 3 * t by omega] <;> omega
  by_cases hbottom : e.row.val + 1 = 20 + 3 * t
  · simp [residueTwoExactRepairCut, residueTwoExactRepairCutFace,
      horizontalDualEndpoints, htop, hbottom] <;> omega
  simp only [horizontalDualEndpoints, dif_neg htop, dif_neg hbottom]
  constructor
  · intro h
    simp only [residueTwoExactRepairCut, Set.mem_insert_iff,
      Set.mem_singleton_iff] at h
    rcases h with h | h
    · have hr := congrArg (fun f => match f with | .out => 0 | .cell r _ => r.val) h
      have hc := congrArg (fun f => match f with | .out => 0 | .cell _ c => c.val) h
      simp [residueTwoExactRepairCutFace] at hr hc
      exact False.elim ((residueTwoExactRepair_rowSix_colSix_not_mem t j) (by
        have hv : (⟨6 + 3 * j.val, by omega⟩, ⟨6, by omega⟩) =
            (horizontalPrimalEndpoints e).1 := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [horizontalPrimalEndpoints] <;> omega
        rw [hv]
        exact he₁))
    · have hr := congrArg (fun f => match f with | .out => 0 | .cell r _ => r.val) h
      have hc := congrArg (fun f => match f with | .out => 0 | .cell _ c => c.val) h
      simp [residueTwoExactRepairCutFace] at hr hc
      exact False.elim ((residueTwoExactRepairDeletedVertex_not_mem t j) (by
        have hv : residueTwoExactRepairDeletedVertex t j =
            (horizontalPrimalEndpoints e).2 := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [horizontalPrimalEndpoints, residueTwoExactRepairDeletedVertex] <;> omega
        rw [hv]
        exact he₂))
  · intro h
    simp only [residueTwoExactRepairCut, Set.mem_insert_iff,
      Set.mem_singleton_iff] at h
    rcases h with h | h
    · have hr := congrArg (fun f => match f with | .out => 0 | .cell r _ => r.val) h
      have hc := congrArg (fun f => match f with | .out => 0 | .cell _ c => c.val) h
      simp [residueTwoExactRepairCutFace] at hr hc
      exact False.elim ((residueTwoExactRepair_rowFive_colSix_not_mem t j) (by
        have hv : (⟨5 + 3 * j.val, by omega⟩, ⟨6, by omega⟩) =
            (horizontalPrimalEndpoints e).1 := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [horizontalPrimalEndpoints] <;> omega
        rw [hv]
        exact he₁))
    · have hr := congrArg (fun f => match f with | .out => 0 | .cell r _ => r.val) h
      have hc := congrArg (fun f => match f with | .out => 0 | .cell _ c => c.val) h
      simp [residueTwoExactRepairCutFace] at hr hc
      exact False.elim ((residueTwoExactRepair_rowFive_colEight_not_mem t j) (by
        have hv : (⟨5 + 3 * j.val, by omega⟩, ⟨8, by omega⟩) =
            (horizontalPrimalEndpoints e).2 := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [horizontalPrimalEndpoints] <;> omega
        rw [hv]
        exact he₂))

/-- Every vertical U-U dual adjacency stays on one side of the two-face cut. -/
theorem residueTwoExactRepairCut_vertical
    (t : Nat) (j : Fin t) (e : VerticalGridEdge (20 + 3 * t) (20 + 3 * t))
    (he₁ : (verticalPrimalEndpoints e).1 ∈ residueTwoExactRepairAt t)
    (_he₂ : (verticalPrimalEndpoints e).2 ∈ residueTwoExactRepairAt t) :
    (verticalDualEndpoints e).1 ∈ residueTwoExactRepairCut t j ↔
      (verticalDualEndpoints e).2 ∈ residueTwoExactRepairCut t j := by
  have hj := j.isLt
  by_cases hleft : e.col.val = 0
  · simp [residueTwoExactRepairCut, residueTwoExactRepairCutFace,
      verticalDualEndpoints, hleft, show 1 ≠ 20 + 3 * t by omega]
  by_cases hright : e.col.val + 1 = 20 + 3 * t
  · simp [residueTwoExactRepairCut, residueTwoExactRepairCutFace,
      verticalDualEndpoints, hleft, hright] <;> omega
  simp only [verticalDualEndpoints, dif_neg hleft, dif_neg hright]
  constructor
  · intro h
    simp only [residueTwoExactRepairCut, Set.mem_insert_iff,
      Set.mem_singleton_iff] at h ⊢
    rcases h with h | h
    · have hr := congrArg (fun f => match f with | .out => 0 | .cell r _ => r.val) h
      have hc := congrArg (fun f => match f with | .out => 0 | .cell _ c => c.val) h
      simp [residueTwoExactRepairCutFace] at hr hc
      right
      congr 1
      · exact Fin.ext (by omega)
      · apply Fin.ext
        norm_num
        omega
    · have hr := congrArg (fun f => match f with | .out => 0 | .cell r _ => r.val) h
      have hc := congrArg (fun f => match f with | .out => 0 | .cell _ c => c.val) h
      simp [residueTwoExactRepairCutFace] at hr hc
      exact False.elim ((residueTwoExactRepair_rowFive_colEight_not_mem t j) (by
        have hv : (⟨5 + 3 * j.val, by omega⟩, ⟨8, by omega⟩) =
            (verticalPrimalEndpoints e).1 := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [verticalPrimalEndpoints] <;> omega
        rw [hv]
        exact he₁))
  · intro h
    simp only [residueTwoExactRepairCut, Set.mem_insert_iff,
      Set.mem_singleton_iff] at h ⊢
    rcases h with h | h
    · have hr := congrArg (fun f => match f with | .out => 0 | .cell r _ => r.val) h
      have hc := congrArg (fun f => match f with | .out => 0 | .cell _ c => c.val) h
      simp [residueTwoExactRepairCutFace] at hr hc
      exact False.elim ((residueTwoExactRepair_rowFive_colSix_not_mem t j) (by
        have hv : (⟨5 + 3 * j.val, by omega⟩, ⟨6, by omega⟩) =
            (verticalPrimalEndpoints e).1 := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [verticalPrimalEndpoints] <;> omega
        rw [hv]
        exact he₁))
    · have hr := congrArg (fun f => match f with | .out => 0 | .cell r _ => r.val) h
      have hc := congrArg (fun f => match f with | .out => 0 | .cell _ c => c.val) h
      simp [residueTwoExactRepairCutFace] at hr hc
      left
      congr 1
      · exact Fin.ext (by omega)
      · apply Fin.ext
        norm_num
        omega

/-- Every dual adjacency of the repaired pattern respects the two-face cut. -/
theorem residueTwoExactRepair_respectsCut (t : Nat) (j : Fin t) :
    RespectsCut (uuDualGraph (residueTwoExactRepairAt t))
      (residueTwoExactRepairCut t j) := by
  intro x y hxy
  rcases hxy.2 with h | h
  · obtain ⟨e, he₁, he₂, hends⟩ := h
    exact (hasDualEndpoints_iff hends
      (fun f => f ∈ residueTwoExactRepairCut t j)).mpr
      (residueTwoExactRepairCut_horizontal t j e he₁ he₂)
  · obtain ⟨e, he₁, he₂, hends⟩ := h
    exact (hasDualEndpoints_iff hends
      (fun f => f ∈ residueTwoExactRepairCut t j)).mpr
      (residueTwoExactRepairCut_vertical t j e he₁ he₂)

/-- The repaired pattern is dual-disconnected at every positive pump depth. -/
theorem residueTwoExactRepairAt_not_dual_connected (t : Nat) (ht : 0 < t) :
    ¬(uuDualGraph (residueTwoExactRepairAt t)).Connected := by
  let j : Fin t := ⟨0, ht⟩
  apply not_connected_of_respectsCut
    (residueTwoExactRepair_respectsCut t j)
  · exact ⟨residueTwoExactRepairCutFace t j 0, by
      simp [residueTwoExactRepairCut, residueTwoExactRepairCutFace]⟩
  · exact ⟨GridFace.out, by simp [residueTwoExactRepairCut,
      residueTwoExactRepairCutFace]⟩

end GridGraphs
