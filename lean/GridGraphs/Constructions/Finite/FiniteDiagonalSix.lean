import GridGraphs.Constructions.ConstructionCertificate
import GridGraphs.Constructions.ResidueZero.ResidueZeroCaps

/-!
# The finite 6 by 6 diagonal construction

An explicit ranked dual certificate for the construction with row masks
`[0, 63, 30, 50, 62, 6]`.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The twenty selected vertices in the `6 x 6` row-mask construction. -/
def finiteU6 : Finset (GridVertex 6 6) :=
  Finset.univ.filter fun v =>
    if v.1.val = 0 then False
    else if v.1.val = 1 then True
    else if v.1.val = 2 then 1 ≤ v.2.val ∧ v.2.val ≤ 4
    else if v.1.val = 3 then v.2.val = 1 ∨ 4 ≤ v.2.val
    else if v.1.val = 4 then 1 ≤ v.2.val
    else v.2.val = 1 ∨ v.2.val = 2

private theorem finiteU6_bottom_adj :
    (uuDualGraph finiteU6).Adj (.cell 4 1) .out := by
  let e : HorizontalGridEdge 6 6 := ⟨5, 1⟩
  refine ⟨by simp, Or.inl ⟨e, ?_, ?_, ?_⟩⟩
  · simp [finiteU6, e, horizontalPrimalEndpoints]
  · simp [finiteU6, e, horizontalPrimalEndpoints]
  · simp [e, HasDualEndpoints, horizontalDualEndpoints]

private theorem finiteU6_right_adj :
    (uuDualGraph finiteU6).Adj (.cell 3 4) .out := by
  apply vertical_uu_dual_right_out_adj finiteU6 3 (by norm_num) (by norm_num)
  · simp [finiteU6]
  · simp [finiteU6]

/-- A parent tree on `out` and all twenty-five bounded faces. -/
def finiteU6Parent : GridFace 6 6 → GridFace 6 6
  | .out => .out
  | .cell r c =>
      if r.val = 0 then .cell 1 c
      else if r.val = 1 then
        if c.val = 0 then .cell 1 1
        else if c.val = 1 then .cell 1 2
        else if c.val = 2 then .cell 1 3
        else if c.val = 3 then .cell 2 3
        else .cell 1 3
      else if r.val = 2 then
        if c.val = 0 then .cell 2 1
        else if c.val = 1 then .cell 1 1
        else if c.val = 2 then .cell 1 2
        else if c.val = 3 then .cell 2 4
        else .cell 3 4
      else if r.val = 3 then
        if c.val = 0 then .cell 3 1
        else if c.val = 1 then .cell 4 1
        else if c.val = 2 then .cell 4 2
        else if c.val = 3 then .cell 3 4
        else .out
      else
        if c.val = 0 then .cell 4 1
        else if c.val = 1 then .out
        else if c.val = 2 then .cell 4 1
        else if c.val = 3 then .cell 3 3
        else .cell 3 4

/-- Depth in `finiteU6Parent`, with rank zero at the outside face. -/
def finiteU6Rank : GridFace 6 6 → Nat
  | .out => 0
  | .cell r c =>
      if r.val = 0 then
        if c.val = 0 then 8
        else if c.val = 1 then 7
        else if c.val = 2 then 6
        else if c.val = 3 then 5
        else 6
      else if r.val = 1 then
        if c.val = 0 then 7
        else if c.val = 1 then 6
        else if c.val = 2 then 5
        else if c.val = 3 then 4
        else 5
      else if r.val = 2 then
        if c.val = 0 then 8
        else if c.val = 1 then 7
        else if c.val = 2 then 6
        else if c.val = 3 then 3
        else 2
      else if r.val = 3 then
        if c.val = 0 then 3
        else if c.val = 1 then 2
        else if c.val = 2 then 3
        else if c.val = 3 then 2
        else 1
      else
        if c.val = 0 then 2
        else if c.val = 1 then 1
        else if c.val = 2 then 2
        else if c.val = 3 then 3
        else 2

private theorem finiteU6_parent_adj (f : GridFace 6 6) (hf : f ≠ .out) :
    (uuDualGraph finiteU6).Adj f (finiteU6Parent f) := by
  cases f with
  | out => exact (hf rfl).elim
  | cell r c =>
      fin_cases r <;> fin_cases c
      · simpa [finiteU6Parent] using horizontal_uu_dual_cells_adj finiteU6 1 0
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using horizontal_uu_dual_cells_adj finiteU6 1 1
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using horizontal_uu_dual_cells_adj finiteU6 1 2
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using horizontal_uu_dual_cells_adj finiteU6 1 3
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using horizontal_uu_dual_cells_adj finiteU6 1 4
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using vertical_uu_dual_cells_adj finiteU6 1 1
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using vertical_uu_dual_cells_adj finiteU6 1 2
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using vertical_uu_dual_cells_adj finiteU6 1 3
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using horizontal_uu_dual_cells_adj finiteU6 2 3
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using
          (vertical_uu_dual_cells_adj finiteU6 1 4
            (by norm_num) (by norm_num) (by norm_num)
            (by simp [finiteU6]) (by simp [finiteU6])).symm
      · simpa [finiteU6Parent] using vertical_uu_dual_cells_adj finiteU6 2 1
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using
          (horizontal_uu_dual_cells_adj finiteU6 2 1
            (by norm_num) (by norm_num) (by norm_num)
            (by simp [finiteU6]) (by simp [finiteU6])).symm
      · simpa [finiteU6Parent] using
          (horizontal_uu_dual_cells_adj finiteU6 2 2
            (by norm_num) (by norm_num) (by norm_num)
            (by simp [finiteU6]) (by simp [finiteU6])).symm
      · simpa [finiteU6Parent] using vertical_uu_dual_cells_adj finiteU6 2 4
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using horizontal_uu_dual_cells_adj finiteU6 3 4
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using vertical_uu_dual_cells_adj finiteU6 3 1
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using horizontal_uu_dual_cells_adj finiteU6 4 1
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using horizontal_uu_dual_cells_adj finiteU6 4 2
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using vertical_uu_dual_cells_adj finiteU6 3 4
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using finiteU6_right_adj
      · simpa [finiteU6Parent] using vertical_uu_dual_cells_adj finiteU6 4 1
          (by norm_num) (by norm_num) (by norm_num)
          (by simp [finiteU6]) (by simp [finiteU6])
      · simpa [finiteU6Parent] using finiteU6_bottom_adj
      · simpa [finiteU6Parent] using
          (vertical_uu_dual_cells_adj finiteU6 4 2
            (by norm_num) (by norm_num) (by norm_num)
            (by simp [finiteU6]) (by simp [finiteU6])).symm
      · simpa [finiteU6Parent] using
          (horizontal_uu_dual_cells_adj finiteU6 4 3
            (by norm_num) (by norm_num) (by norm_num)
            (by simp [finiteU6]) (by simp [finiteU6])).symm
      · simpa [finiteU6Parent] using
          (horizontal_uu_dual_cells_adj finiteU6 4 4
            (by norm_num) (by norm_num) (by norm_num)
            (by simp [finiteU6]) (by simp [finiteU6])).symm

/-- The explicit ranked parent certificate on all twenty-six dual faces. -/
def finiteU6RankedDualCertificate :
    RankedParentCertificate (uuDualGraph finiteU6) where
  root := .out
  parent := finiteU6Parent
  rank := finiteU6Rank
  parent_adj := finiteU6_parent_adj
  rank_parent_lt := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c <;>
          norm_num [finiteU6Parent, finiteU6Rank]

theorem finiteU6_compl_card :
    ((Finset.univ : Finset (GridVertex 6 6)) \ finiteU6).card = 16 := by
  have hU : finiteU6.card = 20 := by
    rfl
  rw [Finset.card_sdiff, Finset.inter_univ, hU]
  change 36 - 20 = 16
  norm_num

/-- Sixteen vertices can be preserved in the `6 x 6` grid. -/
theorem sixteen_le_maxPreserved_six_six : 16 ≤ maxPreserved 6 6 := by
  rw [← finiteU6_compl_card]
  exact compl_card_le_maxPreserved_of_rankedDualCertificate
    (by norm_num) (by norm_num) finiteU6 finiteU6RankedDualCertificate

end GridGraphs
