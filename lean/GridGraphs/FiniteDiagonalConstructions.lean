import GridGraphs.ConstructionCertificate
import GridGraphs.ResidueZeroDual
import GridGraphs.FiniteDiagonalSix
import GridGraphs.FiniteDiagonalEight
import GridGraphs.FiniteDiagonalNine
import GridGraphs.FiniteDiagonalEleven
import GridGraphs.FiniteDiagonalTwelve
import GridGraphs.FiniteDiagonalFourteen
import GridGraphs.FiniteDiagonalFifteen
import GridGraphs.FiniteDiagonalSeventeen
import GridGraphs.FiniteDiagonalEighteen
import GridGraphs.FiniteDiagonalTwenty

/-!
# Finite diagonal constructions

Explicit ranked dual certificates for the `3 x 3` and `5 x 5` diagonal
constructions.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The five selected vertices in the `3 x 3` construction with row masks
`[3, 7, 0]`. -/
def finiteU3 : Finset (GridVertex 3 3) :=
  {(0, 0), (0, 1), (1, 0), (1, 1), (1, 2)}

private abbrev face00 : GridFace 3 3 := .cell 0 0
private abbrev face01 : GridFace 3 3 := .cell 0 1
private abbrev face10 : GridFace 3 3 := .cell 1 0
private abbrev face11 : GridFace 3 3 := .cell 1 1

private theorem gridVertex_eq_iff {m n : Nat} (v w : GridVertex m n) :
    v = w ↔ v.1.val = w.1.val ∧ v.2.val = w.2.val := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hrow, hcol⟩
    apply Prod.ext
    · exact Fin.ext hrow
    · exact Fin.ext hcol

private theorem finiteU3_face00_out_adj :
    (uuDualGraph finiteU3).Adj face00 .out := by
  refine ⟨by simp, Or.inl ⟨⟨0, 0⟩, ?_, ?_, ?_⟩⟩
  · simp [finiteU3, horizontalPrimalEndpoints]
  · simp [finiteU3, horizontalPrimalEndpoints]
  · simp [face00, HasDualEndpoints, horizontalDualEndpoints]

private theorem finiteU3_face01_face00_adj :
    (uuDualGraph finiteU3).Adj face01 face00 := by
  refine ⟨by simp [face01, face00], Or.inr ⟨⟨0, 1⟩, ?_, ?_, ?_⟩⟩
  · simp [finiteU3, verticalPrimalEndpoints]
  · simp [finiteU3, verticalPrimalEndpoints]
  · simp [face01, face00, HasDualEndpoints, verticalDualEndpoints]

private theorem finiteU3_face10_face00_adj :
    (uuDualGraph finiteU3).Adj face10 face00 := by
  refine ⟨by simp [face10, face00], Or.inl ⟨⟨1, 0⟩, ?_, ?_, ?_⟩⟩
  · simp [finiteU3, horizontalPrimalEndpoints]
  · simp [finiteU3, horizontalPrimalEndpoints]
  · simp [face10, face00, HasDualEndpoints, horizontalDualEndpoints]

private theorem finiteU3_face11_face01_adj :
    (uuDualGraph finiteU3).Adj face11 face01 := by
  refine ⟨by simp [face11, face01], Or.inl ⟨⟨1, 1⟩, ?_, ?_, ?_⟩⟩
  · simp [finiteU3, horizontalPrimalEndpoints]
  · simp [finiteU3, horizontalPrimalEndpoints]
  · simp [face11, face01, HasDualEndpoints, horizontalDualEndpoints]

/-- The parent map for the five dual faces, rooted at the outside face. -/
def finiteU3Parent : GridFace 3 3 → GridFace 3 3
  | .out => .out
  | .cell r c =>
      if r.val = 0 then
        if c.val = 0 then .out else face00
      else if c.val = 0 then face00 else face01

/-- Manhattan rank shifted by one on cells, with rank zero at `out`. -/
def finiteU3Rank : GridFace 3 3 → Nat
  | .out => 0
  | .cell r c => r.val + c.val + 1

/-- The explicit ranked parent certificate for `finiteU3`. -/
def finiteU3RankedDualCertificate :
    RankedParentCertificate (uuDualGraph finiteU3) where
  root := .out
  parent := finiteU3Parent
  rank := finiteU3Rank
  parent_adj := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c
        · simpa [finiteU3Parent] using finiteU3_face00_out_adj
        · simpa [finiteU3Parent] using finiteU3_face01_face00_adj
        · simpa [finiteU3Parent] using finiteU3_face10_face00_adj
        · simpa [finiteU3Parent] using finiteU3_face11_face01_adj
  rank_parent_lt := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c <;>
          norm_num [finiteU3Parent, finiteU3Rank, face00, face01]

theorem finiteU3_compl_card :
    ((Finset.univ : Finset (GridVertex 3 3)) \ finiteU3).card = 4 := by
  have hcompl : (Finset.univ : Finset (GridVertex 3 3)) \ finiteU3 =
      {(0, 2), (2, 0), (2, 1), (2, 2)} := by
    ext v
    rcases v with ⟨r, c⟩
    fin_cases r <;> fin_cases c <;>
      simp [finiteU3, gridVertex_eq_iff]
  rw [hcompl]
  norm_num [Finset.card_insert_of_notMem, gridVertex_eq_iff]

/-- Four vertices can be preserved in the `3 x 3` grid. -/
theorem four_le_maxPreserved_three_three : 4 ≤ maxPreserved 3 3 := by
  rw [← finiteU3_compl_card]
  exact compl_card_le_maxPreserved_of_rankedDualCertificate
    (by norm_num) (by norm_num) finiteU3 finiteU3RankedDualCertificate

/-- The fourteen selected vertices in the `5 x 5` construction with row masks
`[16, 31, 13, 15, 8]`. -/
def finiteU5 : Finset (GridVertex 5 5) :=
  Finset.univ.filter fun v =>
    if v.1.val = 0 then v.2.val = 4
    else if v.1.val = 1 then True
    else if v.1.val = 2 then v.2.val = 0 ∨ v.2.val = 2 ∨ v.2.val = 3
    else if v.1.val = 3 then v.2.val ≤ 3
    else v.2.val = 3

private abbrev f5_00 : GridFace 5 5 := .cell 0 0
private abbrev f5_01 : GridFace 5 5 := .cell 0 1
private abbrev f5_02 : GridFace 5 5 := .cell 0 2
private abbrev f5_03 : GridFace 5 5 := .cell 0 3
private abbrev f5_10 : GridFace 5 5 := .cell 1 0
private abbrev f5_11 : GridFace 5 5 := .cell 1 1
private abbrev f5_12 : GridFace 5 5 := .cell 1 2
private abbrev f5_13 : GridFace 5 5 := .cell 1 3
private abbrev f5_20 : GridFace 5 5 := .cell 2 0
private abbrev f5_21 : GridFace 5 5 := .cell 2 1
private abbrev f5_22 : GridFace 5 5 := .cell 2 2
private abbrev f5_23 : GridFace 5 5 := .cell 2 3
private abbrev f5_30 : GridFace 5 5 := .cell 3 0
private abbrev f5_31 : GridFace 5 5 := .cell 3 1
private abbrev f5_32 : GridFace 5 5 := .cell 3 2
private abbrev f5_33 : GridFace 5 5 := .cell 3 3

private theorem horizontal_boundary_adj {U : Finset (GridVertex 5 5)}
    (e : HorizontalGridEdge 5 5) (x y : GridFace 5 5) (hne : x ≠ y)
    (hleft : (horizontalPrimalEndpoints e).1 ∈ U)
    (hright : (horizontalPrimalEndpoints e).2 ∈ U)
    (hdual : HasDualEndpoints (horizontalDualEndpoints e) x y) :
    (uuDualGraph U).Adj x y :=
  ⟨hne, Or.inl ⟨e, hleft, hright, hdual⟩⟩

private theorem vertical_boundary_adj {U : Finset (GridVertex 5 5)}
    (e : VerticalGridEdge 5 5) (x y : GridFace 5 5) (hne : x ≠ y)
    (htop : (verticalPrimalEndpoints e).1 ∈ U)
    (hbottom : (verticalPrimalEndpoints e).2 ∈ U)
    (hdual : HasDualEndpoints (verticalDualEndpoints e) x y) :
    (uuDualGraph U).Adj x y :=
  ⟨hne, Or.inr ⟨e, htop, hbottom, hdual⟩⟩

private theorem finiteU5_f03_out_adj :
    (uuDualGraph finiteU5).Adj f5_03 .out := by
  refine vertical_boundary_adj ⟨⟨0, by omega⟩, 4⟩ f5_03 .out (by simp) ?_ ?_ ?_
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [f5_03, HasDualEndpoints, verticalDualEndpoints]

private theorem finiteU5_f10_out_adj :
    (uuDualGraph finiteU5).Adj f5_10 .out := by
  refine vertical_boundary_adj ⟨⟨1, by omega⟩, 0⟩ f5_10 .out (by simp) ?_ ?_ ?_
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [f5_10, HasDualEndpoints, verticalDualEndpoints]

private theorem finiteU5_f20_out_adj :
    (uuDualGraph finiteU5).Adj f5_20 .out := by
  refine vertical_boundary_adj ⟨⟨2, by omega⟩, 0⟩ f5_20 .out (by simp) ?_ ?_ ?_
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [f5_20, HasDualEndpoints, verticalDualEndpoints]

private theorem finiteU5_f13_f03_adj :
    (uuDualGraph finiteU5).Adj f5_13 f5_03 := by
  refine horizontal_boundary_adj ⟨1, ⟨3, by omega⟩⟩ f5_13 f5_03 (by simp) ?_ ?_ ?_
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [f5_13, f5_03, HasDualEndpoints, horizontalDualEndpoints]

private theorem finiteU5_f00_f10_adj :
    (uuDualGraph finiteU5).Adj f5_00 f5_10 := by
  refine horizontal_boundary_adj ⟨1, ⟨0, by omega⟩⟩ f5_00 f5_10 (by simp) ?_ ?_ ?_
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [f5_00, f5_10, HasDualEndpoints, horizontalDualEndpoints]

private theorem finiteU5_f30_f20_adj :
    (uuDualGraph finiteU5).Adj f5_30 f5_20 := by
  refine horizontal_boundary_adj ⟨3, ⟨0, by omega⟩⟩ f5_30 f5_20 (by simp) ?_ ?_ ?_
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [f5_30, f5_20, HasDualEndpoints, horizontalDualEndpoints]

private theorem finiteU5_f12_f13_adj :
    (uuDualGraph finiteU5).Adj f5_12 f5_13 := by
  refine vertical_boundary_adj ⟨⟨1, by omega⟩, 3⟩ f5_12 f5_13 (by simp) ?_ ?_ ?_
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [f5_12, f5_13, HasDualEndpoints, verticalDualEndpoints]

private theorem finiteU5_f02_f12_adj :
    (uuDualGraph finiteU5).Adj f5_02 f5_12 := by
  refine horizontal_boundary_adj ⟨1, ⟨2, by omega⟩⟩ f5_02 f5_12 (by simp) ?_ ?_ ?_
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [f5_02, f5_12, HasDualEndpoints, horizontalDualEndpoints]

private theorem finiteU5_f11_f12_adj :
    (uuDualGraph finiteU5).Adj f5_11 f5_12 := by
  refine vertical_boundary_adj ⟨⟨1, by omega⟩, 2⟩ f5_11 f5_12 (by simp) ?_ ?_ ?_
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [f5_11, f5_12, HasDualEndpoints, verticalDualEndpoints]

private theorem finiteU5_f22_f12_adj :
    (uuDualGraph finiteU5).Adj f5_22 f5_12 := by
  refine horizontal_boundary_adj ⟨2, ⟨2, by omega⟩⟩ f5_22 f5_12 (by simp) ?_ ?_ ?_
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [f5_22, f5_12, HasDualEndpoints, horizontalDualEndpoints]

private theorem finiteU5_f01_f11_adj :
    (uuDualGraph finiteU5).Adj f5_01 f5_11 := by
  refine horizontal_boundary_adj ⟨1, ⟨1, by omega⟩⟩ f5_01 f5_11 (by simp) ?_ ?_ ?_
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [f5_01, f5_11, HasDualEndpoints, horizontalDualEndpoints]

private theorem finiteU5_f21_f22_adj :
    (uuDualGraph finiteU5).Adj f5_21 f5_22 := by
  refine vertical_boundary_adj ⟨⟨2, by omega⟩, 2⟩ f5_21 f5_22 (by simp) ?_ ?_ ?_
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [f5_21, f5_22, HasDualEndpoints, verticalDualEndpoints]

private theorem finiteU5_f23_f22_adj :
    (uuDualGraph finiteU5).Adj f5_23 f5_22 := by
  refine vertical_boundary_adj ⟨⟨2, by omega⟩, 3⟩ f5_23 f5_22 (by simp) ?_ ?_ ?_
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [f5_23, f5_22, HasDualEndpoints, verticalDualEndpoints]

private theorem finiteU5_f32_f22_adj :
    (uuDualGraph finiteU5).Adj f5_32 f5_22 := by
  refine horizontal_boundary_adj ⟨3, ⟨2, by omega⟩⟩ f5_32 f5_22 (by simp) ?_ ?_ ?_
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [f5_32, f5_22, HasDualEndpoints, horizontalDualEndpoints]

private theorem finiteU5_f31_f21_adj :
    (uuDualGraph finiteU5).Adj f5_31 f5_21 := by
  refine horizontal_boundary_adj ⟨3, ⟨1, by omega⟩⟩ f5_31 f5_21 (by simp) ?_ ?_ ?_
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [finiteU5, horizontalPrimalEndpoints]
  · simp [f5_31, f5_21, HasDualEndpoints, horizontalDualEndpoints]

private theorem finiteU5_f33_f32_adj :
    (uuDualGraph finiteU5).Adj f5_33 f5_32 := by
  refine vertical_boundary_adj ⟨⟨3, by omega⟩, 3⟩ f5_33 f5_32 (by simp) ?_ ?_ ?_
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [finiteU5, verticalPrimalEndpoints]
  · simp [f5_33, f5_32, HasDualEndpoints, verticalDualEndpoints]

/-- The requested parent tree on the sixteen bounded faces, rooted at `out`. -/
def finiteU5Parent : GridFace 5 5 → GridFace 5 5
  | .out => .out
  | .cell r c =>
      if r.val = 0 then
        if c.val = 0 then f5_10
        else if c.val = 1 then f5_11
        else if c.val = 2 then f5_12 else .out
      else if r.val = 1 then
        if c.val = 0 then .out
        else if c.val = 1 then f5_12
        else if c.val = 2 then f5_13 else f5_03
      else if r.val = 2 then
        if c.val = 0 then .out
        else if c.val = 1 then f5_22
        else if c.val = 2 then f5_12 else f5_22
      else
        if c.val = 0 then f5_20
        else if c.val = 1 then f5_21
        else if c.val = 2 then f5_22 else f5_32

/-- Explicit depths in `finiteU5Parent`, with rank zero at `out`. -/
def finiteU5Rank : GridFace 5 5 → Nat
  | .out => 0
  | .cell r c =>
      if r.val = 0 then
        if c.val = 0 then 2 else if c.val = 1 then 5 else if c.val = 2 then 4 else 1
      else if r.val = 1 then
        if c.val = 0 then 1 else if c.val = 1 then 4 else if c.val = 2 then 3 else 2
      else if r.val = 2 then
        if c.val = 0 then 1 else if c.val = 1 then 5 else if c.val = 2 then 4 else 5
      else
        if c.val = 0 then 2 else if c.val = 1 then 6 else if c.val = 2 then 5 else 6

/-- The explicit ranked parent certificate for the `5 x 5` row-mask witness. -/
def finiteU5RankedDualCertificate :
    RankedParentCertificate (uuDualGraph finiteU5) where
  root := .out
  parent := finiteU5Parent
  rank := finiteU5Rank
  parent_adj := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c
        · simpa [finiteU5Parent] using finiteU5_f00_f10_adj
        · simpa [finiteU5Parent] using finiteU5_f01_f11_adj
        · simpa [finiteU5Parent] using finiteU5_f02_f12_adj
        · simpa [finiteU5Parent] using finiteU5_f03_out_adj
        · simpa [finiteU5Parent] using finiteU5_f10_out_adj
        · simpa [finiteU5Parent] using finiteU5_f11_f12_adj
        · simpa [finiteU5Parent] using finiteU5_f12_f13_adj
        · simpa [finiteU5Parent] using finiteU5_f13_f03_adj
        · simpa [finiteU5Parent] using finiteU5_f20_out_adj
        · simpa [finiteU5Parent] using finiteU5_f21_f22_adj
        · simpa [finiteU5Parent] using finiteU5_f22_f12_adj
        · simpa [finiteU5Parent] using finiteU5_f23_f22_adj
        · simpa [finiteU5Parent] using finiteU5_f30_f20_adj
        · simpa [finiteU5Parent] using finiteU5_f31_f21_adj
        · simpa [finiteU5Parent] using finiteU5_f32_f22_adj
        · simpa [finiteU5Parent] using finiteU5_f33_f32_adj
  rank_parent_lt := by
    intro f hf
    cases f with
    | out => exact (hf rfl).elim
    | cell r c =>
        fin_cases r <;> fin_cases c <;>
          norm_num [finiteU5Parent, finiteU5Rank, f5_03, f5_10, f5_11, f5_12,
            f5_13, f5_20, f5_21, f5_22, f5_32]

theorem finiteU5_compl_card :
    ((Finset.univ : Finset (GridVertex 5 5)) \ finiteU5).card = 11 := by
  have hU : finiteU5.card = 14 := by
    rfl
  rw [Finset.card_sdiff, Finset.inter_univ, hU]
  change 25 - 14 = 11
  norm_num

/-- Eleven vertices can be preserved in the `5 x 5` grid. -/
theorem eleven_le_maxPreserved_five_five : 11 ≤ maxPreserved 5 5 := by
  rw [← finiteU5_compl_card]
  exact compl_card_le_maxPreserved_of_rankedDualCertificate
    (by norm_num) (by norm_num) finiteU5 finiteU5RankedDualCertificate

end GridGraphs
