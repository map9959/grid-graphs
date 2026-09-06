import GridGraphs.ResidueZeroAnchored
import GridGraphs.ResidueZeroTransitions

namespace GridGraphs

open SimpleGraph

private def table (xs : List Nat) (c fallback : Nat) : Nat :=
  xs[c]?.getD fallback

/-- Direction of the explicit width-seven parent: up, down, left, right, root
are encoded by `0,1,2,3,4`.  The rows are the two boundary intervals around
the seventeen rows of `phaseRowsBase`; within a row the entries are grouped by
`q = c / 3` and `c % 3`. -/
def residueZeroBaseParentDirection (r c : Nat) : Nat :=
  match r with
  | 1 => table [3,1,2, 3,1,2, 3,1,2, 3,1,2, 3,3,1, 1,2,3, 1,2] c 4
  | 2 => table [3,1,2, 3,1,2, 3,1,2, 3,3,1, 3,0,3, 1,2,3, 1,2] c 4
  | 3 => table [3,1,2, 3,1,2, 3,3,1, 3,0,3, 0,2,3, 1,2,3, 1,2] c 4
  | 4 => table [3,1,2, 3,1,2, 3,0,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 5 => table [3,1,2, 3,3,1, 1,2,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 6 => table [3,3,1, 3,0,3, 1,2,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 7 => table [3,0,3, 0,2,3, 1,2,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 8 => table [3,1,3, 0,2,3, 1,2,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 9 => table [3,3,0, 0,2,3, 1,2,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 10 => table [3,0,2, 3,1,3, 1,2,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 11 => table [3,0,2, 3,3,0, 3,1,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 12 => table [3,0,2, 3,0,2, 3,3,0, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 13 => table [3,0,2, 3,0,2, 3,0,2, 3,1,3, 0,2,3, 1,2,3, 1,2] c 4
  | 14 => table [3,0,2, 3,0,2, 3,0,2, 3,3,0, 0,2,3, 1,2,3, 1,2] c 4
  | 15 => table [3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,1,3, 1,2,3, 1,2] c 4
  | 16 => table [3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,3,0, 3,1,3, 1,2] c 4
  | 17 => table [3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,3,0, 3,1] c 4
  | 18 => table [3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,4] c 4
  | _ => 4

/-- The explicit parent on the bounded `20 x 20` face-coordinate square. -/
def residueZeroBaseParent
    (x : Fin (3 * 7 - 1) × Fin (3 * 7 - 1)) :
    Fin (3 * 7 - 1) × Fin (3 * 7 - 1) :=
  let r := x.1.val
  let c := x.2.val
  match residueZeroBaseParentDirection r c with
  | 0 => if h : 0 < r then (⟨r - 1, by omega⟩, x.2) else x
  | 1 => if h : r + 1 < 3 * 7 - 1 then (⟨r + 1, h⟩, x.2) else x
  | 2 => if h : 0 < c then (x.1, ⟨c - 1, by omega⟩) else x
  | 3 => if h : c + 1 < 3 * 7 - 1 then (x.1, ⟨c + 1, h⟩) else x
  | _ => x

/-- Exact distance along the parent tree to `(18,19)`. -/
def residueZeroBaseRank (x : Fin (3 * 7 - 1) × Fin (3 * 7 - 1)) : Nat :=
  let r := x.1.val
  let c := x.2.val
  match r with
  | 1 => table [66,65,66,59,58,59,40,39,40,33,32,33,26,25,24,23,24,19,18,19] c 0
  | 2 => table [65,64,65,58,57,58,39,38,39,32,31,30,27,26,23,22,23,18,17,18] c 0
  | 3 => table [64,63,64,57,56,57,38,37,36,33,32,29,28,29,22,21,22,17,16,17] c 0
  | 4 => table [63,62,63,56,55,56,39,38,35,34,35,30,29,30,21,20,21,16,15,16] c 0
  | 5 => table [62,61,62,55,54,53,52,53,36,35,36,31,30,31,20,19,20,15,14,15] c 0
  | 6 => table [61,60,59,56,55,52,51,52,37,36,37,32,31,32,19,18,19,14,13,14] c 0
  | 7 => table [62,61,58,57,58,51,50,51,38,37,38,33,32,33,18,17,18,13,12,13] c 0
  | 8 => table [63,62,59,58,59,50,49,50,39,38,39,34,33,34,17,16,17,12,11,12] c 0
  | 9 => table [62,61,60,59,60,49,48,49,40,39,40,35,34,35,16,15,16,11,10,11] c 0
  | 10 => table [63,62,63,52,51,48,47,48,41,40,41,36,35,36,15,14,15,10,9,10] c 0
  | 11 => table [64,63,64,51,50,49,46,45,42,41,42,37,36,37,14,13,14,9,8,9] c 0
  | 12 => table [65,64,65,52,51,52,45,44,43,42,43,38,37,38,13,12,13,8,7,8] c 0
  | 13 => table [66,65,66,53,52,53,46,45,46,43,42,39,38,39,12,11,12,7,6,7] c 0
  | 14 => table [67,66,67,54,53,54,47,46,47,42,41,40,39,40,11,10,11,6,5,6] c 0
  | 15 => table [68,67,68,55,54,55,48,47,48,43,42,43,14,13,10,9,10,5,4,5] c 0
  | 16 => table [69,68,69,56,55,56,49,48,49,44,43,44,13,12,11,8,7,4,3,4] c 0
  | 17 => table [70,69,70,57,56,57,50,49,50,45,44,45,14,13,14,7,6,5,2,1] c 0
  | 18 => table [71,70,71,58,57,58,51,50,51,46,45,46,15,14,15,8,7,8,1,0] c 0
  | _ => 0

set_option maxHeartbeats 2000000 in
theorem residueZeroBase_root_or_rank_parent_lt
    (x : Fin (3 * 7 - 1) × Fin (3 * 7 - 1)) :
    ¬ (0 < x.1.val ∧ x.1.val < 3 * 7 - 2) ∨
    x = residueZeroAnchorCoord 7 (by omega) ∨
      residueZeroBaseRank (residueZeroBaseParent x) < residueZeroBaseRank x := by
  rcases x with ⟨r, c⟩
  fin_cases r
  all_goals fin_cases c
  all_goals decide

theorem residueZeroBaseRank_parent_lt
    (x : Fin (3 * 7 - 1) × Fin (3 * 7 - 1))
    (hr0 : 0 < x.1.val) (hrlast : x.1.val < 3 * 7 - 2)
    (hne : x ≠ residueZeroAnchorCoord 7 (by omega)) :
    residueZeroBaseRank (residueZeroBaseParent x) < residueZeroBaseRank x := by
  rcases residueZeroBase_root_or_rank_parent_lt x with h | h | h
  · exact (h ⟨hr0, hrlast⟩).elim
  · exact (hne h).elim
  · exact h

private theorem base_phase_row_step (i : Fin (phaseRows 7).length) (c : Nat)
    (hc : c < 3 * 7 - 1)
    (hleft : PhaseOccupied 7 ((phaseRows 7).get i) c)
    (hright : PhaseOccupied 7 ((phaseRows 7).get i) (c + 1)) :
    (widenableOldDualGraph 7 (by omega)).Adj
      (⟨i.val + 1, by have := i.isLt; simp [phaseRows_length 7 (by omega)] at this; omega⟩,
        ⟨c, hc⟩)
      (⟨i.val + 2, by have := i.isLt; simp [phaseRows_length 7 (by omega)] at this; omega⟩,
        ⟨c, hc⟩) := by
  constructor
  · exact horizontal_uu_dual_cells_adj _ (i.val + 2) c (by omega) (by
      have := i.isLt
      simp [phaseRows_length 7 (by omega)] at this
      omega) hc
      (phase_occupied_mem_uResidueZero 7 (by omega) i c hleft)
      (phase_occupied_mem_uResidueZero 7 (by omega) i (c + 1) hright)
  · exact old_phase_horizontal_dual_adj_widened 7 (by omega) i c hc hleft hright

private theorem base_between_rows_step (i c : Nat)
    (hi : i + 1 < (phaseRows 7).length) (hc : c + 1 < 3 * 7 - 1)
    (htop : PhaseOccupied 7 ((phaseRows 7)[i]'(by omega)) (c + 1))
    (hbottom : PhaseOccupied 7 ((phaseRows 7)[i + 1]'hi) (c + 1)) :
    (widenableOldDualGraph 7 (by omega)).Adj
      (⟨i + 2, by rw [phaseRows_length 7 (by omega)] at hi; omega⟩, ⟨c, by omega⟩)
      (⟨i + 2, by rw [phaseRows_length 7 (by omega)] at hi; omega⟩, ⟨c + 1, hc⟩) := by
  constructor
  · simpa using consecutive_phase_common_column_dual_adj 7 (by omega) i hi (c + 1)
      (by omega) hc
      ⟨htop, hbottom⟩
  · simpa using old_phase_vertical_dual_adj_widened 7 (by omega) i hi (c + 1)
      (by omega) hc htop hbottom

private theorem base_top_interface_step (c : Nat) (hc : c + 1 < 3 * 7 - 1)
    (hphase7 : PhaseOccupied 7 (.ordinary 4) (c + 1))
    (hseam8 : PhaseOccupied 8 (.seam 5) (c + 1))
    (hphase8 : PhaseOccupied 8 (.ordinary 4) (c + 1)) :
    (widenableOldDualGraph 7 (by omega)).Adj
      (⟨1, by omega⟩, ⟨c, by omega⟩) (⟨1, by omega⟩, ⟨c + 1, hc⟩) := by
  constructor
  · exact vertical_uu_dual_cells_adj _ 1 (c + 1) (by omega) (by omega) hc
      (all_cap_mem_uResidueZero 7 (by omega) (c + 1) (by omega))
      (by simpa [phaseRows, phaseRowsFrom, phaseRowsBase] using
        phase_occupied_mem_uResidueZero 7 (by omega) ⟨0, by norm_num [phaseRows,
          phaseRowsFrom, phaseRowsBase]⟩ (c + 1) hphase7)
  · exact vertical_uu_dual_cells_adj _ 3 (c + 1) (by omega) (by omega) (by omega)
      (by simpa [phaseRows, phaseRowsFrom, phaseRowsBase] using
        phase_occupied_mem_uResidueZero 8 (by omega) ⟨1, by norm_num [phaseRows,
          phaseRowsFrom, phaseRowsBase]⟩ (c + 1) hseam8)
      (by simpa [phaseRows, phaseRowsFrom, phaseRowsBase] using
        phase_occupied_mem_uResidueZero 8 (by omega) ⟨2, by norm_num [phaseRows,
          phaseRowsFrom, phaseRowsBase]⟩ (c + 1) hphase8)

private theorem base_bottom_interface_step (c : Nat) (hc : c + 1 < 3 * 7 - 1)
    (hphase7 : PhaseOccupied 7 (.ordinary 6) (c + 1))
    (hphase8 : PhaseOccupied 8 (.ordinary 6) (c + 1))
    (happended8 : PhaseOccupied 8 (.ordinary 7) (c + 1)) :
    (widenableOldDualGraph 7 (by omega)).Adj
      (⟨18, by omega⟩, ⟨c, by omega⟩) (⟨18, by omega⟩, ⟨c + 1, hc⟩) := by
  constructor
  · exact vertical_uu_dual_cells_adj _ 18 (c + 1) (by omega) (by omega) hc
      (by simpa [phaseRows, phaseRowsFrom, phaseRowsBase] using
        phase_occupied_mem_uResidueZero 7 (by omega) ⟨16, by norm_num [phaseRows,
          phaseRowsFrom, phaseRowsBase]⟩ (c + 1) hphase7)
      (penultimate_cap_mem_uResidueZero 7 (by omega) (c + 1) (by omega) (by omega))
  · exact vertical_uu_dual_cells_adj _ 20 (c + 1) (by omega) (by omega) (by omega)
      (by simpa [phaseRows, phaseRowsFrom, phaseRowsBase] using
        phase_occupied_mem_uResidueZero 8 (by omega) ⟨18, by norm_num [phaseRows,
          phaseRowsFrom, phaseRowsBase]⟩ (c + 1) hphase8)
      (by simpa [phaseRows, phaseRowsFrom, phaseRowsBase] using
        phase_occupied_mem_uResidueZero 8 (by omega) ⟨19, by norm_num [phaseRows,
          phaseRowsFrom, phaseRowsBase]⟩ (c + 1) happended8)

set_option maxHeartbeats 4000000 in
theorem residueZeroBaseParent_adj
    (x : Fin (3 * 7 - 1) × Fin (3 * 7 - 1))
    (hr0 : 0 < x.1.val) (hrlast : x.1.val < 3 * 7 - 2)
    (hne : x ≠ residueZeroAnchorCoord 7 (by omega)) :
    (widenableOldDualGraph 7 (by omega)).Adj x (residueZeroBaseParent x) := by
  rcases x with ⟨r, c⟩
  fin_cases r
  all_goals fin_cases c
  all_goals try { norm_num at hr0 }
  all_goals try { norm_num at hrlast }
  all_goals simp [residueZeroAnchorCoord] at hne
  all_goals dsimp [residueZeroBaseParent, residueZeroBaseParentDirection, table]
  all_goals have hlen : (phaseRows 7).length = 17 := by norm_num [phaseRows,
    phaseRowsFrom, phaseRowsBase]
  all_goals first
    | apply base_phase_row_step ⟨0, by omega⟩
    | apply (base_phase_row_step ⟨0, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨1, by omega⟩
    | apply (base_phase_row_step ⟨1, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨2, by omega⟩
    | apply (base_phase_row_step ⟨2, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨3, by omega⟩
    | apply (base_phase_row_step ⟨3, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨4, by omega⟩
    | apply (base_phase_row_step ⟨4, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨5, by omega⟩
    | apply (base_phase_row_step ⟨5, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨6, by omega⟩
    | apply (base_phase_row_step ⟨6, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨7, by omega⟩
    | apply (base_phase_row_step ⟨7, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨8, by omega⟩
    | apply (base_phase_row_step ⟨8, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨9, by omega⟩
    | apply (base_phase_row_step ⟨9, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨10, by omega⟩
    | apply (base_phase_row_step ⟨10, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨11, by omega⟩
    | apply (base_phase_row_step ⟨11, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨12, by omega⟩
    | apply (base_phase_row_step ⟨12, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨13, by omega⟩
    | apply (base_phase_row_step ⟨13, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨14, by omega⟩
    | apply (base_phase_row_step ⟨14, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨15, by omega⟩
    | apply (base_phase_row_step ⟨15, by omega⟩ _ _ _ _).symm
    | apply base_phase_row_step ⟨16, by omega⟩
    | apply (base_phase_row_step ⟨16, by omega⟩ _ _ _ _).symm
    | apply base_between_rows_step 0
    | apply (base_between_rows_step 0 _ _ _ _ _).symm
    | apply base_between_rows_step 1
    | apply (base_between_rows_step 1 _ _ _ _ _).symm
    | apply base_between_rows_step 2
    | apply (base_between_rows_step 2 _ _ _ _ _).symm
    | apply base_between_rows_step 3
    | apply (base_between_rows_step 3 _ _ _ _ _).symm
    | apply base_between_rows_step 4
    | apply (base_between_rows_step 4 _ _ _ _ _).symm
    | apply base_between_rows_step 5
    | apply (base_between_rows_step 5 _ _ _ _ _).symm
    | apply base_between_rows_step 6
    | apply (base_between_rows_step 6 _ _ _ _ _).symm
    | apply base_between_rows_step 7
    | apply (base_between_rows_step 7 _ _ _ _ _).symm
    | apply base_between_rows_step 8
    | apply (base_between_rows_step 8 _ _ _ _ _).symm
    | apply base_between_rows_step 9
    | apply (base_between_rows_step 9 _ _ _ _ _).symm
    | apply base_between_rows_step 10
    | apply (base_between_rows_step 10 _ _ _ _ _).symm
    | apply base_between_rows_step 11
    | apply (base_between_rows_step 11 _ _ _ _ _).symm
    | apply base_between_rows_step 12
    | apply (base_between_rows_step 12 _ _ _ _ _).symm
    | apply base_between_rows_step 13
    | apply (base_between_rows_step 13 _ _ _ _ _).symm
    | apply base_between_rows_step 14
    | apply (base_between_rows_step 14 _ _ _ _ _).symm
    | apply base_between_rows_step 15
    | apply (base_between_rows_step 15 _ _ _ _ _).symm
    | apply base_top_interface_step
    | apply (base_top_interface_step _ _ _ _ _).symm
    | apply base_bottom_interface_step
    | apply (base_bottom_interface_step _ _ _ _ _).symm
  all_goals dsimp [phaseRows, phaseRowsFrom, phaseRowsBase]
  all_goals try omega
  all_goals unfold PhaseOccupied
  all_goals decide

set_option maxHeartbeats 2000000 in
private theorem residueZeroBaseParent_interior
    (x : Fin (3 * 7 - 1) × Fin (3 * 7 - 1))
    (hr0 : 0 < x.1.val) (hrlast : x.1.val < 3 * 7 - 2) :
    0 < (residueZeroBaseParent x).1.val ∧
      (residueZeroBaseParent x).1.val < 3 * 7 - 2 := by
  rcases x with ⟨r, c⟩
  revert hr0 hrlast
  fin_cases r
  all_goals fin_cases c
  all_goals decide

/-- Every interior width-seven face has a stable path to the designated anchor. -/
theorem residueZeroAnchorBasePaths : ResidueZeroAnchorBasePaths := by
  intro r hr0 hrlast c
  let x : Fin (3 * 7 - 1) × Fin (3 * 7 - 1) := (r, c)
  have main : ∀ n x, residueZeroBaseRank x = n →
      0 < x.1.val → x.1.val < 3 * 7 - 2 →
      (widenableOldDualGraph 7 (by omega)).Reachable x
        (residueZeroAnchorCoord 7 (by omega)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro y hyrank hy0 hylast
        by_cases hanchor : y = residueZeroAnchorCoord 7 (by omega)
        · simp [hanchor]
        · have hlt := residueZeroBaseRank_parent_lt y hy0 hylast hanchor
          have hinterior := residueZeroBaseParent_interior y hy0 hylast
          exact (residueZeroBaseParent_adj y hy0 hylast hanchor).reachable.trans
            (ih (residueZeroBaseRank (residueZeroBaseParent y)) (by omega)
              (residueZeroBaseParent y) rfl hinterior.1 hinterior.2)
  exact main (residueZeroBaseRank x) x rfl hr0 hrlast

/-- The width-seven anchored certificate, with no computational oracle or
external base-case hypothesis. -/
theorem residueZeroAnchoredCertificate_seven_base :
    ResidueZeroAnchoredCertificate 7 (by omega) :=
  residueZeroAnchoredCertificate_seven residueZeroAnchorBasePaths

end GridGraphs
