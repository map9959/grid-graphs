import GridGraphs.Constructions.ResidueTwo.ResidueTwoStableCap

/-!
# Dual connectivity failure for the stable residue-two cap

Deleting the cap vertex `(1,13+3j)` isolates both top faces adjacent to it.
Thus every positive pump depth is disconnected; the inserted bridge at row
five does not repair this top-boundary obstruction.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 4000000

/-- No vertex in row zero at or to the right of column twelve belongs to the
stable-cap pattern. -/
private theorem residueTwoStableCap_top_row_not_mem (t : Nat)
    (c : Fin (20 + 3 * t)) (hc : 12 ≤ c.val) :
    (⟨0, by omega⟩, c) ∉ residueTwoStableCapAt t := by
  classical
  intro h
  have hu := (Finset.mem_sdiff.mp h).1
  rcases Finset.mem_union.mp hu with hraw | hbridge
  · obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hraw
    have hr := congrArg (fun z => z.1.val) hx
    have hcol := congrArg (fun z => z.2.val) hx
    simp only [residueTwoExactVertex] at hr hcol
    have hrow : x.1.val = 0 := by
      by_cases hp : 5 ≤ x.1.val ∧ x.1.val < 5 + 3
      · rw [residueTwoExactExpandIndex_of_pump 5 t (by omega) _ hp] at hr
        simp only at hr
        omega
      · by_cases ha : 5 + 3 ≤ x.1.val
        · rw [residueTwoExactExpandIndex_of_above 5 t (by omega) _ hp ha] at hr
          simp only at hr
          omega
        · rw [residueTwoExactExpandIndex_of_below 5 t (by omega) _ hp ha] at hr
          simp only at hr
          omega
    have hbase := x.2.2.property
    have hbasecol : x.2.1.val = 1 := by
      simpa [IsResidueTwoExactBase, residueTwoExactBaseRow, hrow] using hbase
    have hp : ¬(11 ≤ x.2.1.val ∧ x.2.1.val < 11 + 3) := by omega
    have ha : ¬11 + 3 ≤ x.2.1.val := by omega
    rw [residueTwoExactExpandIndex_of_below 11 t (by omega) _ hp ha] at hcol
    simp only at hcol
    omega
  · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hbridge
    have hr := congrArg (fun z => z.1.val) hj
    simp [residueTwoStableBridgeVertex] at hr

/-- The cap coordinate itself is absent from the stable-cap pattern. -/
private theorem residueTwoStableCap_vertex_not_mem (t : Nat) (j : Fin t) :
    residueTwoStableCapVertex t j ∉ residueTwoStableCapAt t := by
  intro h
  exact (Finset.mem_sdiff.mp h).2
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

/-- Either top cell adjacent to a deleted cap vertex has no incident dual
edge. -/
private theorem residueTwoStableCap_top_face_not_adj (t : Nat) (j : Fin t)
    (c : Fin (20 + 3 * t - 1))
    (hc : c.val = 12 + 3 * j.val ∨ c.val = 13 + 3 * j.val)
    (y : GridFace (20 + 3 * t) (20 + 3 * t)) :
    ¬(uuDualGraph (residueTwoStableCapAt t)).Adj
      (.cell ⟨0, by omega⟩ c) y := by
  intro h
  rcases h.2 with hhorizontal | hvertical
  · obtain ⟨e, he₁, he₂, hends⟩ := hhorizontal
    rcases hends with hends | hends
    · by_cases htop : e.row.val = 0
      · simp [horizontalDualEndpoints, htop] at hends
      · have hr := congrArg (fun f => match f with
            | .out => 0
            | .cell r _ => r.val + 1) hends.1
        have hcol := congrArg (fun f => match f with
            | .out => 0
            | .cell _ col => col.val) hends.1
        simp [horizontalDualEndpoints, htop] at hr hcol
        rcases hc with hc | hc
        · apply residueTwoStableCap_vertex_not_mem t j
          have heq : (horizontalPrimalEndpoints e).2 =
              residueTwoStableCapVertex t j := by
            apply Prod.ext <;> apply Fin.ext <;>
              simp [horizontalPrimalEndpoints, residueTwoStableCapVertex] <;> omega
          rwa [heq] at he₂
        · apply residueTwoStableCap_vertex_not_mem t j
          have heq : (horizontalPrimalEndpoints e).1 =
              residueTwoStableCapVertex t j := by
            apply Prod.ext <;> apply Fin.ext <;>
              simp [horizontalPrimalEndpoints, residueTwoStableCapVertex] <;> omega
          rwa [heq] at he₁
    · by_cases hbottom : e.row.val + 1 = 20 + 3 * t
      · simp [horizontalDualEndpoints, hbottom] at hends
      · have hr := congrArg (fun f => match f with
            | .out => 1
            | .cell r _ => r.val) hends.1
        have hcol := congrArg (fun f => match f with
            | .out => 0
            | .cell _ col => col.val) hends.1
        simp [horizontalDualEndpoints, hbottom] at hr hcol
        have herow : e.row.val = 0 := by omega
        have hecol : e.col.val = c.val := by omega
        have hnot := residueTwoStableCap_top_row_not_mem t
          (⟨c.val, by have := c.isLt; omega⟩ : Fin (20 + 3 * t))
          (by change 12 ≤ c.val; rcases hc with hc | hc <;> omega)
        apply hnot
        have heq : (horizontalPrimalEndpoints e).1 =
            (⟨0, by omega⟩, ⟨c.val, by have := c.isLt; omega⟩) := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [horizontalPrimalEndpoints, herow, hecol]
        rwa [heq] at he₁
  · obtain ⟨e, he₁, he₂, hends⟩ := hvertical
    rcases hends with hends | hends
    · by_cases hleft : e.col.val = 0
      · simp [verticalDualEndpoints, hleft] at hends
      · have hr := congrArg (fun f => match f with
            | .out => 1
            | .cell r _ => r.val) hends.1
        have hcol := congrArg (fun f => match f with
            | .out => 0
            | .cell _ col => col.val + 1) hends.1
        simp [verticalDualEndpoints, hleft] at hr hcol
        have herow : e.row.val = 0 := by omega
        have hecol : e.col.val = c.val + 1 := by omega
        have hnot := residueTwoStableCap_top_row_not_mem t e.col
          (by rcases hc with hc | hc <;> omega)
        apply hnot
        have heq : (verticalPrimalEndpoints e).1 =
            (⟨0, by omega⟩, e.col) := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [verticalPrimalEndpoints, herow]
        rwa [heq] at he₁
    · by_cases hright : e.col.val + 1 = 20 + 3 * t
      · simp [verticalDualEndpoints, hright] at hends
      · have hr := congrArg (fun f => match f with
            | .out => 1
            | .cell r _ => r.val) hends.1
        have hcol := congrArg (fun f => match f with
            | .out => 0
            | .cell _ col => col.val) hends.1
        simp [verticalDualEndpoints, hright] at hr hcol
        have herow : e.row.val = 0 := by omega
        have hecol : e.col.val = c.val := by omega
        have hnot := residueTwoStableCap_top_row_not_mem t e.col
          (by rcases hc with hc | hc <;> omega)
        apply hnot
        have heq : (verticalPrimalEndpoints e).1 =
            (⟨0, by omega⟩, e.col) := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [verticalPrimalEndpoints, herow]
        rwa [heq] at he₁

/-- At every positive depth, the two top faces adjacent to each deleted cap
vertex are isolated in the U-U dual graph. -/
theorem residueTwoStableCap_top_faces_isolated (t : Nat) (j : Fin t) :
    (∀ y, ¬(uuDualGraph (residueTwoStableCapAt t)).Adj
      (.cell ⟨0, by omega⟩
        ⟨12 + 3 * j.val, by have := j.isLt; omega⟩) y) ∧
    (∀ y, ¬(uuDualGraph (residueTwoStableCapAt t)).Adj
      (.cell ⟨0, by omega⟩
        ⟨13 + 3 * j.val, by have := j.isLt; omega⟩) y) := by
  constructor
  · exact residueTwoStableCap_top_face_not_adj t j _ (Or.inl rfl)
  · exact residueTwoStableCap_top_face_not_adj t j _ (Or.inr rfl)

/-- Every positive pump depth has disconnected U-U dual graph. -/
theorem residueTwoStableCapAt_not_connected (t : Nat) (ht : 0 < t) :
    ¬(uuDualGraph (residueTwoStableCapAt t)).Connected := by
  let j : Fin t := ⟨0, ht⟩
  let left : GridFace (20 + 3 * t) (20 + 3 * t) :=
    .cell ⟨0, by omega⟩ ⟨12 + 3 * j.val, by have := j.isLt; omega⟩
  let right : GridFace (20 + 3 * t) (20 + 3 * t) :=
    .cell ⟨0, by omega⟩ ⟨13 + 3 * j.val, by have := j.isLt; omega⟩
  have hisolated : ∀ y, ¬(uuDualGraph (residueTwoStableCapAt t)).Adj left y := by
    simpa [left] using (residueTwoStableCap_top_faces_isolated t j).1
  have hne : left ≠ right := by simp [left, right]
  intro hconnected
  have hreachable := hconnected left right
  have hsupport := SimpleGraph.mem_support_of_reachable hne hreachable
  obtain ⟨y, hy⟩ := (SimpleGraph.mem_support _).mp hsupport
  exact hisolated y hy

/-- Pump depth zero is the connected twenty-by-twenty base certificate. -/
theorem residueTwoStableCapAt_zero_connected :
    (uuDualGraph (residueTwoStableCapAt 0)).Connected := by
  have hzero : residueTwoStableCapAt 0 = uResidueTwoExact 6 := by
    classical
    rw [residueTwoStableCapAt_zero]
    ext v
    simp [residueTwoExactOccurrenceImage, uResidueTwoExact]
  rw [hzero]
  exact uResidueTwoExact_six_dual_connected

/-- The stable-cap candidate has connected U-U dual exactly before any cap is
deleted. -/
theorem residueTwoStableCapAt_connected_iff (t : Nat) :
    (uuDualGraph (residueTwoStableCapAt t)).Connected ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    exact residueTwoStableCapAt_not_connected t (Nat.pos_of_ne_zero ht) h
  · rintro rfl
    exact residueTwoStableCapAt_zero_connected

end GridGraphs
