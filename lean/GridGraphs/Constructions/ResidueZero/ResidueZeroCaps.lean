import GridGraphs.Constructions.ResidueZero.ResidueZeroDual

/-!
# Cap edges of the residue-zero construction

The four cap rows are the empty top row, the all-U row below it, the dense
penultimate row, and the singleton bottom row.  This file records their local
dual geometry independently of the phase-word frontier argument.
-/

namespace GridGraphs

open SimpleGraph

/-- The first cap row is empty. -/
theorem empty_cap_not_mem_uResidueZero (k : Nat) (hk : 7 ≤ k) (c : Nat)
    (hc : c < 3 * k) :
    ((⟨0, by omega⟩, ⟨c, hc⟩) : GridVertex (3 * k) (3 * k)) ∉
      uResidueZero k hk := by
  rw [uResidueZero, Finset.mem_image]
  rintro ⟨i, -, hi⟩
  have hrow := congrArg (fun v => v.1.val) hi
  rcases i with c | i
  · simp [residueZeroVertex] at hrow
  · rcases i with c | i
    · simp [residueZeroVertex] at hrow
      omega
    · rcases i with c | i
      · simp [residueZeroVertex] at hrow
        omega
      · rcases i with ⟨r, j⟩
        simp [residueZeroVertex] at hrow

/-- A U-U vertical primal edge on the right boundary joins its left face to
the unbounded face. -/
theorem vertical_uu_dual_right_out_adj {N : Nat}
    (U : Finset (GridVertex N N)) (r : Nat)
    (hN : 2 ≤ N) (hr : r < N - 1)
    (ht : ((⟨r, by omega⟩, ⟨N - 1, by omega⟩) : GridVertex N N) ∈ U)
    (hb : ((⟨r + 1, by omega⟩, ⟨N - 1, by omega⟩) : GridVertex N N) ∈ U) :
    (uuDualGraph U).Adj
      (.cell ⟨r, hr⟩ ⟨N - 2, by omega⟩) .out := by
  let e : VerticalGridEdge N N := ⟨⟨r, hr⟩, ⟨N - 1, by omega⟩⟩
  refine ⟨by simp, Or.inr ⟨e, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩⟩
  · simpa [e, verticalPrimalEndpoints] using ht
  · simpa [e, verticalPrimalEndpoints] using hb
  · simp [e, verticalDualEndpoints, show N - 1 ≠ 0 by omega]
    omega
  · simp [e, verticalDualEndpoints]
    omega

/-- The final row of the recursively defined phase word is `R_(t+6)`. -/
theorem phaseRowsFrom_getLast (t : Nat) :
    (phaseRowsFrom t).getLast (by cases t <;> simp [phaseRowsFrom, phaseRowsBase]) =
      .ordinary (t + 6) := by
  cases t with
  | zero => decide
  | succ t => simp [phaseRowsFrom]

/-- The final phase row in `B_k` is `R_(k-1)`. -/
theorem phaseRows_getLast (k : Nat) (hk : 7 ≤ k) :
    (phaseRows k).getLast (List.ne_nil_of_length_pos (by
      rw [phaseRows_length k hk]
      omega)) =
      .ordinary (k - 1) := by
  have h := phaseRowsFrom_getLast (k - 7)
  have ha : k - 7 + 6 = k - 1 := by omega
  simpa only [phaseRows, if_pos hk, ha] using h

private theorem phaseColumn_final_ordinary (k : Nat) (hk : 7 ≤ k)
    (row : PhaseRow) (hrow : row = .ordinary (k - 1))
    (j : PhaseSlot k row) (hj : j.val = 2 * k - 1) :
    phaseColumn k row j = 3 * k - 1 := by
  subst row
  simp only [phaseColumn]
  rw [hj]
  by_cases h₁ : 2 * k - 1 < k
  · simp [h₁]
    omega
  · by_cases h₂ : 2 * k - 1 < k + (k - 1) + 1
    · simp [h₁, h₂]
      omega
    · simp [h₁, h₂]
      omega

/-- The rightmost vertex in the final phase row belongs to U. -/
theorem final_phase_right_mem_uResidueZero (k : Nat) (hk : 7 ≤ k) :
    ((⟨3 * k - 3, by omega⟩, ⟨3 * k - 1, by omega⟩) :
      GridVertex (3 * k) (3 * k)) ∈ uResidueZero k hk := by
  let i : Fin (phaseRows k).length := ⟨(phaseRows k).length - 1, by
    rw [phaseRows_length k hk]
    omega⟩
  have hi : (phaseRows k).get i = .ordinary (k - 1) := by
    rw [List.get_eq_getElem]
    rw [← List.getLast_eq_getElem (List.ne_nil_of_length_pos (by
      rw [phaseRows_length k hk]
      omega))]
    exact phaseRows_getLast k hk
  let j : PhaseSlot k ((phaseRows k).get i) := ⟨2 * k - 1, by
    rw [hi]
    simp [phaseSlotCount]
    omega⟩
  have hj : phaseColumn k ((phaseRows k).get i) j = 3 * k - 1 :=
    phaseColumn_final_ordinary k hk _ hi j rfl
  have hm := phase_vertex_mem_uResidueZero k hk i j
  have hiVal : i.val = 3 * k - 5 := by
    simp [i, phaseRows_length k hk]
    omega
  have hv :
      ((⟨3 * k - 3, by omega⟩, ⟨3 * k - 1, by omega⟩) :
        GridVertex (3 * k) (3 * k)) =
      (⟨i.val + 2, by omega⟩, ⟨phaseColumn k ((phaseRows k).get i) j, by
        exact phaseColumn_lt
          (phaseRows_parameter_lt k hk _ (List.get_mem (phaseRows k) i)) j⟩) := by
    apply Prod.ext
    · apply Fin.ext
      simp [hiVal]
      omega
    · apply Fin.ext
      exact hj.symm
  rw [hv]
  exact hm

/-- Every face under the empty top row is joined through the all-U row to the
corresponding face on the initial interior frontier. -/
theorem initial_cap_face_adj_interior_frontier (k : Nat) (hk : 7 ≤ k)
    (c : Nat) (hc : c < 3 * k - 1) :
    (uuDualGraph (uResidueZero k hk)).Adj
      (.cell ⟨0, by omega⟩ ⟨c, hc⟩)
      (.cell ⟨1, by omega⟩ ⟨c, hc⟩) := by
  exact horizontal_uu_dual_cells_adj (uResidueZero k hk) 1 c
    (by omega) (by omega) hc
    (all_cap_mem_uResidueZero k hk c (by omega))
    (all_cap_mem_uResidueZero k hk (c + 1) (by omega))

/-- Reachability of the initial interior frontier propagates across the top
cap to every bounded face in the first face row. -/
theorem initial_cap_face_reachable_out (k : Nat) (hk : 7 ≤ k)
    (hfrontier : ∀ c : Fin (3 * k - 1),
      (uuDualGraph (uResidueZero k hk)).Reachable
        (.cell ⟨1, by omega⟩ c) .out)
    (c : Fin (3 * k - 1)) :
    (uuDualGraph (uResidueZero k hk)).Reachable
      (.cell ⟨0, by omega⟩ c) .out := by
  exact (initial_cap_face_adj_interior_frontier k hk c.val c.isLt).reachable.trans
    (hfrontier c)

/-- Away from column zero, the dense penultimate cap row joins each final cap
face to the corresponding face on the final interior frontier. -/
theorem final_cap_face_adj_interior_frontier (k : Nat) (hk : 7 ≤ k)
    (c : Nat) (hc0 : 0 < c) (hc : c < 3 * k - 1) :
    (uuDualGraph (uResidueZero k hk)).Adj
      (.cell ⟨3 * k - 3, by omega⟩ ⟨c, hc⟩)
      (.cell ⟨3 * k - 2, by omega⟩ ⟨c, hc⟩) := by
  exact horizontal_uu_dual_cells_adj (uResidueZero k hk) (3 * k - 2) c
    (by omega) (by omega) hc
    (penultimate_cap_mem_uResidueZero k hk c hc0 (by omega))
    (penultimate_cap_mem_uResidueZero k hk (c + 1) (by omega) (by omega))

/-- The singleton bottom U vertex handles the column-zero exception by joining
the first two faces in the final cap face row. -/
theorem final_cap_zero_adj_one (k : Nat) (hk : 7 ≤ k) :
    (uuDualGraph (uResidueZero k hk)).Adj
      (.cell ⟨3 * k - 2, by omega⟩ ⟨0, by omega⟩)
      (.cell ⟨3 * k - 2, by omega⟩ ⟨1, by omega⟩) := by
  exact vertical_uu_dual_cells_adj (uResidueZero k hk) (3 * k - 2) 1
    (by omega) (by omega) (by omega)
    (penultimate_cap_mem_uResidueZero k hk 1 (by omega) (by omega))
    (by
      convert bottom_cap_mem_uResidueZero k hk using 1
      apply Prod.ext
      · apply Fin.ext
        simp
        omega
      · apply Fin.ext
        simp)

/-- The right end of the final interior frontier is attached directly to OUT. -/
theorem final_interior_frontier_adj_out (k : Nat) (hk : 7 ≤ k) :
    (uuDualGraph (uResidueZero k hk)).Adj
      (.cell ⟨3 * k - 3, by omega⟩ ⟨3 * k - 2, by omega⟩) .out := by
  exact vertical_uu_dual_right_out_adj (uResidueZero k hk) (3 * k - 3)
    (by omega) (by omega) (final_phase_right_mem_uResidueZero k hk)
    (by
      convert penultimate_cap_mem_uResidueZero k hk (3 * k - 1) (by omega) (by omega)
        using 1
      apply Prod.ext
      · apply Fin.ext
        simp
        omega
      · apply Fin.ext
        simp)

/-- If the strict interior columns of the final interior frontier reach OUT,
then every face in the bottom cap row reaches OUT.  The rightmost frontier face
uses `final_interior_frontier_adj_out`, while column zero routes through the
singleton bottom vertex. -/
theorem final_cap_face_reachable_out (k : Nat) (hk : 7 ≤ k)
    (hfrontier : ∀ c : Fin (3 * k - 1), 0 < c.val → c.val < 3 * k - 2 →
      (uuDualGraph (uResidueZero k hk)).Reachable
        (.cell ⟨3 * k - 3, by omega⟩ c) .out)
    (c : Fin (3 * k - 1)) :
    (uuDualGraph (uResidueZero k hk)).Reachable
      (.cell ⟨3 * k - 2, by omega⟩ c) .out := by
  by_cases hc0 : c.val = 0
  · have hc : c = ⟨0, by omega⟩ := Fin.ext hc0
    have hk3 : 21 ≤ 3 * k := Nat.mul_le_mul_left 3 hk
    let one : Fin (3 * k - 1) := ⟨1, by omega⟩
    rw [hc]
    exact (final_cap_zero_adj_one k hk).reachable.trans
      ((final_cap_face_adj_interior_frontier k hk 1 (by omega) (by omega)).symm.reachable.trans
        (hfrontier one (by simp [one]) (by simp [one]; omega)))
  · by_cases hlast : c.val = 3 * k - 2
    · have hc : c = ⟨3 * k - 2, by omega⟩ := Fin.ext hlast
      rw [hc]
      exact (final_cap_face_adj_interior_frontier k hk (3 * k - 2)
        (by omega) (by omega)).symm.reachable.trans
          (final_interior_frontier_adj_out k hk).reachable
    · exact (final_cap_face_adj_interior_frontier k hk c.val (by omega) c.isLt).symm.reachable.trans
        (hfrontier c (by omega) (by omega))

end GridGraphs
