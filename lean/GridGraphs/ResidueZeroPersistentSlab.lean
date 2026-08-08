import GridGraphs.ResidueZeroPersistent
import GridGraphs.ResidueZeroWidening

/-!
# Persistent paths through the residue-zero right slab

The old phase block supplies a vertical corridor in column `3k`.  The proofs
below retain both copies of every dual edge, so the corridor is still present
after one further widening.
-/

namespace GridGraphs

open SimpleGraph

private theorem old_row_right_run (k : Nat) (hk : 7 ≤ k)
    (i : Fin (phaseRows k).length) :
    PhaseOccupied (k + 1) ((phaseRows k).get i) (3 * k) ∧
      PhaseOccupied (k + 1) ((phaseRows k).get i) (3 * k + 1) := by
  have hp := phaseRows_parameter_lt k hk _ (List.get_mem (phaseRows k) i)
  constructor
  · cases hrow : (phaseRows k).get i with
    | ordinary a =>
        simp only [hrow, PhaseRow.parameter] at hp ⊢
        exact (phaseOccupied_ordinary_iff (by omega : a < k + 1)).2
          (Or.inr (Or.inr ⟨k, by omega, by omega, rfl⟩))
    | seam a =>
        simp only [hrow, PhaseRow.parameter] at hp ⊢
        exact (phaseOccupied_seam_iff (by omega : a < k + 1)).2
          (Or.inr (Or.inr ⟨k, by omega, by omega, rfl⟩))
  · exact phaseOccupied_backbone (by omega : k < k + 1)

private theorem shifted_old_row (k : Nat) (hk : 7 ≤ k)
    (i : Fin (phaseRows k).length) :
    (phaseRows (k + 1)).get ⟨i.val + 2, by
      have hlenNew := phaseRows_length (k + 1) (by omega)
      have hlenOld := phaseRows_length k hk
      have := i.isLt
      omega⟩ = (phaseRows k).get i := by
  simp [phaseRows_succ k hk, List.getElem_append_left i.isLt]

private theorem slab_vertical_persistent (k : Nat) (hk : 7 ≤ k)
    (i : Fin (phaseRows k).length) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Adj
      (⟨i.val + 3, by
        have hlen := phaseRows_length k hk
        have := i.isLt
        omega⟩, ⟨3 * k, by omega⟩)
      (⟨i.val + 4, by
        have hlen := phaseRows_length k hk
        have := i.isLt
        omega⟩, ⟨3 * k, by omega⟩) := by
  have hcur := old_phase_right_slab_vertical_step k hk i
  let i' : Fin (phaseRows (k + 1)).length := ⟨i.val + 2, by
    have hlenNew := phaseRows_length (k + 1) (by omega)
    have hlenOld := phaseRows_length k hk
    have := i.isLt
    omega⟩
  have hrow : (phaseRows (k + 1)).get i' = (phaseRows k).get i := by
    simpa [i'] using shifted_old_row k hk i
  have hrun := old_row_right_run k hk i
  have hnext := old_phase_horizontal_dual_adj_widened (k + 1) (by omega)
    i' (3 * k) (by omega)
    (by rw [hrow]; exact hrun.1) (by rw [hrow]; exact hrun.2)
  have hlen := phaseRows_length k hk
  have hii := i.isLt
  refine ⟨⟨hcur, ?_⟩, ⟨by simp [IsStrictInteriorResidueZeroCoord]; omega,
    by simp [IsStrictInteriorResidueZeroCoord]; omega⟩⟩
  simpa [i', widenCell, widenBoundedFace] using hnext

private theorem slab_left_horizontal_persistent (k : Nat) (hk : 7 ≤ k)
    (i : Nat) (hi : i + 1 < (phaseRows k).length) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Adj
      (⟨i + 4, by rw [phaseRows_length k hk] at hi; omega⟩,
        ⟨3 * k - 1, by omega⟩)
      (⟨i + 4, by rw [phaseRows_length k hk] at hi; omega⟩,
        ⟨3 * k, by omega⟩) := by
  have hcur := old_phase_right_slab_horizontal_step k hk i hi
  let i' : Nat := i + 2
  have hi' : i' + 1 < (phaseRows (k + 1)).length := by
    simp [i', phaseRows_length (k + 1) (by omega), phaseRows_length k hk] at hi ⊢
    omega
  have htop := (old_row_right_run k hk ⟨i, by omega⟩).1
  have hbottom := (old_row_right_run k hk ⟨i + 1, hi⟩).1
  have hrowTop : (phaseRows (k + 1))[i']'(by omega) =
      (phaseRows k)[i]'(by omega) := by
    simp [i', phaseRows_succ k hk,
      List.getElem_append_left (show i < (phaseRows k).length by omega)]
  have hrowBottom : (phaseRows (k + 1))[i' + 1]'hi' =
      (phaseRows k)[i + 1]'hi := by
    simp [i', phaseRows_succ k hk,
      List.getElem_append_left (show i + 1 < (phaseRows k).length by omega)]
  have hnext := old_phase_vertical_dual_adj_widened (k + 1) (by omega)
    i' hi' (3 * k) (by omega) (by omega)
    (by simpa [hrowTop] using htop) (by simpa [hrowBottom] using hbottom)
  have hlenOld := phaseRows_length k hk
  have hlenNew := phaseRows_length (k + 1) (by omega)
  refine ⟨⟨hcur, ?_⟩, ⟨by simp [IsStrictInteriorResidueZeroCoord]; omega,
    by simp [IsStrictInteriorResidueZeroCoord]; omega⟩⟩
  simpa [i', widenCell, widenBoundedFace] using hnext

private theorem slab_right_horizontal_persistent (k : Nat) (hk : 7 ≤ k)
    (r : Nat) (hr0 : 3 ≤ r) (hrlast : r < 3 * k) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Adj
      (⟨r, by omega⟩, ⟨3 * k, by omega⟩)
      (⟨r, by omega⟩, ⟨3 * k + 1, by omega⟩) := by
  let i : Nat := r - 2
  have hi : i + 1 < (phaseRows (k + 1)).length := by
    simp [i, phaseRows_length (k + 1) (by omega)]
    omega
  have htop : PhaseOccupied (k + 1)
      ((phaseRows (k + 1))[i]'(by omega)) (3 * k + 1) :=
    phaseOccupied_backbone (by omega)
  have hbottom : PhaseOccupied (k + 1)
      ((phaseRows (k + 1))[i + 1]'hi) (3 * k + 1) :=
    phaseOccupied_backbone (by omega)
  have htopMem := phase_occupied_mem_uResidueZero (k + 1) (by omega)
    ⟨i, by omega⟩ (3 * k + 1) htop
  have hbottomMem := phase_occupied_mem_uResidueZero (k + 1) (by omega)
    ⟨i + 1, hi⟩ (3 * k + 1) hbottom
  have hcur := vertical_uu_dual_cells_adj
    (uResidueZero (k + 1) (by omega)) (r) (3 * k + 1)
    (by omega) (by omega) (by omega)
    (by
      convert htopMem using 1
      apply Prod.ext <;> apply Fin.ext <;> simp [i] <;> omega)
    (by
      convert hbottomMem using 1
      apply Prod.ext <;> apply Fin.ext <;> simp [i] <;> omega)
  have hnext := old_phase_vertical_dual_adj_widened (k + 1) (by omega)
    i hi (3 * k + 1) (by omega) (by omega) htop hbottom
  refine ⟨⟨hcur, ?_⟩, ⟨by simp [IsStrictInteriorResidueZeroCoord]; omega,
    by simp [IsStrictInteriorResidueZeroCoord]; omega⟩⟩
  convert hnext using 1 <;> apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
    simp [i, widenCell, widenBoundedFace] <;> omega

private theorem slab_column_reachable_checkpoint (k : Nat) (hk : 7 ≤ k)
    (r : Nat) (hr0 : 3 ≤ r) (hrlast : r < 3 * k) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
      (⟨r, by omega⟩, ⟨3 * k, by omega⟩)
      (⟨3 * k - 1, by omega⟩, ⟨3 * k, by omega⟩) := by
  obtain ⟨d, hd⟩ : ∃ d, r + d = 3 * k - 1 := by
    exact ⟨3 * k - 1 - r, by omega⟩
  induction d generalizing r with
  | zero =>
      have hr : r = 3 * k - 1 := by omega
      subst r
      apply Reachable.refl
  | succ d ih =>
      have hirange : r - 3 < (phaseRows k).length := by
        rw [phaseRows_length k hk]
        omega
      have hedge := slab_vertical_persistent k hk ⟨r - 3, hirange⟩
      have hedge' : (persistentResidueZeroGraph (k + 1) (by omega)).Adj
          (⟨r, by omega⟩, ⟨3 * k, by omega⟩)
          (⟨r + 1, by omega⟩, ⟨3 * k, by omega⟩) := by
        simpa only [show r - 3 + 3 = r by omega,
          show r - 3 + 4 = r + 1 by omega] using hedge
      exact hedge'.reachable.trans (ih (r + 1) (by omega) (by omega) (by omega))

private theorem checkpoint_reachable_anchor (k : Nat) (hk : 7 ≤ k) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
      (⟨3 * k - 1, by omega⟩, ⟨3 * k, by omega⟩)
      (residueZeroAnchorCoord (k + 1) (by omega)) := by
  have hright := slab_right_horizontal_persistent k hk (3 * k - 1)
    (by omega) (by omega)
  let i : Fin (phaseRows (k + 1)).length :=
    ⟨(phaseRows (k + 1)).length - 1, by
      rw [phaseRows_length (k + 1) (by omega)]
      omega⟩
  have hrow : (phaseRows (k + 1)).get i = .ordinary k := by
    rw [List.get_eq_getElem]
    rw [← List.getLast_eq_getElem (List.ne_nil_of_length_pos (by
      rw [phaseRows_length (k + 1) (by omega)]
      omega))]
    simpa only [show k + 1 - 1 = k by omega] using
      phaseRows_getLast (k + 1) (by omega)
  have hrun : PhaseOccupied (k + 1) ((phaseRows (k + 1)).get i) (3 * k + 1) ∧
      PhaseOccupied (k + 1) ((phaseRows (k + 1)).get i) (3 * k + 2) := by
    rw [hrow]
    constructor
    · exact phaseOccupied_backbone (by omega)
    · exact (phaseOccupied_ordinary_iff (by omega : k < k + 1)).2
        (Or.inr (Or.inl ⟨k, by omega, by omega, rfl⟩))
  have hcur := horizontal_uu_dual_cells_adj
    (uResidueZero (k + 1) (by omega)) (3 * k) (3 * k + 1)
    (by omega) (by omega) (by omega)
    (by
      convert phase_occupied_mem_uResidueZero (k + 1) (by omega) i
        (3 * k + 1) hrun.1 using 1
      apply Prod.ext <;> apply Fin.ext
      · simp [i, phaseRows_length (k + 1) (by omega)]
        omega
      · rfl)
    (by
      convert phase_occupied_mem_uResidueZero (k + 1) (by omega) i
        (3 * k + 2) hrun.2 using 1
      apply Prod.ext <;> apply Fin.ext
      · simp [i, phaseRows_length (k + 1) (by omega)]
        omega
      · rfl)
  have hnext := old_phase_horizontal_dual_adj_widened (k + 1) (by omega)
    i (3 * k + 1) (by omega) hrun.1 hrun.2
  have hdown : (persistentResidueZeroGraph (k + 1) (by omega)).Adj
      (⟨3 * k - 1, by omega⟩, ⟨3 * k + 1, by omega⟩)
      (⟨3 * k, by omega⟩, ⟨3 * k + 1, by omega⟩) := by
    refine ⟨⟨hcur, ?_⟩, ⟨by simp [IsStrictInteriorResidueZeroCoord]; omega,
      by simp [IsStrictInteriorResidueZeroCoord]; omega⟩⟩
    convert hnext using 1 <;> apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
      simp [i, phaseRows_length (k + 1) (by omega), widenCell,
        widenBoundedFace] <;> omega
  simpa [residueZeroAnchorCoord] using hright.reachable.trans hdown.reachable

/-- Every face in the two rightmost slab columns reaches the successor anchor
through edges which survive the following widening. -/
theorem persistentResidueZero_rightSlab_core (k : Nat) (hk : 7 ≤ k)
    (r c : Fin (3 * (k + 1) - 1))
    (hr0 : 3 ≤ r.val) (hrlast : r.val < 3 * k)
    (hc : 3 * k ≤ c.val) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Reachable (r, c)
      (residueZeroAnchorCoord (k + 1) (by omega)) := by
  have hcolumn := slab_column_reachable_checkpoint k hk r.val hr0 hrlast
  have hfinish := checkpoint_reachable_anchor k hk
  have hc' : c.val = 3 * k ∨ c.val = 3 * k + 1 := by
    have := c.isLt
    omega
  rcases hc' with hc' | hc'
  · convert hcolumn.trans hfinish using 1
    apply Prod.ext
    · rfl
    · exact Fin.ext hc'
  · have hleft := slab_right_horizontal_persistent k hk r.val hr0 hrlast
    have hstart : (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
        (r, c) (⟨r.val, by omega⟩, ⟨3 * k, by omega⟩) := by
      convert hleft.symm.reachable using 1
      apply Prod.ext
      · rfl
      · exact Fin.ext hc'
    exact hstart.trans (hcolumn.trans hfinish)

private theorem slab_top_left_persistent (k : Nat) (hk : 7 ≤ k) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Adj
      (⟨3, by omega⟩, ⟨3 * k - 1, by omega⟩)
      (⟨3, by omega⟩, ⟨3 * k, by omega⟩) := by
  have hlen : 2 < (phaseRows (k + 1)).length := by
    rw [phaseRows_length (k + 1) (by omega)]
    omega
  have hrowTop : (phaseRows (k + 1))[1]'(by omega) = .seam (k - 2) := by
    simp [phaseRows_succ k hk]
  have hrowBottom : (phaseRows (k + 1))[2]'hlen = (phaseRows k)[0]'(by
      rw [phaseRows_length k hk]
      omega) := by
    simp [phaseRows_succ k hk,
      List.getElem_append_left (show 0 < (phaseRows k).length by
        rw [phaseRows_length k hk]
        omega)]
  have htop : PhaseOccupied (k + 1) ((phaseRows (k + 1))[1]'(by omega))
      (3 * k) := by
    rw [hrowTop]
    exact (phaseOccupied_seam_iff (by omega : k - 2 < k + 1)).2
      (Or.inr (Or.inr ⟨k, by omega, by omega, rfl⟩))
  have hbottom : PhaseOccupied (k + 1) ((phaseRows (k + 1))[2]'hlen)
      (3 * k) := by
    rw [hrowBottom]
    exact (old_row_right_run k hk ⟨0, by
      rw [phaseRows_length k hk]
      omega⟩).1
  have hcur := vertical_uu_dual_cells_adj
    (uResidueZero (k + 1) (by omega)) 3 (3 * k)
    (by omega) (by omega) (by omega)
    (by simpa using (phase_occupied_mem_uResidueZero (k + 1) (by omega)
      ⟨1, by omega⟩ (3 * k) htop))
    (by simpa using (phase_occupied_mem_uResidueZero (k + 1) (by omega)
      ⟨2, hlen⟩ (3 * k) hbottom))
  have hnext := old_phase_vertical_dual_adj_widened (k + 1) (by omega)
    1 (by omega) (3 * k) (by omega) (by omega) htop hbottom
  refine ⟨⟨hcur, ?_⟩, ⟨by simp [IsStrictInteriorResidueZeroCoord]; omega,
    by simp [IsStrictInteriorResidueZeroCoord]; omega⟩⟩
  simpa [widenCell, widenBoundedFace] using hnext

private theorem slab_bottom_left_vertical_persistent (k : Nat) (hk : 7 ≤ k) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Adj
      (⟨3 * k - 2, by omega⟩, ⟨3 * k - 1, by omega⟩)
      (⟨3 * k - 1, by omega⟩, ⟨3 * k - 1, by omega⟩) := by
  let i : Fin (phaseRows k).length :=
    ⟨(phaseRows k).length - 1, by rw [phaseRows_length k hk]; omega⟩
  have hrowOld : (phaseRows k).get i = .ordinary (k - 1) := by
    rw [List.get_eq_getElem]
    rw [← List.getLast_eq_getElem (List.ne_nil_of_length_pos (by
      rw [phaseRows_length k hk]
      omega))]
    exact phaseRows_getLast k hk
  let i' : Fin (phaseRows (k + 1)).length := ⟨i.val + 2, by
    have hlenOld := phaseRows_length k hk
    have hlenNew := phaseRows_length (k + 1) (by omega)
    have := i.isLt
    omega⟩
  have hrow : (phaseRows (k + 1)).get i' = .ordinary (k - 1) := by
    rw [shifted_old_row k hk i, hrowOld]
  have hrun : PhaseOccupied (k + 1) ((phaseRows (k + 1)).get i') (3 * k - 1) ∧
      PhaseOccupied (k + 1) ((phaseRows (k + 1)).get i') (3 * k) := by
    rw [hrow]
    constructor
    · exact (phaseOccupied_ordinary_iff (by omega : k - 1 < k + 1)).2
        (Or.inr (Or.inl ⟨k - 1, by omega, by omega, by omega⟩))
    · exact (phaseOccupied_ordinary_iff (by omega : k - 1 < k + 1)).2
        (Or.inr (Or.inr ⟨k, by omega, by omega, rfl⟩))
  have hcur := horizontal_uu_dual_cells_adj
    (uResidueZero (k + 1) (by omega)) (3 * k - 1) (3 * k - 1)
    (by omega) (by omega) (by omega)
    (by
      convert phase_occupied_mem_uResidueZero (k + 1) (by omega) i'
        (3 * k - 1) hrun.1 using 1
      apply Prod.ext <;> apply Fin.ext
      · simp [i', i, phaseRows_length k hk]
        omega
      · rfl)
    (by
      convert phase_occupied_mem_uResidueZero (k + 1) (by omega) i'
        (3 * k) hrun.2 using 1
      apply Prod.ext <;> apply Fin.ext
      · simp [i', i, phaseRows_length k hk]
        omega
      · simp
        omega)
  have hrunRight : PhaseOccupied (k + 1) ((phaseRows (k + 1)).get i')
      (3 * k - 1 + 1) := by
    convert hrun.2 using 1 <;> omega
  have hnext := old_phase_horizontal_dual_adj_widened (k + 1) (by omega)
    i' (3 * k - 1) (by omega) hrun.1 hrunRight
  refine ⟨⟨hcur, ?_⟩, ⟨by simp [IsStrictInteriorResidueZeroCoord]; omega,
    by simp [IsStrictInteriorResidueZeroCoord]; omega⟩⟩
  convert hnext using 1 <;> apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
    simp [i', i, phaseRows_length k hk, widenCell, widenBoundedFace] <;> omega

/-- The `rightSlab` obligation in `PersistentResidueZeroStepGeometry`. -/
theorem persistentResidueZeroStepGeometry_rightSlab (k : Nat) (hk : 7 ≤ k) :
    ∀ (r c : Fin (3 * (k + 1) - 1)),
      3 ≤ r.val → r.val < 3 * k → 3 * k - 1 ≤ c.val →
      (persistentResidueZeroGraph (k + 1) (by omega)).Reachable (r, c)
        (residueZeroAnchorCoord (k + 1) (by omega)) := by
  intro r c hr0 hrlast hc
  by_cases hcore : 3 * k ≤ c.val
  · exact persistentResidueZero_rightSlab_core k hk r c hr0 hrlast hcore
  have hcval : c.val = 3 * k - 1 := by omega
  by_cases htop : r.val = 3
  · have hedge := slab_top_left_persistent k hk
    have hfinish := persistentResidueZero_rightSlab_core k hk
      (⟨3, by omega⟩) (⟨3 * k, by omega⟩)
      (by change 3 ≤ 3; omega) (by change 3 < 3 * k; omega)
      (by change 3 * k ≤ 3 * k; omega)
    convert hedge.reachable.trans hfinish using 1
    apply Prod.ext
    · exact Fin.ext htop
    · exact Fin.ext hcval
  by_cases hbottom : r.val = 3 * k - 1
  · have hup := slab_bottom_left_vertical_persistent k hk
    have hacross := slab_left_horizontal_persistent k hk (3 * k - 6) (by
      rw [phaseRows_length k hk]
      omega)
    have hacross' : (persistentResidueZeroGraph (k + 1) (by omega)).Adj
        (⟨3 * k - 2, by omega⟩, ⟨3 * k - 1, by omega⟩)
        (⟨3 * k - 2, by omega⟩, ⟨3 * k, by omega⟩) := by
      simpa only [show 3 * k - 6 + 4 = 3 * k - 2 by omega] using hacross
    have hfinish := persistentResidueZero_rightSlab_core k hk
      (⟨3 * k - 2, by omega⟩) (⟨3 * k, by omega⟩)
      (by change 3 ≤ 3 * k - 2; omega)
      (by change 3 * k - 2 < 3 * k; omega)
      (by change 3 * k ≤ 3 * k; omega)
    have hroute := hup.symm.reachable.trans (hacross'.reachable.trans hfinish)
    convert hroute using 1
    apply Prod.ext
    · exact Fin.ext hbottom
    · exact Fin.ext hcval
  · have hacross := slab_left_horizontal_persistent k hk (r.val - 4) (by
      rw [phaseRows_length k hk]
      omega)
    have hfinish := persistentResidueZero_rightSlab_core k hk
      (⟨r.val, by omega⟩) (⟨3 * k, by omega⟩)
      (by simpa using hr0) (by simpa using hrlast)
      (by change 3 * k ≤ 3 * k; omega)
    have hacross' : (persistentResidueZeroGraph (k + 1) (by omega)).Adj
        (r, c) (⟨r.val, by omega⟩, ⟨3 * k, by omega⟩) := by
      convert hacross using 1
      · apply Prod.ext
        · apply Fin.ext
          simp
          omega
        · exact Fin.ext hcval
      · apply Prod.ext
        · apply Fin.ext
          simp
          omega
        · rfl
    exact hacross'.reachable.trans hfinish

end GridGraphs
