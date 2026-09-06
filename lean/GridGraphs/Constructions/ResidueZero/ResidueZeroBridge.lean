import GridGraphs.Constructions.ResidueZero.ResidueZeroAnchored
import GridGraphs.Constructions.ResidueZero.ResidueZeroWidening

/-!
# The successor anchor bridge

The appended `R_k` omits column `3k`.  Consequently the route from the
embedded old anchor makes a one-face-row detour through the final two old
phase rows before descending into the new right slab.
-/

namespace GridGraphs

open SimpleGraph

private theorem old_final_mem_widened (k : Nat) (hk : 7 ≤ k) (c : Nat)
    (hc : PhaseOccupied (k + 1) (.ordinary (k - 1)) c) :
    ((⟨3 * k - 1, by omega⟩, ⟨c, by
        rcases hc with ⟨j, rfl⟩
        exact phaseColumn_lt (by simp [PhaseRow.parameter]) j⟩) :
      GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
        uResidueZero (k + 1) (by omega) := by
  let i : Fin (phaseRows k).length := ⟨(phaseRows k).length - 1, by
    rw [phaseRows_length k hk]
    omega⟩
  have hi : (phaseRows k).get i = .ordinary (k - 1) := by
    rw [List.get_eq_getElem]
    rw [← List.getLast_eq_getElem (List.ne_nil_of_length_pos (by
      rw [phaseRows_length k hk]
      omega))]
    exact phaseRows_getLast k hk
  have hc' : PhaseOccupied (k + 1) ((phaseRows k).get i) c := by
    rw [hi]
    exact hc
  convert old_phase_occupied_mem_widened k hk i c hc' using 1
  apply Prod.ext <;> apply Fin.ext
  · simp [i, phaseRows_length k hk]
    omega
  · rfl

private theorem appended_mem (k : Nat) (hk : 7 ≤ k) (c : Nat)
    (hc : PhaseOccupied (k + 1) (.ordinary k) c) :
    ((⟨3 * k, by omega⟩, ⟨c, by
        rcases hc with ⟨j, rfl⟩
        exact phaseColumn_lt (by simp [PhaseRow.parameter]) j⟩) :
      GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
        uResidueZero (k + 1) (by omega) := by
  let i : Fin (phaseRows (k + 1)).length :=
    ⟨(phaseRows (k + 1)).length - 1, by
      rw [phaseRows_length (k + 1) (by omega)]
      omega⟩
  have hi : (phaseRows (k + 1)).get i = .ordinary k := by
    rw [List.get_eq_getElem]
    rw [← List.getLast_eq_getElem (List.ne_nil_of_length_pos (by
      rw [phaseRows_length (k + 1) (by omega)]
      omega))]
    simpa only [show k + 1 - 1 = k by omega] using
      phaseRows_getLast (k + 1) (by omega)
  have hc' : PhaseOccupied (k + 1) ((phaseRows (k + 1)).get i) c := by
    rw [hi]
    exact hc
  convert phase_occupied_mem_uResidueZero (k + 1) (by omega) i c hc' using 1
  apply Prod.ext <;> apply Fin.ext
  · simp [i, phaseRows_length (k + 1) (by omega)]
    omega
  · rfl

private theorem old_final_at (k : Nat) (hk : 7 ≤ k) (c : Nat)
    (hc : c = 3 * k - 1 ∨ c = 3 * k ∨ c = 3 * k + 1) :
    ((⟨3 * k - 1, by omega⟩, ⟨c, by omega⟩) :
      GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
        uResidueZero (k + 1) (by omega) := by
  apply old_final_mem_widened k hk
  rw [phaseOccupied_ordinary_iff (by omega : k - 1 < k + 1)]
  rcases hc with rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨k - 1, by omega, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨k, by omega, by omega, rfl⟩)
  · exact Or.inl ⟨k, by omega, rfl⟩

private theorem appended_at (k : Nat) (hk : 7 ≤ k) (c : Nat)
    (hc : c = 3 * k - 1 ∨ c = 3 * k + 1 ∨ c = 3 * k + 2) :
    ((⟨3 * k, by omega⟩, ⟨c, by omega⟩) :
      GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
        uResidueZero (k + 1) (by omega) := by
  apply appended_mem k hk
  rw [phaseOccupied_ordinary_iff (by omega : k < k + 1)]
  rcases hc with rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨k - 1, by omega, by omega, by omega⟩)
  · exact Or.inl ⟨k, by omega, rfl⟩
  · exact Or.inr (Or.inl ⟨k, by omega, by omega, rfl⟩)

/-- The embedded old anchor reaches the first checkpoint in the new slab. -/
theorem residueZero_embeddedAnchor_reachable_slab (k : Nat) (hk : 7 ≤ k) :
    (uuDualGraph (uResidueZero (k + 1) (by omega))).Reachable
      (widenCell k (residueZeroAnchorCoord k hk).1
        (residueZeroAnchorCoord k hk).2)
      (widenedAnchorSlabFace k hk) := by
  let G := uuDualGraph (uResidueZero (k + 1) (by omega))
  have hstart :
      widenCell k (residueZeroAnchorCoord k hk).1
          (residueZeroAnchorCoord k hk).2 =
        .cell ⟨3 * k - 1, by omega⟩ ⟨3 * k - 2, by omega⟩ := by
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
      simp [widenBoundedFace, residueZeroAnchorCoord]
    omega
  have hright : G.Adj
      (.cell ⟨3 * k - 1, by omega⟩ ⟨3 * k - 2, by omega⟩)
      (.cell ⟨3 * k - 1, by omega⟩ ⟨3 * k - 1, by omega⟩) :=
    by
      have hb : ((⟨3 * k - 1 + 1, by omega⟩, ⟨3 * k - 1, by omega⟩) :
          GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
          uResidueZero (k + 1) (by omega) := by
        convert appended_at k hk _ (Or.inl rfl) using 1
        apply Prod.ext <;> apply Fin.ext <;> simp
        omega
      exact vertical_uu_dual_cells_adj _ (3 * k - 1) (3 * k - 1)
        (by omega) (by omega) (by omega)
        (old_final_at k hk _ (Or.inl rfl)) hb
  have hup : G.Adj
      (.cell ⟨3 * k - 2, by omega⟩ ⟨3 * k - 1, by omega⟩)
      (.cell ⟨3 * k - 1, by omega⟩ ⟨3 * k - 1, by omega⟩) :=
    by
      have hr : ((⟨3 * k - 1, by omega⟩, ⟨3 * k - 1 + 1, by omega⟩) :
          GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
          uResidueZero (k + 1) (by omega) := by
        convert old_final_at k hk _ (Or.inr (Or.inl rfl)) using 1
        apply Prod.ext <;> apply Fin.ext <;> simp
        omega
      exact horizontal_uu_dual_cells_adj _ (3 * k - 1) (3 * k - 1)
        (by omega) (by omega) (by omega)
        (old_final_at k hk _ (Or.inl rfl)) hr
  have hacross : G.Adj
      (.cell ⟨3 * k - 2, by omega⟩ ⟨3 * k - 1, by omega⟩)
      (.cell ⟨3 * k - 2, by omega⟩ ⟨3 * k, by omega⟩) := by
    simpa only [show 3 * k - 6 + 4 = 3 * k - 2 by omega] using
      old_phase_right_slab_horizontal_step k hk
        (3 * k - 6) (by rw [phaseRows_length k hk]; omega)
  have hdown : G.Adj
      (.cell ⟨3 * k - 2, by omega⟩ ⟨3 * k, by omega⟩)
      (.cell ⟨3 * k - 1, by omega⟩ ⟨3 * k, by omega⟩) := by
    simpa only [show 3 * k - 5 + 3 = 3 * k - 2 by omega,
      show 3 * k - 5 + 4 = 3 * k - 1 by omega] using
      old_phase_right_slab_vertical_step k hk
        ⟨3 * k - 5, by rw [phaseRows_length k hk]; omega⟩
  rw [hstart]
  simpa [G, widenedAnchorSlabFace] using
      hright.reachable.trans (hup.symm.reachable.trans
        (hacross.reachable.trans hdown.reachable))

/-- The slab checkpoint descends across the appended `R_k`. -/
theorem residueZero_slab_reachable_appended (k : Nat) (hk : 7 ≤ k) :
    (uuDualGraph (uResidueZero (k + 1) (by omega))).Reachable
      (widenedAnchorSlabFace k hk) (widenedAnchorAppendedFace k hk) := by
  let G := uuDualGraph (uResidueZero (k + 1) (by omega))
  have hright : G.Adj
      (.cell ⟨3 * k - 1, by omega⟩ ⟨3 * k, by omega⟩)
      (.cell ⟨3 * k - 1, by omega⟩ ⟨3 * k + 1, by omega⟩) := by
    have hb : ((⟨3 * k - 1 + 1, by omega⟩, ⟨3 * k + 1, by omega⟩) :
        GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
        uResidueZero (k + 1) (by omega) := by
      convert appended_at k hk _ (Or.inr (Or.inl rfl)) using 1
      apply Prod.ext <;> apply Fin.ext <;> simp
      omega
    exact vertical_uu_dual_cells_adj _ (3 * k - 1) (3 * k + 1)
      (by omega) (by omega) (by omega)
      (old_final_at k hk _ (Or.inr (Or.inr rfl))) hb
  have hdown : G.Adj
      (.cell ⟨3 * k - 1, by omega⟩ ⟨3 * k + 1, by omega⟩)
      (.cell ⟨3 * k, by omega⟩ ⟨3 * k + 1, by omega⟩) := by
    simpa only [show 3 * k + 1 + 1 = 3 * k + 2 by omega] using
      horizontal_uu_dual_cells_adj _ (3 * k) (3 * k + 1)
        (by omega) (by omega) (by omega)
        (appended_at k hk _ (Or.inr (Or.inl rfl)))
        (appended_at k hk _ (Or.inr (Or.inr rfl)))
  have hleft : G.Adj
      (.cell ⟨3 * k, by omega⟩ ⟨3 * k, by omega⟩)
      (.cell ⟨3 * k, by omega⟩ ⟨3 * k + 1, by omega⟩) := by
    exact vertical_uu_dual_cells_adj _ (3 * k) (3 * k + 1)
      (by omega) (by omega) (by omega)
      (appended_at k hk _ (Or.inr (Or.inl rfl)))
      (penultimate_cap_mem_uResidueZero (k + 1) (by omega) (3 * k + 1)
        (by omega) (by omega))
  simpa [G, widenedAnchorSlabFace, widenedAnchorAppendedFace] using
    hright.reachable.trans (hdown.reachable.trans hleft.symm.reachable)

/-- The appended-row checkpoint crosses the new right slab to the new anchor. -/
theorem residueZero_appended_reachable_newAnchor (k : Nat) (hk : 7 ≤ k) :
    (uuDualGraph (uResidueZero (k + 1) (by omega))).Reachable
      (widenedAnchorAppendedFace k hk)
      (residueZeroAnchor (k + 1) (by omega)) := by
  exact (vertical_uu_dual_cells_adj _ (3 * k) (3 * k + 1)
    (by omega) (by omega) (by omega)
    (appended_at k hk _ (Or.inr (Or.inl rfl)))
    (penultimate_cap_mem_uResidueZero (k + 1) (by omega) (3 * k + 1)
      (by omega) (by omega))).reachable

/-- The complete bounded anchor bridge for one successor step. -/
theorem residueZeroAnchorWideningBridge (k : Nat) (hk : 7 ≤ k) :
    ResidueZeroAnchorWideningBridge k hk := by
  exact ⟨residueZero_embeddedAnchor_reachable_slab k hk,
    residueZero_slab_reachable_appended k hk,
    residueZero_appended_reachable_newAnchor k hk⟩

/-- With the anchor route discharged, these are exactly the two geometric
obligations left by the strengthened, one-more-widening certificate. -/
theorem residueZeroAnchoredCertificate_succ_of_newFaces_nextStable
    (k : Nat) (hk : 7 ≤ k)
    (hold : ResidueZeroAnchoredCertificate k hk)
    (hnew :
      ∀ (r : Fin (3 * (k + 1) - 1)), 0 < r.val →
        r.val < 3 * (k + 1) - 2 → ∀ c : Fin (3 * (k + 1) - 1),
          IsNewResidueZeroInteriorFace k r c →
            (uuDualGraph (uResidueZero (k + 1) (by omega))).Reachable
              (.cell r c) (residueZeroAnchor (k + 1) (by omega)))
    (hstable :
      ∀ (r : Fin (3 * (k + 1) - 1)), 0 < r.val →
        r.val < 3 * (k + 1) - 2 → ∀ c : Fin (3 * (k + 1) - 1),
          (widenableOldDualGraph (k + 1) (by omega)).Reachable (r, c)
            (residueZeroAnchorCoord (k + 1) (by omega))) :
    ResidueZeroAnchoredCertificate (k + 1) (by omega) := by
  apply residueZeroAnchoredCertificate_succ k hk hold
  exact ⟨residueZeroAnchorWideningBridge k hk, hnew, hstable⟩

end GridGraphs
