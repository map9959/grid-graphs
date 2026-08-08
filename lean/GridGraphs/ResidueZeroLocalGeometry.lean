import GridGraphs.ResidueZeroSuccessor

namespace GridGraphs

open Finset SimpleGraph

private theorem phaseHorizontal (K : Nat) (hK : 7 ≤ K)
    (i : Fin (phaseRows K).length) (c : Nat) (hc : c < 3 * K - 1)
    (hl : PhaseOccupied K ((phaseRows K).get i) c)
    (hr : PhaseOccupied K ((phaseRows K).get i) (c + 1)) :
    (persistentResidueZeroGraph K hK).Adj
      (⟨i.val + 1, by have hi := i.isLt; have hlen := phaseRows_length K hK; omega⟩, ⟨c, hc⟩)
      (⟨i.val + 2, by have hi := i.isLt; have hlen := phaseRows_length K hK; omega⟩, ⟨c, hc⟩) := by
  refine ⟨⟨?_, old_phase_horizontal_dual_adj_widened K hK i c hc hl hr⟩, ?_, ?_⟩
  exact horizontal_uu_dual_cells_adj _ (i.val + 2) c (by omega)
    (by have hi := i.isLt; have hlen := phaseRows_length K hK; omega) hc
    (phase_occupied_mem_uResidueZero K hK i c hl)
    (phase_occupied_mem_uResidueZero K hK i (c + 1) hr)
  · simp only [IsStrictInteriorResidueZeroCoord, Prod.fst, Fin.val_mk]
    have hi := i.isLt
    have hlen := phaseRows_length K hK
    omega
  · simp only [IsStrictInteriorResidueZeroCoord, Prod.fst, Fin.val_mk]
    have hi := i.isLt
    have hlen := phaseRows_length K hK
    omega

private theorem phaseVertical (K : Nat) (hK : 7 ≤ K)
    (i c : Nat) (hi : i + 1 < (phaseRows K).length)
    (hc0 : 0 < c) (hc : c < 3 * K - 1)
    (ht : PhaseOccupied K ((phaseRows K)[i]'(by omega)) c)
    (hb : PhaseOccupied K ((phaseRows K)[i + 1]'hi) c) :
    (persistentResidueZeroGraph K hK).Adj
      (⟨i + 2, by rw [phaseRows_length K hK] at hi; omega⟩, ⟨c - 1, by omega⟩)
      (⟨i + 2, by rw [phaseRows_length K hK] at hi; omega⟩, ⟨c, hc⟩) := by
  refine ⟨⟨?_, old_phase_vertical_dual_adj_widened K hK i hi c hc0 hc ht hb⟩, ?_, ?_⟩
  exact vertical_uu_dual_cells_adj _ (i + 2) c
    (by rw [phaseRows_length K hK] at hi; omega) hc0 hc
    (phase_occupied_mem_uResidueZero K hK ⟨i, by omega⟩ c ht)
    (phase_occupied_mem_uResidueZero K hK ⟨i + 1, hi⟩ c hb)
  · simp only [IsStrictInteriorResidueZeroCoord, Prod.fst, Fin.val_mk]
    have hlen := phaseRows_length K hK
    omega
  · simp only [IsStrictInteriorResidueZeroCoord, Prod.fst, Fin.val_mk]
    have hlen := phaseRows_length K hK
    omega

private theorem topInterface (k : Nat) (hk : 7 ≤ k) (c : Nat)
    (hc0 : 0 < c) (hc : c < 3 * (k + 1) - 1)
    (hocc : PhaseOccupied (k + 1) (.ordinary (k - 2)) c)
    (hs : PhaseOccupied (k + 2) (.seam (k - 1)) c) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Adj
      (⟨1, by omega⟩, ⟨c - 1, by omega⟩) (⟨1, by omega⟩, ⟨c, hc⟩) := by
  let i0 : Fin (phaseRows (k + 1)).length := ⟨0, by
    rw [phaseRows_length (k + 1) (by omega)]; omega⟩
  have hrow0 : (phaseRows (k + 1)).get i0 = .ordinary (k - 2) := by
    simp [i0, phaseRows_succ k hk]
  have hm0 := phase_occupied_mem_uResidueZero (k + 1) (by omega) i0 c
    (by rw [hrow0]; exact hocc)
  have hm0' : ((⟨2, by omega⟩, ⟨c, by omega⟩) :
      GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈ uResidueZero (k + 1) (by omega) := by
    convert hm0 using 1 <;> apply Fin.ext <;> simp [i0]
  have hnow := vertical_uu_dual_cells_adj (uResidueZero (k + 1) (by omega)) 1 c
    (by omega) hc0 hc (all_cap_mem_uResidueZero (k + 1) (by omega) c (by omega)) hm0'
  let is : Fin (phaseRows (k + 2)).length := ⟨1, by
    rw [phaseRows_length (k + 2) (by omega)]; omega⟩
  let io : Fin (phaseRows (k + 2)).length := ⟨2, by
    rw [phaseRows_length (k + 2) (by omega)]; omega⟩
  have hrs : (phaseRows (k + 2)).get is = .seam (k - 1) := by
    simp [is, phaseRows_succ (k + 1) (by omega)]
  have hro : (phaseRows (k + 2)).get io = .ordinary (k - 2) := by
    simp [io, phaseRows_succ (k + 1) (by omega), phaseRows_succ k hk]
  have hms := phase_occupied_mem_uResidueZero (k + 2) (by omega) is c
    (by rw [hrs]; exact hs)
  have hmo := phase_occupied_mem_uResidueZero (k + 2) (by omega) io c
    (by rw [hro]; exact hocc.widen (by omega) (by simp [PhaseRow.parameter]; omega))
  have hnext := vertical_uu_dual_cells_adj (uResidueZero (k + 2) (by omega)) 3 c
    (by omega) hc0 (by omega) (by simpa [is] using hms) (by simpa [io] using hmo)
  exact ⟨⟨hnow, by simpa [widenCell, widenBoundedFace] using hnext⟩,
    by simp [IsStrictInteriorResidueZeroCoord]; omega,
    by simp [IsStrictInteriorResidueZeroCoord]; omega⟩

private theorem appendedInterface (k : Nat) (hk : 7 ≤ k) (c : Nat)
    (hc0 : 0 < c) (hc : c < 3 * (k + 1) - 1)
    (hocc : PhaseOccupied (k + 1) (.ordinary k) c)
    (hnew : PhaseOccupied (k + 2) (.ordinary (k + 1)) c) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Adj
      (⟨3 * k, by omega⟩, ⟨c - 1, by omega⟩)
      (⟨3 * k, by omega⟩, ⟨c, hc⟩) := by
  let ilast : Fin (phaseRows (k + 1)).length :=
    ⟨(phaseRows (k + 1)).length - 1, by
      rw [phaseRows_length (k + 1) (by omega)]; omega⟩
  have hrow : (phaseRows (k + 1)).get ilast = .ordinary k := by
    rw [List.get_eq_getElem]
    rw [← List.getLast_eq_getElem (List.ne_nil_of_length_pos (by
      rw [phaseRows_length (k + 1) (by omega)]; omega))]
    simpa only [show k + 1 - 1 = k by omega] using
      phaseRows_getLast (k + 1) (by omega)
  have hm := phase_occupied_mem_uResidueZero (k + 1) (by omega) ilast c
    (by rw [hrow]; exact hocc)
  have hm' : ((⟨3 * k, by omega⟩, ⟨c, by omega⟩) :
      GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈ uResidueZero (k + 1) (by omega) := by
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;>
      simp [ilast, phaseRows_length (k + 1) (by omega)] <;> omega
  have hnow := vertical_uu_dual_cells_adj (uResidueZero (k + 1) (by omega))
    (3 * k) c (by omega) hc0 hc hm'
    (penultimate_cap_mem_uResidueZero (k + 1) (by omega) c hc0 (by omega))
  have hold : PhaseOccupied (k + 2) (.ordinary k) c := by
    exact hocc.widen (by omega) (by simp [PhaseRow.parameter])
  have hmOld := old_phase_occupied_mem_widened (k + 1) (by omega) ilast c
    (by rw [hrow]; exact hold)
  let inew : Fin (phaseRows (k + 2)).length :=
    ⟨(phaseRows (k + 2)).length - 1, by
      rw [phaseRows_length (k + 2) (by omega)]; omega⟩
  have hrowNew : (phaseRows (k + 2)).get inew = .ordinary (k + 1) := by
    rw [List.get_eq_getElem]
    rw [← List.getLast_eq_getElem (List.ne_nil_of_length_pos (by
      rw [phaseRows_length (k + 2) (by omega)]; omega))]
    simpa only [show k + 2 - 1 = k + 1 by omega] using
      phaseRows_getLast (k + 2) (by omega)
  have hmNew := phase_occupied_mem_uResidueZero (k + 2) (by omega) inew c
    (by rw [hrowNew]; exact hnew)
  have hnext := vertical_uu_dual_cells_adj (uResidueZero (k + 2) (by omega))
    (3 * k + 2) c (by omega) hc0 (by omega)
    (by
      convert hmOld using 1
      apply Prod.ext <;> apply Fin.ext <;>
        simp [ilast, phaseRows_length (k + 1) (by omega)] <;> omega)
    (by
      convert hmNew using 1
      apply Prod.ext <;> apply Fin.ext <;>
        simp [inew, phaseRows_length (k + 2) (by omega)] <;> omega)
  exact ⟨⟨hnow, by
    simpa [widenCell, widenBoundedFace] using hnext⟩,
    by simp [IsStrictInteriorResidueZeroCoord]; omega,
    by simp [IsStrictInteriorResidueZeroCoord]; omega⟩

private theorem topRowOneToTwo (k : Nat) (hk : 7 ≤ k)
    (c : Fin (3 * (k + 1) - 1)) :
    ∃ d, (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
      (⟨1, by omega⟩, c) (⟨2, by omega⟩, d) := by
  let K := k + 1
  let a := k - 2
  let row1 := fun d : Fin (3 * K - 1) =>
    ((⟨1, by omega⟩, d) : Fin (3 * K - 1) × Fin (3 * K - 1))
  let row2 := fun d : Fin (3 * K - 1) =>
    ((⟨2, by omega⟩, d) : Fin (3 * K - 1) × Fin (3 * K - 1))
  have hrow : (phaseRows K)[0]'(by rw [phaseRows_length K (by omega)]; omega) =
      .ordinary a := by simp [K, a, phaseRows_succ k hk]
  have h := attach_all_columns_pointwise (G := persistentResidueZeroGraph K (by omega))
    (k := K) (by omega) row2 row1
  apply Exists.imp (fun d hd => hd.symm) (h ?_ ?_ c)
  · intro q hq
    constructor
    · by_cases hqa : q ≤ a
      · right
        have hr := ordinary_left_run (k := K) (a := a) (q := q) (by omega) hq hqa
        simpa [row1, row2, K, hrow] using
          (phaseHorizontal K (by omega) ⟨0, by rw [phaseRows_length K (by omega)]; omega⟩
            (3 * q + 1) (by omega) (by simpa [hrow] using hr.1)
            (by simpa [hrow] using hr.2)).symm.reachable
      · left
        have hr := ordinary_right_run (k := K) (a := a) (q := q)
          (by omega) hq (by omega)
        simpa [row1, row2, K, hrow] using
          (phaseHorizontal K (by omega) ⟨0, by rw [phaseRows_length K (by omega)]; omega⟩
            (3 * q) (by omega) (by simpa [hrow] using hr.1)
            (by simpa [hrow] using hr.2)).symm.reachable
    · have hb : PhaseOccupied K (.ordinary a) (3 * q + 1) := phaseOccupied_backbone hq
      simpa [row1, K] using topInterface k hk (3 * q + 1) (by omega) (by omega) hb
        (phaseOccupied_backbone (by omega : q < k + 2))
  · intro q hq
    by_cases hqa : q ≤ a
    · left
      have ho := (ordinary_left_run (k := K) (a := a) (q := q)
        (by omega) (by omega) hqa).2
      exact ⟨by
        have hr := ordinary_left_run (k := K) (a := a) (q := q)
          (by omega) (by omega) hqa
        simpa [row1, row2, K] using
          (phaseHorizontal K (by omega) ⟨0, by rw [phaseRows_length K (by omega)]; omega⟩
            (3 * q + 1) (by omega)
            (by change PhaseOccupied K ((phaseRows K)[0]'(by
                rw [phaseRows_length K (by omega)]; omega)) _; rw [hrow]; exact hr.1)
            (by change PhaseOccupied K ((phaseRows K)[0]'(by
                rw [phaseRows_length K (by omega)]; omega)) _; rw [hrow]; exact hr.2)).symm.reachable,
        by simpa [row1, K] using (topInterface k hk (3 * q + 2) (by omega) (by omega) ho
          (seam_left_run (k := k + 2) (a := k - 1) (q := q)
            (by omega) (by omega) (by omega)).2)⟩
    · right
      have hr := ordinary_right_run (k := K) (a := a) (q := q + 1)
        (by omega) (by omega) (by omega)
      exact ⟨by
        simpa [row1, row2, K] using
          (phaseHorizontal K (by omega) ⟨0, by rw [phaseRows_length K (by omega)]; omega⟩
            (3 * (q + 1)) (by omega)
            (by change PhaseOccupied K ((phaseRows K)[0]'(by
                rw [phaseRows_length K (by omega)]; omega)) _; rw [hrow]; exact hr.1)
            (by change PhaseOccupied K ((phaseRows K)[0]'(by
                rw [phaseRows_length K (by omega)]; omega)) _; rw [hrow]; exact hr.2)).symm.reachable,
        by simpa [row1, K] using (topInterface k hk (3 * (q + 1)) (by omega) (by omega) hr.1
          (seam_right_run (k := k + 2) (a := k - 1) (q := q + 1)
            (by omega) (by omega) (by omega)).1)⟩

private theorem interiorRowAttachment (k : Nat) (hk : 7 ≤ k)
    (r c : Fin (3 * (k + 1) - 1)) (hr0 : 3 ≤ r.val)
    (hrlast : r.val < 3 * k) :
    AttachesToWidenedOldInterior k hk (r, c) := by
  by_cases hc : c.val < 3 * k - 1
  · let c₀ : Fin (3 * k - 1) := ⟨c.val, hc⟩
    let r₀ : Fin (3 * k - 1) := ⟨r.val - 2, by omega⟩
    refine ⟨r₀, by simp [r₀]; omega, by simp [r₀]; omega, c₀, ?_⟩
    have heq : widenBoundedFace k (r₀, c₀) =
        ((r, c) : Fin (3 * (k + 1) - 1) ×
          Fin (3 * (k + 1) - 1)) := by
      apply Prod.ext <;> apply Fin.ext <;> simp [widenBoundedFace, r₀, c₀] <;> omega
    rw [heq]
  · refine ⟨(residueZeroAnchorCoord k hk).1, ?_, ?_,
      (residueZeroAnchorCoord k hk).2, ?_⟩
    · simp [residueZeroAnchorCoord]; omega
    · simp [residueZeroAnchorCoord]; omega
    · have hroute := persistentResidueZeroStepGeometry_rightSlab k hk
        r c hr0 hrlast (by omega)
      exact hroute.trans (persistentResidueZeroStepGeometry_anchorBridge k hk).symm

private theorem rowThreeAttachment (k : Nat) (hk : 7 ≤ k)
    (c : Fin (3 * (k + 1) - 1)) :
    AttachesToWidenedOldInterior k hk (⟨3, by omega⟩, c) := by
  let r : Fin (3 * (k + 1) - 1) := ⟨3, by omega⟩
  simpa [r] using interiorRowAttachment k hk r c (by simp [r]) (by simp [r]; omega)

private theorem rowTwoAttachment (k : Nat) (hk : 7 ≤ k)
    (c : Fin (3 * (k + 1) - 1)) :
    AttachesToWidenedOldInterior k hk (⟨2, by omega⟩, c) := by
  let q := c.val / 3
  let a := k - 2
  have hq : q < k + 1 := by dsimp [q]; have := c.isLt; omega
  have hc : c.val = 3 * q + c.val % 3 := by dsimp [q]; omega
  have hm : c.val % 3 = 0 ∨ c.val % 3 = 1 ∨ c.val % 3 = 2 := by
    have := Nat.mod_lt c.val (by omega : 0 < 3)
    omega
  have hrowO : (phaseRows (k + 1))[0]'(by
      rw [phaseRows_length (k + 1) (by omega)]; omega) = .ordinary a := by
    simp [a, phaseRows_succ k hk]
  have hrowS : (phaseRows (k + 1))[1]'(by
      rw [phaseRows_length (k + 1) (by omega)]; omega) = .seam a := by
    simp [a, phaseRows_succ k hk]
  have vertical (d : Nat) (hd0 : 0 < d) (hd : d < 3 * (k + 1) - 1)
      (ho : PhaseOccupied (k + 1) (.ordinary a) d)
      (hs : PhaseOccupied (k + 1) (.seam a) d) :
      (persistentResidueZeroGraph (k + 1) (by omega)).Adj
        (⟨2, by omega⟩, ⟨d - 1, by omega⟩)
        (⟨2, by omega⟩, ⟨d, hd⟩) := by
    exact phaseVertical (k + 1) (by omega) 0 d
      (by rw [phaseRows_length (k + 1) (by omega)]; omega) hd0 hd
      (by simpa [hrowO] using ho) (by simpa [hrowS] using hs)
  have cross (d : Nat) (hd : d < 3 * (k + 1) - 1)
      (h₀ : PhaseOccupied (k + 1) (.seam a) d)
      (h₁ : PhaseOccupied (k + 1) (.seam a) (d + 1)) :
      (persistentResidueZeroGraph (k + 1) (by omega)).Adj
        (⟨2, by omega⟩, ⟨d, hd⟩) (⟨3, by omega⟩, ⟨d, hd⟩) := by
    exact phaseHorizontal (k + 1) (by omega)
      ⟨1, by rw [phaseRows_length (k + 1) (by omega)]; omega⟩ d hd
      (by simpa [hrowS] using h₀) (by simpa [hrowS] using h₁)
  have finish (d : Fin (3 * (k + 1) - 1))
      (hmove : (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
        (⟨2, by omega⟩, c) (⟨2, by omega⟩, d))
      (hcross : (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
        (⟨2, by omega⟩, d) (⟨3, by omega⟩, d)) :
      AttachesToWidenedOldInterior k hk (⟨2, by omega⟩, c) := by
    rcases rowThreeAttachment k hk d with ⟨r₀, hr₀, hr₀last, c₀, hfinish⟩
    exact ⟨r₀, hr₀, hr₀last, c₀, hmove.trans (hcross.trans hfinish)⟩
  by_cases hleft : q < a
  · have ho := ordinary_left_run (k := k + 1) (a := a) (q := q)
      (by omega) hq hleft.le
    have hs := seam_left_run (k := k + 1) (a := a) (q := q)
      (by omega) hq hleft
    let d : Fin (3 * (k + 1) - 1) := ⟨3 * q + 1, by omega⟩
    have e₁ := vertical (3 * q + 1) (by omega) (by omega) ho.1 hs.1
    have e₂ := vertical (3 * q + 2) (by omega) (by omega) ho.2 hs.2
    have hcross := (cross (3 * q + 1) (by omega) hs.1 hs.2).reachable
    rcases hm with hm | hm | hm
    · apply finish d (by
        convert e₁.reachable using 1 <;> apply Prod.ext <;> apply Fin.ext <;>
          simp [d] <;> omega) (by simpa [d] using hcross)
    · apply finish d (by
        have hcd : c = d := Fin.ext (by simp [d]; omega)
        simpa only [hcd] using
          (Reachable.refl ((⟨2, by omega⟩, d) : Fin (3 * (k + 1) - 1) × _)))
        (by simpa [d] using hcross)
    · apply finish d (by
        convert e₂.symm.reachable using 1 <;> apply Prod.ext <;> apply Fin.ext <;>
          simp [d] <;> omega) (by simpa [d] using hcross)
  · by_cases hpivot : q = a
    · have hpivot' : q = k - 2 := by simpa [a] using hpivot
      have ho := ordinary_left_run (k := k + 1) (a := a) (q := q)
        (by omega) hq (by omega)
      have ho' := ordinary_right_run (k := k + 1) (a := a) (q := q + 1)
        (by omega) (by omega) (by omega)
      have hs' := seam_right_run (k := k + 1) (a := a) (q := q + 1)
        (by omega) (by omega) (by omega)
      let d : Fin (3 * (k + 1) - 1) := ⟨3 * (q + 1), by omega⟩
      have hb := commonPhaseColumn_backbone (k := k + 1) (q := q)
        (top := .ordinary a) (bottom := .seam a) hq
      have e₁ := vertical (3 * q + 1) (by omega) (by omega)
        (by simpa [a, hpivot'] using hb.1) (by simpa [a, hpivot'] using hb.2)
      have eup₁ := phaseHorizontal (k + 1) (by omega)
        ⟨0, by rw [phaseRows_length (k + 1) (by omega)]; omega⟩ (3 * q + 1)
        (by omega) (by simpa [hrowO] using ho.1) (by simpa [hrowO] using ho.2)
      have eup₂ := phaseHorizontal (k + 1) (by omega)
        ⟨0, by rw [phaseRows_length (k + 1) (by omega)]; omega⟩ (3 * q + 2)
        (by omega) (by simpa [hrowO] using ho.2)
        (by simpa [hrowO] using ho'.1)
      have etop := topInterface k hk (3 * q + 2) (by omega) (by omega) ho.2
        (seam_left_run (k := k + 2) (a := k - 1) (q := q)
          (by omega) (by omega) (by omega)).2
      have e₃ := vertical (3 * (q + 1)) (by omega) (by omega) ho'.1 hs'.1
      have hcross := (cross (3 * (q + 1)) (by omega) hs'.1 hs'.2).reachable
      have hfromOne : (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
          (⟨2, by omega⟩, ⟨3 * q + 1, by omega⟩)
          (⟨2, by omega⟩, d) := by
        simpa [d] using eup₁.symm.reachable.trans
          (etop.reachable.trans (eup₂.reachable.trans e₃.reachable))
      rcases hm with hm | hm | hm
      · apply finish d (by
          convert e₁.reachable.trans hfromOne using 1 <;>
            apply Prod.ext <;> apply Fin.ext <;> simp [d] <;> omega)
          (by simpa [d] using hcross)
      · apply finish d (by
          convert hfromOne using 1 <;> apply Prod.ext <;> apply Fin.ext <;>
            simp [d] <;> omega) (by simpa [d] using hcross)
      · apply finish d (by
          convert e₃.reachable using 1 <;> apply Prod.ext <;> apply Fin.ext <;>
            simp [d] <;> omega) (by simpa [d] using hcross)
    · have hright : a < q := by omega
      have ho := ordinary_right_run (k := k + 1) (a := a) (q := q)
        (by omega) hq hright
      have hs := seam_right_run (k := k + 1) (a := a) (q := q)
        (by omega) hq hright
      rcases hm with hm | hm | hm
      · let d : Fin (3 * (k + 1) - 1) := ⟨3 * q, by omega⟩
        have hcross := (cross (3 * q) (by omega) hs.1 hs.2).reachable
        apply finish d (by
          have hcd : c = d := Fin.ext (by simp [d]; omega)
          simpa only [hcd] using
            (Reachable.refl ((⟨2, by omega⟩, d) : Fin (3 * (k + 1) - 1) × _)))
          (by simpa [d] using hcross)
      · let d : Fin (3 * (k + 1) - 1) := ⟨3 * q, by omega⟩
        have e₁ := vertical (3 * q + 1) (by omega) (by omega) ho.2 hs.2
        have hcross := (cross (3 * q) (by omega) hs.1 hs.2).reachable
        apply finish d (by
          convert e₁.symm.reachable using 1 <;> apply Prod.ext <;> apply Fin.ext <;>
            simp [d] <;> omega)
          (by simpa [d] using hcross)
      · have hq' : q + 1 < k + 1 := by have := c.isLt; omega
        have ho' := ordinary_right_run (k := k + 1) (a := a) (q := q + 1)
          (by omega) hq' (by omega)
        have hs' := seam_right_run (k := k + 1) (a := a) (q := q + 1)
          (by omega) hq' (by omega)
        let d : Fin (3 * (k + 1) - 1) := ⟨3 * (q + 1), by omega⟩
        have e₃ := vertical (3 * (q + 1)) (by omega) (by omega) ho'.1 hs'.1
        have hcross := (cross (3 * (q + 1)) (by omega) hs'.1 hs'.2).reachable
        apply finish d (by
          convert e₃.reachable using 1 <;> apply Prod.ext <;> apply Fin.ext <;>
            simp [d] <;> omega) (by simpa [d] using hcross)

private theorem appendedAttachment (k : Nat) (hk : 7 ≤ k)
    (c : Fin (3 * (k + 1) - 1)) :
    AttachesToWidenedOldInterior k hk (⟨3 * k, by omega⟩, c) := by
  let q := c.val / 3
  have hq : q < k + 1 := by dsimp [q]; have := c.isLt; omega
  have hc : c.val = 3 * q + c.val % 3 := by dsimp [q]; omega
  have hm : c.val % 3 = 0 ∨ c.val % 3 = 1 ∨ c.val % 3 = 2 := by
    have := Nat.mod_lt c.val (by omega : 0 < 3)
    omega
  have hr := ordinary_left_run (k := k + 1) (a := k) (q := q)
    (by omega) hq (by omega)
  let i : Fin (phaseRows (k + 1)).length :=
    ⟨(phaseRows (k + 1)).length - 1, by
      rw [phaseRows_length (k + 1) (by omega)]; omega⟩
  have hrow : (phaseRows (k + 1)).get i = .ordinary k := by
    rw [List.get_eq_getElem]
    rw [← List.getLast_eq_getElem (List.ne_nil_of_length_pos (by
      rw [phaseRows_length (k + 1) (by omega)]; omega))]
    exact phaseRows_getLast (k + 1) (by omega)
  let d : Fin (3 * (k + 1) - 1) := ⟨3 * q + 1, by omega⟩
  have hcross : (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
      (⟨3 * k, by omega⟩, d) (⟨3 * k - 1, by omega⟩, d) := by
    have e := phaseHorizontal (k + 1) (by omega) i (3 * q + 1) (by omega)
      (by rw [hrow]; exact hr.1) (by rw [hrow]; convert hr.2 using 1 <;> omega)
    convert e.symm.reachable using 1 <;> apply Prod.ext <;> apply Fin.ext <;>
      simp [i, d, phaseRows_length (k + 1) (by omega)] <;> omega
  have hmove : (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
      (⟨3 * k, by omega⟩, c) (⟨3 * k, by omega⟩, d) := by
    rcases hm with hm | hm | hm
    · have e := appendedInterface k hk (3 * q + 1) (by omega) (by omega) hr.1
        (ordinary_left_run (k := k + 2) (a := k + 1) (q := q)
          (by omega) (by omega) (by omega)).1
      convert e.reachable using 1 <;> apply Prod.ext <;> apply Fin.ext <;>
        simp [d] <;> omega
    · have hcd : c = d := Fin.ext (by simp [d]; omega)
      simpa only [hcd] using
        (Reachable.refl ((⟨3 * k, by omega⟩, d) : Fin (3 * (k + 1) - 1) × _))
    · have e := appendedInterface k hk (3 * q + 2) (by omega) (by omega) hr.2
        (ordinary_left_run (k := k + 2) (a := k + 1) (q := q)
          (by omega) (by omega) (by omega)).2
      convert e.symm.reachable using 1 <;> apply Prod.ext <;> apply Fin.ext <;>
        simp [d] <;> omega
  let r : Fin (3 * (k + 1) - 1) := ⟨3 * k - 1, by omega⟩
  rcases interiorRowAttachment k hk r d (by simp [r]; omega) (by simp [r]; omega) with
    ⟨r₀, hr₀, hr₀last, c₀, hfinish⟩
  refine ⟨r₀, hr₀, hr₀last, c₀, hmove.trans ?_⟩
  simpa [r] using hcross.trans hfinish

private theorem topAttachment (k : Nat) (hk : 7 ≤ k)
    (r c : Fin (3 * (k + 1) - 1)) (hr : r.val = 1 ∨ r.val = 2) :
    AttachesToWidenedOldInterior k hk (r, c) := by
  rcases hr with hr | hr
  · rcases topRowOneToTwo k hk c with ⟨d, htop⟩
    rcases rowTwoAttachment k hk d with ⟨r₀, hr₀, hr₀last, c₀, hfinish⟩
    refine ⟨r₀, hr₀, hr₀last, c₀, ?_⟩
    have hre : r = ⟨1, by omega⟩ := Fin.ext hr
    rw [hre]
    exact htop.trans hfinish
  · have hre : r = ⟨2, by omega⟩ := Fin.ext hr
    rw [hre]
    exact rowTwoAttachment k hk c

set_option maxHeartbeats 4000000 in
theorem residueZeroLocalAttachmentGaps (k : Nat) (hk : 7 ≤ k) :
    ResidueZeroLocalAttachmentGaps k hk := by
  refine ⟨?_, appendedAttachment k hk⟩
  refine ⟨(fun r c hr _ _ => topAttachment k hk r c hr), ?_, ?_, ?_, ?_⟩
  · exact topAttachment k hk _ _ (Or.inl rfl)
  · exact topAttachment k hk _ _ (Or.inl rfl)
  · exact rowTwoAttachment k hk _
  · exact rowTwoAttachment k hk _

theorem betterPersistentResidueZeroStepGeometry (k : Nat) (hk : 7 ≤ k) :
    BetterPersistentResidueZeroStepGeometry k hk :=
  (residueZeroLocalAttachmentGaps k hk).toBetterGeometry

theorem persistentResidueZeroCertificate (k : Nat) (hk : 7 ≤ k) :
    PersistentResidueZeroCertificate k hk :=
  persistentResidueZeroCertificate_of_betterGeometry
    betterPersistentResidueZeroStepGeometry k hk

theorem uuDualGraph_uResidueZero_connected (k : Nat) (hk : 7 ≤ k) :
    (uuDualGraph (uResidueZero k hk)).Connected :=
  uuDualGraph_uResidueZero_connected_of_betterGeometry
    betterPersistentResidueZeroStepGeometry k hk

theorem forced_compl_uResidueZero_isAcyclic (k : Nat) (hk : 7 ≤ k) :
    (forcedEdgeGraph (gridGraph (3 * k) (3 * k))
      (↑(uResidueZero k hk) : Set (GridVertex (3 * k) (3 * k)))ᶜ).IsAcyclic :=
  forced_compl_uResidueZero_isAcyclic_of_anchored k hk
    (persistentResidueZeroCertificate k hk).toAnchored

theorem exists_isTree_preserving_compl_uResidueZero (k : Nat) (hk : 7 ≤ k) :
    ∃ T : SimpleGraph (GridVertex (3 * k) (3 * k)),
      T ≤ gridGraph (3 * k) (3 * k) ∧ T.IsTree ∧
      ∀ ⦃v : GridVertex (3 * k) (3 * k)⦄,
        v ∈ (↑(uResidueZero k hk) : Set (GridVertex (3 * k) (3 * k)))ᶜ →
          preservesIncidentEdges (gridGraph (3 * k) (3 * k)) T v :=
  exists_isTree_preserving_compl_uResidueZero_of_anchored k hk
    (persistentResidueZeroCertificate k hk).toAnchored

theorem residueZero_le_maxPreserved (k : Nat) (hk : 7 ≤ k) :
    3 * k ^ 2 + 3 * k - 2 ≤ maxPreserved (3 * k) (3 * k) :=
  residueZero_le_maxPreserved_of_betterGeometry
    betterPersistentResidueZeroStepGeometry k hk

end GridGraphs
