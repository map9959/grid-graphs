import GridGraphs.Constructions.ResidueZero.ResidueZeroPersistent
import GridGraphs.Constructions.ResidueZero.ResidueZeroBridge

/-!
# The persistent successor anchor bridge

The bounded bridge from `ResidueZeroBridge` is exposed here edge by edge.  In
addition to belonging to the successor dual graph, every edge is shown to
survive the following widening and every endpoint keeps a strictly interior
row.
-/

namespace GridGraphs

open SimpleGraph

private theorem phaseOccupied_of_mem (k r c : Nat) (hk : 7 ≤ k)
    (hr0 : 2 ≤ r) (hrlast : r < 3 * k - 2) (hc : c < 3 * k)
    (hmem : ((⟨r, by omega⟩, ⟨c, by omega⟩) : GridVertex (3 * k) (3 * k)) ∈
      uResidueZero k hk) :
    PhaseOccupied k ((phaseRows k).get
      (⟨r - 2, by rw [phaseRows_length k hk]; omega⟩ :
        Fin (phaseRows k).length)) c := by
  rw [uResidueZero, Finset.mem_image] at hmem
  rcases hmem with ⟨x, -, hx⟩
  rcases x with d | x
  · have hrow := congrArg (fun v => v.1.val) hx
    simp [residueZeroVertex] at hrow
    omega
  · rcases x with d | x
    · have hrow := congrArg (fun v => v.1.val) hx
      simp [residueZeroVertex] at hrow
      omega
    · rcases x with d | x
      · have hrow := congrArg (fun v => v.1.val) hx
        simp [residueZeroVertex] at hrow
        omega
      · rcases x with ⟨i, j⟩
        have hi : i.val = r - 2 := by
          have hrow := congrArg (fun v => v.1.val) hx
          simp [residueZeroVertex] at hrow
          omega
        have hieq : i = ⟨r - 2, by rw [phaseRows_length k hk]; omega⟩ :=
          Fin.ext hi
        rw [← hieq]
        refine ⟨j, ?_⟩
        have hcol := congrArg (fun v => v.2.val) hx
        simpa [residueZeroVertex] using hcol

private theorem phase_mem_widen (k r c : Nat) (hk : 7 ≤ k)
    (hr0 : 2 ≤ r) (hrlast : r < 3 * k - 2) (hc : c < 3 * k)
    (hmem : ((⟨r, by omega⟩, ⟨c, by omega⟩) : GridVertex (3 * k) (3 * k)) ∈
      uResidueZero k hk) :
    ((⟨r + 2, by omega⟩, ⟨c, by omega⟩) :
      GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
        uResidueZero (k + 1) (by omega) := by
  let i : Fin (phaseRows k).length :=
    ⟨r - 2, by rw [phaseRows_length k hk]; omega⟩
  have hocc := phaseOccupied_of_mem k r c hk hr0 hrlast hc hmem
  have hp := phaseRows_parameter_lt k hk _ (List.get_mem (phaseRows k) i)
  have hwide := hocc.widen hk hp
  convert old_phase_occupied_mem_widened k hk i c hwide using 1
  apply Prod.ext <;> apply Fin.ext
  · simp [i]
    omega
  · rfl

private theorem finalPhaseMem (k : Nat) (hk : 7 ≤ k) (c : Nat)
    (hc : c = 3 * k - 1 ∨ c = 3 * k ∨ c = 3 * k + 1) :
    ((⟨3 * k - 1, by omega⟩, ⟨c, by omega⟩) :
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
  have hm := old_phase_occupied_mem_widened k hk i c (by
    rw [hi, phaseOccupied_ordinary_iff (by omega : k - 1 < k + 1)]
    rcases hc with rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨k - 1, by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨k, by omega, by omega, rfl⟩)
    · exact Or.inl ⟨k, by omega, rfl⟩)
  convert hm using 1
  apply Prod.ext <;> apply Fin.ext
  · simp [i, phaseRows_length k hk]
    omega
  · rfl

private theorem appendedPhaseMem (k : Nat) (hk : 7 ≤ k) (c : Nat)
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

private theorem appendedAt (k : Nat) (hk : 7 ≤ k) (c : Nat)
    (hc : c = 3 * k - 1 ∨ c = 3 * k + 1 ∨ c = 3 * k + 2) :
    ((⟨3 * k, by omega⟩, ⟨c, by omega⟩) :
      GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
        uResidueZero (k + 1) (by omega) := by
  apply appendedPhaseMem k hk
  rw [phaseOccupied_ordinary_iff (by omega : k < k + 1)]
  rcases hc with rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨k - 1, by omega, by omega, by omega⟩)
  · exact Or.inl ⟨k, by omega, rfl⟩
  · exact Or.inr (Or.inl ⟨k, by omega, by omega, rfl⟩)

private theorem nextAppendedAt (k : Nat) (hk : 7 ≤ k) (c : Nat)
    (hc : c = 3 * k + 1 ∨ c = 3 * k + 2) :
    ((⟨3 * k + 3, by omega⟩, ⟨c, by omega⟩) :
      GridVertex (3 * (k + 2)) (3 * (k + 2))) ∈
        uResidueZero (k + 2) (by omega) := by
  apply appendedPhaseMem (k + 1) (by omega)
  rw [phaseOccupied_ordinary_iff (by omega : k + 1 < k + 2)]
  rcases hc with rfl | rfl
  · exact Or.inl ⟨k, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨k, by omega, by omega, by omega⟩)

set_option maxHeartbeats 2000000

/-- The explicit old-anchor/slab/appended/new-anchor route is persistent for
every successor step. -/
theorem persistentResidueZeroStepGeometry_anchorBridge
    (k : Nat) (hk : 7 ≤ k) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
      (widenBoundedFace k (residueZeroAnchorCoord k hk))
      (residueZeroAnchorCoord (k + 1) (by omega)) := by
  let G := persistentResidueZeroGraph (k + 1) (by omega)
  let a : Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1) :=
    (⟨3 * k - 1, by omega⟩, ⟨3 * k - 2, by omega⟩)
  let b : Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1) :=
    (⟨3 * k - 1, by omega⟩, ⟨3 * k - 1, by omega⟩)
  let c : Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1) :=
    (⟨3 * k - 2, by omega⟩, ⟨3 * k - 1, by omega⟩)
  let d : Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1) :=
    (⟨3 * k - 2, by omega⟩, ⟨3 * k, by omega⟩)
  let e : Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1) :=
    (⟨3 * k - 1, by omega⟩, ⟨3 * k, by omega⟩)
  let f : Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1) :=
    (⟨3 * k - 1, by omega⟩, ⟨3 * k + 1, by omega⟩)
  let g : Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1) :=
    (⟨3 * k, by omega⟩, ⟨3 * k + 1, by omega⟩)
  let h : Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1) :=
    (⟨3 * k, by omega⟩, ⟨3 * k, by omega⟩)
  have interior (x : Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1))
      (hx0 : 0 < x.1.val) (hxlast : x.1.val < 3 * (k + 1) - 2) :
      IsStrictInteriorResidueZeroCoord (k + 1) x := ⟨hx0, hxlast⟩
  have package {x y : Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1)}
      (hnow : (uuDualGraph (uResidueZero (k + 1) (by omega))).Adj
        (.cell x.1 x.2) (.cell y.1 y.2))
      (hnext : (uuDualGraph (uResidueZero (k + 2) (by omega))).Adj
        (widenCell (k + 1) x.1 x.2) (widenCell (k + 1) y.1 y.2))
      (hx : IsStrictInteriorResidueZeroCoord (k + 1) x)
      (hy : IsStrictInteriorResidueZeroCoord (k + 1) y) : G.Adj x y :=
    ⟨⟨hnow, hnext⟩, hx, hy⟩
  have hab : G.Adj a b := by
    refine package (x := a) (y := b) ?_ ?_ ?_ ?_
    · change (uuDualGraph (uResidueZero (k + 1) (by omega))).Adj
        (.cell ⟨3 * k - 1, by omega⟩ ⟨3 * k - 2, by omega⟩)
        (.cell ⟨3 * k - 1, by omega⟩ ⟨3 * k - 1, by omega⟩)
      exact vertical_uu_dual_cells_adj _ (3 * k - 1) (3 * k - 1)
        (by omega) (by omega) (by omega)
        (finalPhaseMem k hk _ (Or.inl rfl))
        (by simpa only [show 3 * k - 1 + 1 = 3 * k by omega] using
          appendedAt k hk _ (Or.inl rfl))
    · simp only [a, b, widenCell, widenBoundedFace]
      exact vertical_uu_dual_cells_adj _ (3 * k - 1 + 2) (3 * k - 1)
        (by omega) (by omega) (by omega)
        (by simpa only [show k + 1 + 1 = k + 2 by omega] using
          (phase_mem_widen (k + 1) (3 * k - 1) (3 * k - 1)
            (by omega) (by omega) (by omega) (by omega)
            (finalPhaseMem k hk _ (Or.inl rfl))))
        (by simpa only [show 3 * k + 2 = (3 * k - 1 + 2) + 1 by omega,
            show k + 1 + 1 = k + 2 by omega] using
          (phase_mem_widen (k + 1) (3 * k) (3 * k - 1)
            (by omega) (by omega) (by omega) (by omega)
            (appendedAt k hk _ (Or.inl rfl))))
    · exact interior a (by simp [a]; omega) (by simp [a]; omega)
    · exact interior b (by simp [b]; omega) (by simp [b]; omega)
  have hbc : G.Adj b c := by
    refine package (x := b) (y := c) ?_ ?_ ?_ ?_
    · convert (horizontal_uu_dual_cells_adj _ (3 * k - 1) (3 * k - 1)
        (by omega) (by omega) (by omega)
        (finalPhaseMem k hk _ (Or.inl rfl))
        (finalPhaseMem k hk (3 * k - 1 + 1)
          (Or.inr (Or.inl (by omega))))).symm using 1
      simp [c]
      omega
    · have hn := (horizontal_uu_dual_cells_adj
          (uResidueZero (k + 2) (by omega))
          (3 * k - 1 + 2) (3 * k - 1) (by omega) (by omega) (by omega)
          (phase_mem_widen (k + 1) (3 * k - 1) (3 * k - 1)
            (by omega) (by omega) (by omega) (by omega)
            (finalPhaseMem k hk _ (Or.inl rfl)))
          (phase_mem_widen (k + 1) (3 * k - 1) (3 * k - 1 + 1)
            (by omega) (by omega) (by omega) (by omega)
            (finalPhaseMem k hk _ (Or.inr (Or.inl (by omega)))))).symm
      convert hn using 1 <;> apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
        simp [b, c, widenBoundedFace]
      omega
    · exact interior b (by simp [b]; omega) (by simp [b]; omega)
    · exact interior c (by simp [c]; omega) (by simp [c]; omega)
  have hcd : G.Adj c d := by
    refine package (x := c) (y := d) ?_ ?_ ?_ ?_
    · convert old_phase_right_slab_horizontal_step k hk
        (3 * k - 6) (by rw [phaseRows_length k hk]; omega) using 1 <;>
        apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> simp [c, d] <;> omega
    · have ht := (old_phase_right_slab_run k hk
          ⟨3 * k - 6, by rw [phaseRows_length k hk]; omega⟩).1
      have hb := (old_phase_right_slab_run k hk
          ⟨3 * k - 5, by rw [phaseRows_length k hk]; omega⟩).1
      have ht' : ((⟨3 * k - 2, by omega⟩, ⟨3 * k, by omega⟩) :
          GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
          uResidueZero (k + 1) (by omega) := by
        convert ht using 1
        apply Prod.ext <;> apply Fin.ext <;> simp
        omega
      have hb' : ((⟨3 * k - 1, by omega⟩, ⟨3 * k, by omega⟩) :
          GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
          uResidueZero (k + 1) (by omega) := by
        convert hb using 1
        apply Prod.ext <;> apply Fin.ext <;> simp
        omega
      have hn := vertical_uu_dual_cells_adj (uResidueZero (k + 2) (by omega))
          (3 * k) (3 * k) (by omega) (by omega) (by omega)
          (by simpa only [show 3 * k - 2 + 2 = 3 * k by omega,
              show k + 1 + 1 = k + 2 by omega] using
            (phase_mem_widen (k + 1) (3 * k - 2) (3 * k)
              (by omega) (by omega) (by omega) (by omega) ht'))
          (by simpa only [show 3 * k - 1 + 2 = 3 * k + 1 by omega,
              show k + 1 + 1 = k + 2 by omega] using
            (phase_mem_widen (k + 1) (3 * k - 1) (3 * k)
              (by omega) (by omega) (by omega) (by omega) hb'))
      convert hn using 1 <;> apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
        simp [c, d, widenBoundedFace] <;> omega
    · exact interior c (by simp [c]; omega) (by simp [c]; omega)
    · exact interior d (by simp [d]; omega) (by simp [d]; omega)
  have hde : G.Adj d e := by
    refine package (x := d) (y := e) ?_ ?_ ?_ ?_
    · convert old_phase_right_slab_vertical_step k hk
        ⟨3 * k - 5, by rw [phaseRows_length k hk]; omega⟩ using 1 <;>
        apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> simp [d, e] <;> omega
    · have ml : ((⟨3 * k + 1, by omega⟩, ⟨3 * k, by omega⟩) :
          GridVertex (3 * (k + 2)) (3 * (k + 2))) ∈
          uResidueZero (k + 2) (by omega) := by
        simpa only [show 3 * k - 1 + 2 = 3 * k + 1 by omega,
            show k + 1 + 1 = k + 2 by omega] using
          (phase_mem_widen (k + 1) (3 * k - 1) (3 * k) (by omega)
            (by omega) (by omega) (by omega)
            (finalPhaseMem k hk _ (Or.inr (Or.inl rfl))))
      have mr : ((⟨3 * k + 1, by omega⟩, ⟨3 * k + 1, by omega⟩) :
          GridVertex (3 * (k + 2)) (3 * (k + 2))) ∈
          uResidueZero (k + 2) (by omega) := by
        simpa only [show 3 * k - 1 + 2 = 3 * k + 1 by omega,
            show k + 1 + 1 = k + 2 by omega] using
          (phase_mem_widen (k + 1) (3 * k - 1) (3 * k + 1) (by omega)
            (by omega) (by omega) (by omega)
            (finalPhaseMem k hk _ (Or.inr (Or.inr rfl))))
      have hn := horizontal_uu_dual_cells_adj
        (uResidueZero (k + 2) (by omega)) (3 * k + 1) (3 * k)
        (by omega) (by omega) (by omega) ml mr
      convert hn using 1 <;> apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
        simp [d, e, widenBoundedFace] <;> omega
    · exact interior d (by simp [d]; omega) (by simp [d]; omega)
    · exact interior e (by simp [e]; omega) (by simp [e]; omega)
  have hef : G.Adj e f := by
    refine package (x := e) (y := f) ?_ ?_ ?_ ?_
    · simpa only [e, f, Nat.add_sub_cancel] using
        vertical_uu_dual_cells_adj _ (3 * k - 1) (3 * k + 1)
        (by omega) (by omega) (by omega)
        (finalPhaseMem k hk _ (Or.inr (Or.inr rfl)))
        (by simpa only [show 3 * k - 1 + 1 = 3 * k by omega] using
          appendedAt k hk _ (Or.inr (Or.inl rfl)))
    · have mt : ((⟨3 * k + 1, by omega⟩, ⟨3 * k + 1, by omega⟩) :
          GridVertex (3 * (k + 2)) (3 * (k + 2))) ∈
          uResidueZero (k + 2) (by omega) := by
        simpa only [show 3 * k - 1 + 2 = 3 * k + 1 by omega,
            show k + 1 + 1 = k + 2 by omega] using
          (phase_mem_widen (k + 1) (3 * k - 1) (3 * k + 1) (by omega)
            (by omega) (by omega) (by omega)
            (finalPhaseMem k hk _ (Or.inr (Or.inr rfl))))
      have mb : ((⟨3 * k + 2, by omega⟩, ⟨3 * k + 1, by omega⟩) :
          GridVertex (3 * (k + 2)) (3 * (k + 2))) ∈
          uResidueZero (k + 2) (by omega) := by
        exact phase_mem_widen (k + 1) (3 * k) (3 * k + 1) (by omega)
          (by omega) (by omega) (by omega)
          (appendedAt k hk _ (Or.inr (Or.inl rfl)))
      have hn := vertical_uu_dual_cells_adj (uResidueZero (k + 2) (by omega))
        (3 * k + 1) (3 * k + 1) (by omega) (by omega) (by omega) mt mb
      convert hn using 1 <;> apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
        simp [e, f, widenBoundedFace] <;> omega
    · exact interior e (by simp [e]; omega) (by simp [e]; omega)
    · exact interior f (by simp [f]; omega) (by simp [f]; omega)
  have hfg : G.Adj f g := by
    refine package (x := f) (y := g) ?_ ?_ ?_ ?_
    · simpa [f, g] using horizontal_uu_dual_cells_adj _ (3 * k) (3 * k + 1)
        (by omega) (by omega) (by omega)
        (appendedAt k hk _ (Or.inr (Or.inl rfl)))
        (appendedAt k hk _ (Or.inr (Or.inr rfl)))
    · have ml : ((⟨3 * k + 2, by omega⟩, ⟨3 * k + 1, by omega⟩) :
          GridVertex (3 * (k + 2)) (3 * (k + 2))) ∈
          uResidueZero (k + 2) (by omega) := by
        exact phase_mem_widen (k + 1) (3 * k) (3 * k + 1) (by omega)
          (by omega) (by omega) (by omega)
          (appendedAt k hk _ (Or.inr (Or.inl rfl)))
      have mr : ((⟨3 * k + 2, by omega⟩, ⟨3 * k + 2, by omega⟩) :
          GridVertex (3 * (k + 2)) (3 * (k + 2))) ∈
          uResidueZero (k + 2) (by omega) := by
        exact phase_mem_widen (k + 1) (3 * k) (3 * k + 2) (by omega)
          (by omega) (by omega) (by omega)
          (appendedAt k hk _ (Or.inr (Or.inr rfl)))
      have hn := horizontal_uu_dual_cells_adj
        (uResidueZero (k + 2) (by omega)) (3 * k + 2) (3 * k + 1)
        (by omega) (by omega) (by omega) ml mr
      convert hn using 1 <;> apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
        simp [f, g, widenBoundedFace]
      omega
    · exact interior f (by simp [f]; omega) (by simp [f]; omega)
    · exact interior g (by simp [g]; omega) (by simp [g]; omega)
  have hhg : G.Adj h g := by
    refine package (x := h) (y := g) ?_ ?_ ?_ ?_
    · simpa [h, g] using vertical_uu_dual_cells_adj _ (3 * k) (3 * k + 1)
        (by omega) (by omega) (by omega)
        (appendedAt k hk _ (Or.inr (Or.inl rfl)))
        (penultimate_cap_mem_uResidueZero (k + 1) (by omega) (3 * k + 1)
          (by omega) (by omega))
    · simpa [h, g, widenCell, widenBoundedFace] using
        vertical_uu_dual_cells_adj (uResidueZero (k + 2) (by omega))
          (3 * k + 2) (3 * k + 1) (by omega) (by omega) (by omega)
          (by simpa only [show k + 1 + 1 = k + 2 by omega] using
            (phase_mem_widen (k + 1) (3 * k) (3 * k + 1) (by omega)
              (by omega) (by omega) (by omega)
              (appendedAt k hk _ (Or.inr (Or.inl rfl)))))
          (by simpa only [show 3 * k + 2 + 1 = 3 * k + 3 by omega] using
            nextAppendedAt k hk _ (Or.inl rfl))
    · exact interior h (by simp [h]; omega) (by simp [h]; omega)
    · exact interior g (by simp [g]; omega) (by simp [g]; omega)
  have hstart : widenBoundedFace k (residueZeroAnchorCoord k hk) = a := by
    apply Prod.ext <;> apply Fin.ext <;>
      simp [widenBoundedFace, residueZeroAnchorCoord, a]
    omega
  have hend : residueZeroAnchorCoord (k + 1) (by omega) = g := by
    apply Prod.ext <;> apply Fin.ext <;>
      simp [residueZeroAnchorCoord, g] <;> omega
  rw [hstart, hend]
  exact hab.reachable.trans (hbc.reachable.trans (hcd.reachable.trans
    (hde.reachable.trans (hef.reachable.trans (hfg.reachable.trans
      (hhg.symm.reachable.trans hhg.reachable))))))

end GridGraphs
