import GridGraphs.ResidueZeroBase
import GridGraphs.ResidueZeroBridge

/-!
# Induction for the residue-zero construction

This file closes the symbolic widening induction.  The paths retained by the
anchored certificate are widened one step further than the paths currently in
use, so every edge used below is witnessed at two consecutive widths.
-/

namespace GridGraphs

open SimpleGraph

private theorem phaseOccupied_of_mem {k r c : Nat} (hk : 7 ≤ k)
    (hr0 : 2 ≤ r) (hrlast : r < 3 * k - 2) (hc : c < 3 * k)
    (hmem : ((⟨r, by omega⟩, ⟨c, by omega⟩) :
      GridVertex (3 * k) (3 * k)) ∈ uResidueZero k hk) :
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
          try omega
        have hieq : i = ⟨r - 2, by rw [phaseRows_length k hk]; omega⟩ :=
          Fin.ext hi
        rw [← hieq]
        refine ⟨j, ?_⟩
        have hcol := congrArg (fun v => v.2.val) hx
        simpa [residueZeroVertex] using hcol

private theorem phase_mem_widen_twice {k r c : Nat} (hk : 7 ≤ k)
    (hr0 : 2 ≤ r) (hrlast : r < 3 * k - 2) (hc : c < 3 * k)
    (hmem : ((⟨r, by omega⟩, ⟨c, by omega⟩) :
      GridVertex (3 * k) (3 * k)) ∈ uResidueZero k hk) :
    ((⟨r + 2, by omega⟩, ⟨c, by omega⟩) :
      GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
        uResidueZero (k + 1) (by omega) := by
  let i : Fin (phaseRows k).length :=
    ⟨r - 2, by rw [phaseRows_length k hk]; omega⟩
  have hocc := phaseOccupied_of_mem hk hr0 hrlast hc hmem
  have hparameter := phaseRows_parameter_lt k hk _
    (List.get_mem (phaseRows k) i)
  have hwide := hocc.widen hk hparameter
  convert old_phase_occupied_mem_widened k hk i c hwide using 1
  apply Prod.ext <;> apply Fin.ext
  · simp [i]
    omega
  · rfl

private def shiftFace (k : Nat) :
    GridFace (3 * (k + 1)) (3 * (k + 1)) →
      GridFace (3 * (k + 2)) (3 * (k + 2))
  | .out => .out
  | .cell r c => .cell ⟨r.val + 2, by omega⟩ ⟨c.val, by omega⟩

private theorem shiftFace_injective (k : Nat) : Function.Injective (shiftFace k) := by
  intro f g h
  cases f <;> cases g <;> simp [shiftFace] at h ⊢
  exact ⟨Fin.ext h.1, Fin.ext h.2⟩

private def faceRowTag {m n : Nat} : GridFace m n → Nat
  | .out => 0
  | .cell r _ => r.val + 1

private theorem widened_phase_adj_widens_again (k : Nat) (hk : 7 ≤ k)
    (x y : Fin (3 * k - 1) × Fin (3 * k - 1))
    (hx0 : 0 < x.1.val) (hxlast : x.1.val < 3 * k - 2)
    (hy0 : 0 < y.1.val) (hylast : y.1.val < 3 * k - 2)
    (h : (uuDualGraph (uResidueZero (k + 1) (by omega))).Adj
      (widenCell k x.1 x.2) (widenCell k y.1 y.2)) :
    (uuDualGraph (uResidueZero (k + 2) (by omega))).Adj
      (widenCell (k + 1) (widenBoundedFace k x).1 (widenBoundedFace k x).2)
      (widenCell (k + 1) (widenBoundedFace k y).1 (widenBoundedFace k y).2) := by
  change (uuDualGraph (uResidueZero (k + 2) (by omega))).Adj
    (shiftFace k (widenCell k x.1 x.2))
    (shiftFace k (widenCell k y.1 y.2))
  rcases h with ⟨hxy, hhorizontal | hvertical⟩
  · rcases hhorizontal with ⟨e, he₁, he₂, hends⟩
    have herow0 : 2 ≤ e.row.val := by
      rcases hends with hends | hends
      · rcases hends with ⟨h₁, h₂⟩
        simp only [horizontalDualEndpoints] at h₁
        split at h₁ <;> simp_all [widenCell, widenBoundedFace]
        omega
      · rcases hends with ⟨h₁, h₂⟩
        simp only [horizontalDualEndpoints] at h₂
        split at h₂ <;> simp_all [widenCell, widenBoundedFace]
        omega
    have herowlast : e.row.val < 3 * (k + 1) - 2 := by
      rcases hends with hends | hends
      · rcases hends with ⟨h₁, h₂⟩
        simp only [horizontalDualEndpoints] at h₂
        split at h₂ <;> simp_all [widenCell, widenBoundedFace]
        omega
      · rcases hends with ⟨h₁, h₂⟩
        simp only [horizontalDualEndpoints] at h₁
        split at h₁ <;> simp_all [widenCell, widenBoundedFace]
        omega
    let e' : HorizontalGridEdge (3 * (k + 2)) (3 * (k + 2)) :=
      ⟨⟨e.row.val + 2, by omega⟩, ⟨e.col.val, by omega⟩⟩
    refine ⟨?_, Or.inl ⟨e', ?_, ?_, ?_⟩⟩
    · exact fun heq => hxy (shiftFace_injective k heq)
    · have hm := phase_mem_widen_twice (k := k + 1) (r := e.row.val)
          (c := e.col.val) (by omega) herow0 herowlast
          (by have := e.col.isLt; omega) (by simpa [horizontalPrimalEndpoints] using he₁)
      simpa [e', horizontalPrimalEndpoints] using hm
    · have hm := phase_mem_widen_twice (k := k + 1) (r := e.row.val)
          (c := e.col.val + 1) (by omega) herow0 herowlast
          (by have := e.col.isLt; omega) (by simpa [horizontalPrimalEndpoints] using he₂)
      simpa [e', horizontalPrimalEndpoints] using hm
    · have htop : (horizontalDualEndpoints e').1 =
          shiftFace k (horizontalDualEndpoints e).1 := by
        simp [e', horizontalDualEndpoints, shiftFace,
          show e.row.val ≠ 0 by omega]
        omega
      have hbottom : (horizontalDualEndpoints e').2 =
          shiftFace k (horizontalDualEndpoints e).2 := by
        simp [e', horizontalDualEndpoints, shiftFace,
          show e.row.val + 1 ≠ 3 * (k + 1) by omega,
          show e.row.val + 2 + 1 ≠ 3 * (k + 2) by omega]
      rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨(congrArg (shiftFace k) h₁).trans htop.symm,
          (congrArg (shiftFace k) h₂).trans hbottom.symm⟩
      · exact Or.inr ⟨(congrArg (shiftFace k) h₁).trans hbottom.symm,
          (congrArg (shiftFace k) h₂).trans htop.symm⟩
  · rcases hvertical with ⟨e, he₁, he₂, hends⟩
    have herow0 : 2 ≤ e.row.val := by
      rcases hends with ⟨h₁, -⟩ | ⟨-, h₁⟩
      all_goals
        have hv := congrArg faceRowTag h₁
        simp only [verticalDualEndpoints] at hv
        split at hv
        · simp [faceRowTag, widenCell, widenBoundedFace] at hv
          try omega
        · simp [faceRowTag, widenCell, widenBoundedFace] at hv
          try omega
    have herowlast : e.row.val + 1 < 3 * (k + 1) - 2 := by
      rcases hends with ⟨h₁, -⟩ | ⟨-, h₁⟩
      all_goals
        have hv := congrArg faceRowTag h₁
        simp only [verticalDualEndpoints] at hv
        split at hv
        · simp [faceRowTag, widenCell, widenBoundedFace] at hv
          try omega
        · simp [faceRowTag, widenCell, widenBoundedFace] at hv
          omega
    have hecol0 : 0 < e.col.val := by
      rcases hends with ⟨h₁, -⟩ | ⟨-, h₁⟩
      all_goals
        simp only [verticalDualEndpoints] at h₁
        split at h₁
        · simp_all
        · exact Nat.pos_of_ne_zero (by assumption)
    have hecollast : e.col.val + 1 ≠ 3 * (k + 1) := by
      rcases hends with ⟨-, h₂⟩ | ⟨h₂, -⟩
      all_goals
        simp only [verticalDualEndpoints] at h₂
        split at h₂ <;> simp_all
    let e' : VerticalGridEdge (3 * (k + 2)) (3 * (k + 2)) :=
      ⟨⟨e.row.val + 2, by omega⟩, ⟨e.col.val, by omega⟩⟩
    refine ⟨fun heq => hxy (shiftFace_injective k heq),
      Or.inr ⟨e', ?_, ?_, ?_⟩⟩
    · have hm := phase_mem_widen_twice (k := k + 1) (r := e.row.val)
          (c := e.col.val) (by omega) herow0 (by omega)
          (by have := e.col.isLt; omega) (by simpa [verticalPrimalEndpoints] using he₁)
      simpa [e', verticalPrimalEndpoints] using hm
    · have hm := phase_mem_widen_twice (k := k + 1) (r := e.row.val + 1)
          (c := e.col.val) (by omega) (by omega) herowlast
          (by have := e.col.isLt; omega) (by simpa [verticalPrimalEndpoints] using he₂)
      simpa [e', verticalPrimalEndpoints] using hm
    · have hleft : (verticalDualEndpoints e').1 =
          shiftFace k (verticalDualEndpoints e).1 := by
        simp [e', verticalDualEndpoints, shiftFace, hecol0.ne']
      have hright : (verticalDualEndpoints e').2 =
          shiftFace k (verticalDualEndpoints e).2 := by
        simp [e', verticalDualEndpoints, shiftFace, hecollast,
          show e.col.val + 1 ≠ 3 * (k + 2) by
            have := e.col.isLt
            omega]
      rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨(congrArg (shiftFace k) h₁).trans hleft.symm,
          (congrArg (shiftFace k) h₂).trans hright.symm⟩
      · exact Or.inr ⟨(congrArg (shiftFace k) h₁).trans hright.symm,
          (congrArg (shiftFace k) h₂).trans hleft.symm⟩

/-- An edge between old interior coordinates which survived one widening also
survives the following widening.  This is the edge-level invariant required to
map a chosen phase path through two successor steps. -/
theorem widenableOldDualGraph_interior_adj_widen
    (k : Nat) (hk : 7 ≤ k)
    (x y : Fin (3 * k - 1) × Fin (3 * k - 1))
    (hx0 : 0 < x.1.val) (hxlast : x.1.val < 3 * k - 2)
    (hy0 : 0 < y.1.val) (hylast : y.1.val < 3 * k - 2)
    (h : (widenableOldDualGraph k hk).Adj x y) :
    (widenableOldDualGraph (k + 1) (by omega)).Adj
      (widenBoundedFace k x) (widenBoundedFace k y) := by
  exact ⟨h.2,
    widened_phase_adj_widens_again k hk x y hx0 hxlast hy0 hylast h.2⟩

/-- The stable successor obligation already contains all genuinely new-face
paths.  Projecting its edges to the current dual graph discharges `hnew`; only
the one-more-stable path construction remains. -/
theorem residueZeroAnchoredCertificate_succ_of_nextStable
    (k : Nat) (hk : 7 ≤ k)
    (hold : ResidueZeroAnchoredCertificate k hk)
    (hstable :
      ∀ (r : Fin (3 * (k + 1) - 1)), 0 < r.val →
        r.val < 3 * (k + 1) - 2 → ∀ c : Fin (3 * (k + 1) - 1),
          (widenableOldDualGraph (k + 1) (by omega)).Reachable (r, c)
            (residueZeroAnchorCoord (k + 1) (by omega))) :
    ResidueZeroAnchoredCertificate (k + 1) (by omega) := by
  apply residueZeroAnchoredCertificate_succ_of_newFaces_nextStable k hk hold
  · intro r hr0 hrlast c _
    simpa [residueZeroAnchor, residueZeroAnchorCoord] using
      (hstable r hr0 hrlast c).map
        (widenableOldDualToOld (k + 1) (by omega))
  · exact hstable

end GridGraphs
