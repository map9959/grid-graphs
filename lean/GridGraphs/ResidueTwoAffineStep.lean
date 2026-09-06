import GridGraphs.ResidueTwoAffine
import GridGraphs.ConnectivityTransport
import GridGraphs.FiniteDiagonalSeventeen
import GridGraphs.ResidueZeroDual

/-!
# One-step geometry for the affine residue-two family

This module separates the topological induction from the remaining local
geometry.  A width-three step need not preserve an old dual edge as one edge:
it is enough to replace each crossed horizontal or vertical edge by a path.
The final field says that every successor face attaches to an embedded old
face.  Thus the structure is an exact list of the symbolic local obligations
needed for one affine step.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 14000000
set_option maxRecDepth 100000

/-- The base predicate as a finset, used to keep the dependent affine image
separate from the fixed row-table comparison. -/
private def residueTwoAffineBase : Finset (GridVertex 17 17) :=
  Finset.univ.filter fun v => IsResidueTwoAffineBase v.1 v.2

/-- At zero pumping, the symbolic occurrence image is exactly the base
predicate. -/
private theorem uResidueTwoAffine_five_eq_base :
    uResidueTwoAffine 5 = residueTwoAffineBase := by
  classical
  ext v
  simp only [uResidueTwoAffine, dif_pos (by omega : 5 ≤ 5),
    Finset.mem_image, residueTwoAffineOccurrences, Finset.mem_univ, true_and,
    residueTwoAffineBase, Finset.mem_filter]
  constructor
  · rintro ⟨x, hx⟩
    have hr : x.1 = v.1 := Fin.ext (by
      have h := congrArg (fun z => z.1.val) hx
      have hcopy : x.2.2.val.1.val = 0 := by
        have := x.2.2.val.1.isLt
        by_cases hp : 9 ≤ x.1.val ∧ x.1.val < 9 + 3
        · have hlt : x.2.2.val.1.val < 0 + 1 := by
            simpa only [Nat.sub_self, residueTwoPumpMultiplicity, if_pos hp] using this
          clear this
          omega
        · have hlt : x.2.2.val.1.val < 1 := by
            simpa only [Nat.sub_self, residueTwoPumpMultiplicity, if_neg hp] using this
          clear this
          omega
      simpa [residueTwoAffineVertex, residueTwoExpandIndex,
        residueTwoPumpMultiplicity, hcopy] using h)
    have hc : x.2.1 = v.2 := Fin.ext (by
      have h := congrArg (fun z => z.2.val) hx
      have hcopy : x.2.2.val.2.val = 0 := by
        have := x.2.2.val.2.isLt
        by_cases hp : 4 ≤ x.2.1.val ∧ x.2.1.val < 4 + 3
        · have hlt : x.2.2.val.2.val < 0 + 1 := by
            simpa only [Nat.sub_self, residueTwoPumpMultiplicity, if_pos hp] using this
          clear this
          omega
        · have hlt : x.2.2.val.2.val < 1 := by
            simpa only [Nat.sub_self, residueTwoPumpMultiplicity, if_neg hp] using this
          clear this
          omega
      simpa [residueTwoAffineVertex, residueTwoExpandIndex,
        residueTwoPumpMultiplicity, hcopy] using h)
    simpa [← hr, ← hc] using x.2.2.property
  · intro hv
    let copies :
        {p : Fin (residueTwoPumpMultiplicity 9 0 v.1) ×
          Fin (residueTwoPumpMultiplicity 4 0 v.2) //
          IsResidueTwoAffineBase v.1 v.2} :=
      ⟨(⟨0, by simp [residueTwoPumpMultiplicity]⟩,
        ⟨0, by simp [residueTwoPumpMultiplicity]⟩), hv⟩
    let x : ResidueTwoAffineOccurrence 0 := ⟨v.1, v.2, copies⟩
    refine ⟨x, ?_⟩
    apply Prod.ext <;> apply Fin.ext <;>
      simp [x, copies, residueTwoAffineVertex, residueTwoExpandIndex]

/-- The fixed base predicate is the explicit seventeen-by-seventeen table. -/
private theorem residueTwoAffineBase_eq_finiteU17 :
    residueTwoAffineBase = finiteU17 := by rfl

/-- The affine base is the explicit seventeen-by-seventeen construction. -/
theorem uResidueTwoAffine_five : uResidueTwoAffine 5 = finiteU17 :=
  uResidueTwoAffine_five_eq_base.trans residueTwoAffineBase_eq_finiteU17

/-- Unconditional dual connectivity at the affine base. -/
theorem uResidueTwoAffine_five_dual_connected :
    (uuDualGraph (uResidueTwoAffine 5)).Connected := by
  rw [uResidueTwoAffine_five]
  exact finiteU17RankedDualCertificate.connected

/-- Embed old faces across the next affine copy.  From the coordinate expansion,
the appended copies start at row `9 + 3*(k-5) = 3k-6` and column
`4 + 3*(k-5) = 3k-11`; faces on or beyond either cut shift by three. -/
def residueTwoAffineStepFace (k : Nat) :
    GridFace (3 * k + 2) (3 * k + 2) →
      GridFace (3 * (k + 1) + 2) (3 * (k + 1) + 2)
  | .out => .out
  | .cell r c =>
      .cell
        ⟨if 3 * k - 6 ≤ r.val then r.val + 3 else r.val, by
          split <;> have := r.isLt <;> omega⟩
         ⟨if 3 * k - 11 ≤ c.val then c.val + 3 else c.val, by
           split <;> have := c.isLt <;> omega⟩

/-- Every successor face outside the inserted three-row and three-column slabs
has a unique old-coordinate preimage. -/
private theorem exists_residueTwoAffineStepFace_preimage
    (k : Nat) (hk : 5 ≤ k)
    (r c : Fin (3 * (k + 1) + 1))
    (hr : r.val < 3 * k - 6 ∨ 3 * k - 3 ≤ r.val)
    (hc : c.val < 3 * k - 11 ∨ 3 * k - 8 ≤ c.val) :
    ∃ y : GridFace (3 * k + 2) (3 * k + 2),
      residueTwoAffineStepFace k y = .cell r c := by
  let oldRow : Fin (3 * k + 1) :=
    ⟨if r.val < 3 * k - 6 then r.val else r.val - 3, by
      split
      · omega
      · have := r.isLt
        omega⟩
  let oldCol : Fin (3 * k + 1) :=
    ⟨if c.val < 3 * k - 11 then c.val else c.val - 3, by
      split
      · omega
      · have := c.isLt
        omega⟩
  refine ⟨.cell oldRow oldCol, ?_⟩
  simp only [residueTwoAffineStepFace]
  apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
    simp only [oldRow, oldCol] <;> split_ifs <;> omega

/-- A successor cell outside both inserted slabs already lies in the embedded
old face set, so it attaches by the empty path. -/
theorem residueTwoAffineStepFace_regular_reachable
    (k : Nat) (hk : 5 ≤ k)
    (r c : Fin (3 * (k + 1) + 1))
    (hr : r.val < 3 * k - 6 ∨ 3 * k - 3 ≤ r.val)
    (hc : c.val < 3 * k - 11 ∨ 3 * k - 8 ≤ c.val) :
    ∃ y : GridFace (3 * k + 2) (3 * k + 2),
      (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable (.cell r c)
        (residueTwoAffineStepFace k y) := by
  obtain ⟨y, hy⟩ := exists_residueTwoAffineStepFace_preimage k hk r c hr hc
  exact ⟨y, hy ▸ SimpleGraph.Reachable.refl _⟩

/-- Away from the row seam separating its dual cells and the column seam
separating its primal vertices, an old interior horizontal U-U edge remains a
single dual edge after the affine insertion. -/
theorem residueTwoAffineStep_horizontal_regular_adj
    (k : Nat) (hk : 5 ≤ k)
    (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2))
    (hrow0 : 0 < e.row.val) (hrowLast : e.row.val + 1 < 3 * k + 2)
    (hdualSeam : e.row.val ≠ 3 * k - 6)
    (hprimalSeam : e.col.val + 1 ≠ 3 * k - 11)
    (he₁ : (horizontalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (horizontalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Adj
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).1)
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).2) := by
  let e' : HorizontalGridEdge (3 * (k + 1) + 2) (3 * (k + 1) + 2) :=
    ⟨⟨if 3 * k - 6 ≤ e.row.val then e.row.val + 3 else e.row.val, by
        split <;> have := e.row.isLt <;> omega⟩,
      ⟨if 3 * k - 11 ≤ e.col.val then e.col.val + 3 else e.col.val, by
        split <;> have := e.col.isLt <;> omega⟩⟩
  have he₁' : (horizontalPrimalEndpoints e').1 ∈
      uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffineStepVertex_mem k hk he₁
    rw [← show residueTwoAffineStepVertex k (horizontalPrimalEndpoints e).1 =
        (horizontalPrimalEndpoints e').1 by rfl]
    exact hm
  have he₂' : (horizontalPrimalEndpoints e').2 ∈
      uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffineStepVertex_mem k hk he₂
    rw [← show residueTwoAffineStepVertex k (horizontalPrimalEndpoints e).2 =
        (horizontalPrimalEndpoints e').2 by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change (if 3 * k - 11 ≤ e.col.val + 1 then e.col.val + 1 + 3
          else e.col.val + 1) =
          (if 3 * k - 11 ≤ e.col.val then e.col.val + 3 else e.col.val) + 1
        split_ifs <;> omega]
    exact hm
  have hrow0' : e'.row.val ≠ 0 := by
    simp only [e']
    split_ifs <;> omega
  have hrowLast' : e'.row.val + 1 ≠ 3 * (k + 1) + 2 := by
    simp only [e']
    split_ifs <;> omega
  have htop : (horizontalDualEndpoints e').1 =
      residueTwoAffineStepFace k (horizontalDualEndpoints e).1 := by
    simp only [horizontalDualEndpoints, dif_neg hrow0', dif_neg hrow0.ne']
    simp only [residueTwoAffineStepFace]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext
    · simp only [e']
      split_ifs <;> omega
    · rfl
  have hbottom : (horizontalDualEndpoints e').2 =
      residueTwoAffineStepFace k (horizontalDualEndpoints e).2 := by
    simp only [horizontalDualEndpoints, dif_neg hrowLast',
      dif_neg (by omega : e.row.val + 1 ≠ 3 * k + 2)]
    simp only [residueTwoAffineStepFace]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> rfl
  refine ⟨?_, Or.inl ⟨e', he₁', he₂', Or.inl ⟨htop.symm, hbottom.symm⟩⟩⟩
  rw [← htop, ← hbottom]
  simp only [horizontalDualEndpoints, dif_neg hrow0', dif_neg hrowLast']
  intro h
  simp only [GridFace.cell.injEq, Fin.mk.injEq] at h
  have hpos : 0 < e'.row.val := Nat.pos_of_ne_zero hrow0'
  omega

/-- The regular horizontal transport is in particular a successor dual path. -/
theorem residueTwoAffineStep_horizontal_regular_reachable
    (k : Nat) (hk : 5 ≤ k)
    (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2))
    (hrow0 : 0 < e.row.val) (hrowLast : e.row.val + 1 < 3 * k + 2)
    (hdualSeam : e.row.val ≠ 3 * k - 6)
    (hprimalSeam : e.col.val + 1 ≠ 3 * k - 11)
    (he₁ : (horizontalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (horizontalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).1)
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).2) :=
  (residueTwoAffineStep_horizontal_regular_adj k hk e hrow0 hrowLast
    hdualSeam hprimalSeam he₁ he₂).reachable

/-- Away from the row seam separating its primal vertices and the column seam
separating its dual cells, an old interior vertical U-U edge remains a single
dual edge after the affine insertion. -/
theorem residueTwoAffineStep_vertical_regular_adj
    (k : Nat) (hk : 5 ≤ k)
    (e : VerticalGridEdge (3 * k + 2) (3 * k + 2))
    (hcol0 : 0 < e.col.val) (hcolLast : e.col.val + 1 < 3 * k + 2)
    (hprimalSeam : e.row.val + 1 ≠ 3 * k - 6)
    (hdualSeam : e.col.val ≠ 3 * k - 11)
    (he₁ : (verticalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (verticalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Adj
      (residueTwoAffineStepFace k (verticalDualEndpoints e).1)
      (residueTwoAffineStepFace k (verticalDualEndpoints e).2) := by
  let e' : VerticalGridEdge (3 * (k + 1) + 2) (3 * (k + 1) + 2) :=
    ⟨⟨if 3 * k - 6 ≤ e.row.val then e.row.val + 3 else e.row.val, by
        split <;> have := e.row.isLt <;> omega⟩,
      ⟨if 3 * k - 11 ≤ e.col.val then e.col.val + 3 else e.col.val, by
        split <;> have := e.col.isLt <;> omega⟩⟩
  have he₁' : (verticalPrimalEndpoints e').1 ∈
      uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffineStepVertex_mem k hk he₁
    rw [← show residueTwoAffineStepVertex k (verticalPrimalEndpoints e).1 =
        (verticalPrimalEndpoints e').1 by rfl]
    exact hm
  have he₂' : (verticalPrimalEndpoints e').2 ∈
      uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffineStepVertex_mem k hk he₂
    rw [← show residueTwoAffineStepVertex k (verticalPrimalEndpoints e).2 =
        (verticalPrimalEndpoints e').2 by
      apply Prod.ext
      · apply Fin.ext
        change (if 3 * k - 6 ≤ e.row.val + 1 then e.row.val + 1 + 3
          else e.row.val + 1) =
          (if 3 * k - 6 ≤ e.row.val then e.row.val + 3 else e.row.val) + 1
        split_ifs <;> omega
      · rfl]
    exact hm
  have hcol0' : e'.col.val ≠ 0 := by
    simp only [e']
    split_ifs <;> omega
  have hcolLast' : e'.col.val + 1 ≠ 3 * (k + 1) + 2 := by
    simp only [e']
    split_ifs <;> omega
  have hleft : (verticalDualEndpoints e').1 =
      residueTwoAffineStepFace k (verticalDualEndpoints e).1 := by
    simp only [verticalDualEndpoints, dif_neg hcol0', dif_neg hcol0.ne']
    simp only [residueTwoAffineStepFace]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext
    · rfl
    · simp only [e']
      split_ifs <;> omega
  have hright : (verticalDualEndpoints e').2 =
      residueTwoAffineStepFace k (verticalDualEndpoints e).2 := by
    simp only [verticalDualEndpoints, dif_neg hcolLast',
      dif_neg (by omega : e.col.val + 1 ≠ 3 * k + 2)]
    simp only [residueTwoAffineStepFace]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> rfl
  refine ⟨?_, Or.inr ⟨e', he₁', he₂', Or.inl ⟨hleft.symm, hright.symm⟩⟩⟩
  rw [← hleft, ← hright]
  simp only [verticalDualEndpoints, dif_neg hcol0', dif_neg hcolLast']
  intro h
  simp only [GridFace.cell.injEq, Fin.mk.injEq] at h
  have hpos : 0 < e'.col.val := Nat.pos_of_ne_zero hcol0'
  omega

/-- The regular vertical transport is in particular a successor dual path. -/
theorem residueTwoAffineStep_vertical_regular_reachable
    (k : Nat) (hk : 5 ≤ k)
    (e : VerticalGridEdge (3 * k + 2) (3 * k + 2))
    (hcol0 : 0 < e.col.val) (hcolLast : e.col.val + 1 < 3 * k + 2)
    (hprimalSeam : e.row.val + 1 ≠ 3 * k - 6)
    (hdualSeam : e.col.val ≠ 3 * k - 11)
    (he₁ : (verticalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (verticalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (verticalDualEndpoints e).1)
      (residueTwoAffineStepFace k (verticalDualEndpoints e).2) :=
  (residueTwoAffineStep_vertical_regular_adj k hk e hcol0 hcolLast
    hprimalSeam hdualSeam he₁ he₂).reachable

/-- A horizontal U-U edge on the top or bottom boundary transports to a
successor dual edge whenever the insertion does not split its primal edge. -/
theorem residueTwoAffineStep_horizontal_boundary_reachable
    (k : Nat) (hk : 5 ≤ k)
    (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2))
    (hboundary : e.row.val = 0 ∨ e.row.val + 1 = 3 * k + 2)
    (hprimalSeam : e.col.val + 1 ≠ 3 * k - 11)
    (he₁ : (horizontalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (horizontalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).1)
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).2) := by
  let e' : HorizontalGridEdge (3 * (k + 1) + 2) (3 * (k + 1) + 2) :=
    ⟨⟨if 3 * k - 6 ≤ e.row.val then e.row.val + 3 else e.row.val, by
        split <;> have := e.row.isLt <;> omega⟩,
      ⟨if 3 * k - 11 ≤ e.col.val then e.col.val + 3 else e.col.val, by
        split <;> have := e.col.isLt <;> omega⟩⟩
  have he₁' : (horizontalPrimalEndpoints e').1 ∈
      uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffineStepVertex_mem k hk he₁
    rw [← show residueTwoAffineStepVertex k (horizontalPrimalEndpoints e).1 =
        (horizontalPrimalEndpoints e').1 by rfl]
    exact hm
  have he₂' : (horizontalPrimalEndpoints e').2 ∈
      uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffineStepVertex_mem k hk he₂
    rw [← show residueTwoAffineStepVertex k (horizontalPrimalEndpoints e).2 =
        (horizontalPrimalEndpoints e').2 by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change (if 3 * k - 11 ≤ e.col.val + 1 then e.col.val + 1 + 3
          else e.col.val + 1) =
          (if 3 * k - 11 ≤ e.col.val then e.col.val + 3 else e.col.val) + 1
        split_ifs <;> omega]
    exact hm
  have hadj : (uuDualGraph (uResidueTwoAffine (k + 1))).Adj
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).1)
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).2) := by
    rcases hboundary with htop | hbottom
    · have htop' : e'.row.val = 0 := by
        simp only [e', htop]
        split_ifs <;> omega
      have hbounded : (horizontalDualEndpoints e').2 =
          residueTwoAffineStepFace k (horizontalDualEndpoints e).2 := by
        simp only [horizontalDualEndpoints, dif_neg (by omega : e'.row.val + 1 ≠
          3 * (k + 1) + 2), dif_neg (by omega : e.row.val + 1 ≠ 3 * k + 2)]
        simp only [residueTwoAffineStepFace]
        apply congrArg₂ GridFace.cell <;> apply Fin.ext
        · simp only [e']
        · rfl
      have hout : (horizontalDualEndpoints e').1 =
          residueTwoAffineStepFace k (horizontalDualEndpoints e).1 := by
        simp [horizontalDualEndpoints, residueTwoAffineStepFace, htop, htop']
      refine ⟨?_, Or.inl ⟨e', he₁', he₂', Or.inl ⟨hout.symm, hbounded.symm⟩⟩⟩
      rw [← hout, ← hbounded]
      simp [horizontalDualEndpoints, htop']
    · have hbottom' : e'.row.val + 1 = 3 * (k + 1) + 2 := by
        simp only [e']
        split_ifs <;> omega
      have hrow0' : e'.row.val ≠ 0 := by omega
      have hbounded : (horizontalDualEndpoints e').1 =
          residueTwoAffineStepFace k (horizontalDualEndpoints e).1 := by
        simp only [horizontalDualEndpoints, dif_neg (by omega : e'.row.val ≠ 0),
          dif_neg (by omega : e.row.val ≠ 0), residueTwoAffineStepFace]
        apply congrArg₂ GridFace.cell <;> apply Fin.ext
        · simp only [e']
          split_ifs <;> omega
        · rfl
      have hout : (horizontalDualEndpoints e').2 =
          residueTwoAffineStepFace k (horizontalDualEndpoints e).2 := by
        simp [horizontalDualEndpoints, residueTwoAffineStepFace, hbottom, hbottom']
      refine ⟨?_, Or.inl ⟨e', he₁', he₂', Or.inl ⟨hbounded.symm, hout.symm⟩⟩⟩
      rw [← hbounded, ← hout]
      simp [horizontalDualEndpoints, hbottom', hrow0']
  exact hadj.reachable

/-- A vertical U-U edge on the left or right boundary transports to a
successor dual edge whenever the insertion does not split its primal edge. -/
theorem residueTwoAffineStep_vertical_boundary_reachable
    (k : Nat) (hk : 5 ≤ k)
    (e : VerticalGridEdge (3 * k + 2) (3 * k + 2))
    (hboundary : e.col.val = 0 ∨ e.col.val + 1 = 3 * k + 2)
    (hprimalSeam : e.row.val + 1 ≠ 3 * k - 6)
    (he₁ : (verticalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (verticalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (verticalDualEndpoints e).1)
      (residueTwoAffineStepFace k (verticalDualEndpoints e).2) := by
  let e' : VerticalGridEdge (3 * (k + 1) + 2) (3 * (k + 1) + 2) :=
    ⟨⟨if 3 * k - 6 ≤ e.row.val then e.row.val + 3 else e.row.val, by
        split <;> have := e.row.isLt <;> omega⟩,
      ⟨if 3 * k - 11 ≤ e.col.val then e.col.val + 3 else e.col.val, by
        split <;> have := e.col.isLt <;> omega⟩⟩
  have he₁' : (verticalPrimalEndpoints e').1 ∈
      uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffineStepVertex_mem k hk he₁
    rw [← show residueTwoAffineStepVertex k (verticalPrimalEndpoints e).1 =
        (verticalPrimalEndpoints e').1 by rfl]
    exact hm
  have he₂' : (verticalPrimalEndpoints e').2 ∈
      uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffineStepVertex_mem k hk he₂
    rw [← show residueTwoAffineStepVertex k (verticalPrimalEndpoints e).2 =
        (verticalPrimalEndpoints e').2 by
      apply Prod.ext
      · apply Fin.ext
        change (if 3 * k - 6 ≤ e.row.val + 1 then e.row.val + 1 + 3
          else e.row.val + 1) =
          (if 3 * k - 6 ≤ e.row.val then e.row.val + 3 else e.row.val) + 1
        split_ifs <;> omega
      · rfl]
    exact hm
  have hadj : (uuDualGraph (uResidueTwoAffine (k + 1))).Adj
      (residueTwoAffineStepFace k (verticalDualEndpoints e).1)
      (residueTwoAffineStepFace k (verticalDualEndpoints e).2) := by
    rcases hboundary with hleft | hright
    · have hleft' : e'.col.val = 0 := by
        simp only [e', hleft]
        split_ifs <;> omega
      have hbounded : (verticalDualEndpoints e').2 =
          residueTwoAffineStepFace k (verticalDualEndpoints e).2 := by
        simp only [verticalDualEndpoints, dif_neg (by omega : e'.col.val + 1 ≠
          3 * (k + 1) + 2), dif_neg (by omega : e.col.val + 1 ≠ 3 * k + 2)]
        simp only [residueTwoAffineStepFace]
        apply congrArg₂ GridFace.cell <;> apply Fin.ext
        · rfl
        · simp only [e']
      have hout : (verticalDualEndpoints e').1 =
          residueTwoAffineStepFace k (verticalDualEndpoints e).1 := by
        simp [verticalDualEndpoints, residueTwoAffineStepFace, hleft, hleft']
      refine ⟨?_, Or.inr ⟨e', he₁', he₂', Or.inl ⟨hout.symm, hbounded.symm⟩⟩⟩
      rw [← hout, ← hbounded]
      simp [verticalDualEndpoints, hleft']
    · have hright' : e'.col.val + 1 = 3 * (k + 1) + 2 := by
        simp only [e']
        split_ifs <;> omega
      have hcol0' : e'.col.val ≠ 0 := by omega
      have hbounded : (verticalDualEndpoints e').1 =
          residueTwoAffineStepFace k (verticalDualEndpoints e).1 := by
        simp only [verticalDualEndpoints, dif_neg (by omega : e'.col.val ≠ 0),
          dif_neg (by omega : e.col.val ≠ 0), residueTwoAffineStepFace]
        apply congrArg₂ GridFace.cell <;> apply Fin.ext
        · rfl
        · simp only [e']
          split_ifs <;> omega
      have hout : (verticalDualEndpoints e').2 =
          residueTwoAffineStepFace k (verticalDualEndpoints e).2 := by
        simp [verticalDualEndpoints, residueTwoAffineStepFace, hright, hright']
      refine ⟨?_, Or.inr ⟨e', he₁', he₂', Or.inl ⟨hbounded.symm, hout.symm⟩⟩⟩
      rw [← hbounded, ← hout]
      simp [verticalDualEndpoints, hright', hcol0']
  exact hadj.reachable

/-- Every horizontal old edge avoiding both insertion seams transports unless
its dual cells are separated by the inserted row slab. -/
theorem residueTwoAffineStep_horizontal_nonexceptional_reachable
    (k : Nat) (hk : 5 ≤ k)
    (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2))
    (hdualSeam : e.row.val ≠ 3 * k - 6)
    (hprimalSeam : e.col.val + 1 ≠ 3 * k - 11)
    (he₁ : (horizontalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (horizontalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).1)
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).2) := by
  by_cases htop : e.row.val = 0
  · exact residueTwoAffineStep_horizontal_boundary_reachable k hk e (Or.inl htop)
      hprimalSeam he₁ he₂
  by_cases hbottom : e.row.val + 1 = 3 * k + 2
  · exact residueTwoAffineStep_horizontal_boundary_reachable k hk e (Or.inr hbottom)
      hprimalSeam he₁ he₂
  exact residueTwoAffineStep_horizontal_regular_reachable k hk e
    (Nat.pos_of_ne_zero htop) (by omega) hdualSeam hprimalSeam he₁ he₂

/-- Every vertical old edge avoiding both insertion seams transports unless
its dual cells are separated by the inserted column slab. -/
theorem residueTwoAffineStep_vertical_nonexceptional_reachable
    (k : Nat) (hk : 5 ≤ k)
    (e : VerticalGridEdge (3 * k + 2) (3 * k + 2))
    (hprimalSeam : e.row.val + 1 ≠ 3 * k - 6)
    (hdualSeam : e.col.val ≠ 3 * k - 11)
    (he₁ : (verticalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (verticalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (verticalDualEndpoints e).1)
      (residueTwoAffineStepFace k (verticalDualEndpoints e).2) := by
  by_cases hleft : e.col.val = 0
  · exact residueTwoAffineStep_vertical_boundary_reachable k hk e (Or.inl hleft)
      hprimalSeam he₁ he₂
  by_cases hright : e.col.val + 1 = 3 * k + 2
  · exact residueTwoAffineStep_vertical_boundary_reachable k hk e (Or.inr hright)
      hprimalSeam he₁ he₂
  exact residueTwoAffineStep_vertical_regular_reachable k hk e
    (Nat.pos_of_ne_zero hleft) (by omega) hprimalSeam hdualSeam he₁ he₂

/-- A horizontal U-U edge crossing only the primal column seam remains a
single successor edge under the row-step/column-keep embedding. -/
theorem residueTwoAffineStep_horizontal_primalSeam_adj
    (k : Nat) (hk : 5 ≤ k)
    (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2))
    (hprimalSeam : e.col.val + 1 = 3 * k - 11)
    (hdualSeam : e.row.val ≠ 3 * k - 6)
    (he₁ : (horizontalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (horizontalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Adj
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).1)
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).2) := by
  have hcolSeam : e.col.val + 12 = 3 * k := by omega
  let e' : HorizontalGridEdge (3 * (k + 1) + 2) (3 * (k + 1) + 2) :=
    ⟨⟨if 3 * k - 6 ≤ e.row.val then e.row.val + 3 else e.row.val, by
        split <;> have := e.row.isLt <;> omega⟩,
      ⟨e.col.val, by have := e.col.isLt; omega⟩⟩
  have he₁' : (horizontalPrimalEndpoints e').1 ∈
      uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffineStepKeepVertex_mem k hk he₁
    rw [← show residueTwoAffineStepKeepVertex k
        (horizontalPrimalEndpoints e).1 = (horizontalPrimalEndpoints e').1 by
      apply Prod.ext <;> apply Fin.ext
      · rfl
      · simp [residueTwoAffineStepKeepVertex, horizontalPrimalEndpoints, e']
        omega]
    exact hm
  have he₂' : (horizontalPrimalEndpoints e').2 ∈
      uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffineStepKeepVertex_mem k hk he₂
    rw [← show residueTwoAffineStepKeepVertex k
        (horizontalPrimalEndpoints e).2 = (horizontalPrimalEndpoints e').2 by
      apply Prod.ext <;> apply Fin.ext
      · rfl
      · simp [residueTwoAffineStepKeepVertex, horizontalPrimalEndpoints, e']
        omega]
    exact hm
  have hrowCut : 0 < 3 * k - 6 := by omega
  have htop : (horizontalDualEndpoints e').1 =
      residueTwoAffineStepFace k (horizontalDualEndpoints e).1 := by
    by_cases hrow0 : e.row.val = 0
    · have hrow0' : e'.row.val = 0 := by simp [e', hrow0, hrowCut.ne']
      simp [horizontalDualEndpoints, hrow0, hrow0', residueTwoAffineStepFace]
    · have hrow0' : e'.row.val ≠ 0 := by
        simp only [e']
        split_ifs <;> omega
      simp only [horizontalDualEndpoints, dif_neg hrow0, dif_neg hrow0',
        residueTwoAffineStepFace]
      apply congrArg₂ GridFace.cell <;> apply Fin.ext
      · simp [e']
        split_ifs <;> omega
      · simp [e']
        omega
  have hbottom : (horizontalDualEndpoints e').2 =
      residueTwoAffineStepFace k (horizontalDualEndpoints e).2 := by
    by_cases hrowLast : e.row.val + 1 = 3 * k + 2
    · have hrowLast' : e'.row.val + 1 = 3 * (k + 1) + 2 := by
        simp only [e']
        split_ifs <;> omega
      simp [horizontalDualEndpoints, hrowLast, hrowLast', residueTwoAffineStepFace]
    · have hrowLast' : e'.row.val + 1 ≠ 3 * (k + 1) + 2 := by
        simp only [e']
        split_ifs <;> omega
      simp only [horizontalDualEndpoints, dif_neg hrowLast, dif_neg hrowLast',
        residueTwoAffineStepFace]
      apply congrArg₂ GridFace.cell <;> apply Fin.ext
      · simp [e']
      · simp [e']
        omega
  refine ⟨?_, Or.inl ⟨e', he₁', he₂', Or.inl ⟨htop.symm, hbottom.symm⟩⟩⟩
  rw [← htop, ← hbottom]
  by_cases hrow0' : e'.row.val = 0
  · simp [horizontalDualEndpoints, hrow0']
  by_cases hrowLast' : e'.row.val + 1 = 3 * (k + 1) + 2
  · simp [horizontalDualEndpoints, hrow0', hrowLast']
  simp only [horizontalDualEndpoints, dif_neg hrow0', dif_neg hrowLast']
  intro h
  simp only [GridFace.cell.injEq, Fin.mk.injEq] at h
  omega

/-- A vertical U-U edge crossing only the primal row seam remains a single
successor edge under the row-keep/column-step embedding. -/
theorem residueTwoAffineStep_vertical_primalSeam_adj
    (k : Nat) (hk : 5 ≤ k)
    (e : VerticalGridEdge (3 * k + 2) (3 * k + 2))
    (hprimalSeam : e.row.val + 1 = 3 * k - 6)
    (hdualSeam : e.col.val ≠ 3 * k - 11)
    (he₁ : (verticalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (verticalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Adj
      (residueTwoAffineStepFace k (verticalDualEndpoints e).1)
      (residueTwoAffineStepFace k (verticalDualEndpoints e).2) := by
  have hrowSeam : e.row.val + 7 = 3 * k := by omega
  let e' : VerticalGridEdge (3 * (k + 1) + 2) (3 * (k + 1) + 2) :=
    ⟨⟨e.row.val, by have := e.row.isLt; omega⟩,
      ⟨if 3 * k - 11 ≤ e.col.val then e.col.val + 3 else e.col.val, by
        split <;> have := e.col.isLt <;> omega⟩⟩
  have he₁' : (verticalPrimalEndpoints e').1 ∈
      uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffineKeepStepVertex_mem k hk he₁
    rw [← show residueTwoAffineKeepStepVertex k
        (verticalPrimalEndpoints e).1 = (verticalPrimalEndpoints e').1 by
      apply Prod.ext <;> apply Fin.ext
      · simp [residueTwoAffineKeepStepVertex, verticalPrimalEndpoints, e']
        omega
      · rfl]
    exact hm
  have he₂' : (verticalPrimalEndpoints e').2 ∈
      uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffineKeepStepVertex_mem k hk he₂
    rw [← show residueTwoAffineKeepStepVertex k
        (verticalPrimalEndpoints e).2 = (verticalPrimalEndpoints e').2 by
      apply Prod.ext <;> apply Fin.ext
      · simp [residueTwoAffineKeepStepVertex, verticalPrimalEndpoints, e']
        omega
      · rfl]
    exact hm
  have hcolCut : 0 < 3 * k - 11 := by omega
  have hleft : (verticalDualEndpoints e').1 =
      residueTwoAffineStepFace k (verticalDualEndpoints e).1 := by
    by_cases hcol0 : e.col.val = 0
    · have hcol0' : e'.col.val = 0 := by simp [e', hcol0, hcolCut.ne']
      simp [verticalDualEndpoints, hcol0, hcol0', residueTwoAffineStepFace]
    · have hcol0' : e'.col.val ≠ 0 := by
        simp only [e']
        split_ifs <;> omega
      simp only [verticalDualEndpoints, dif_neg hcol0, dif_neg hcol0',
        residueTwoAffineStepFace]
      apply congrArg₂ GridFace.cell <;> apply Fin.ext
      · simp [e']
        omega
      · simp [e']
        split_ifs <;> omega
  have hright : (verticalDualEndpoints e').2 =
      residueTwoAffineStepFace k (verticalDualEndpoints e).2 := by
    by_cases hcolLast : e.col.val + 1 = 3 * k + 2
    · have hcolLast' : e'.col.val + 1 = 3 * (k + 1) + 2 := by
        simp only [e']
        split_ifs <;> omega
      simp [verticalDualEndpoints, hcolLast, hcolLast', residueTwoAffineStepFace]
    · have hcolLast' : e'.col.val + 1 ≠ 3 * (k + 1) + 2 := by
        simp only [e']
        split_ifs <;> omega
      simp only [verticalDualEndpoints, dif_neg hcolLast, dif_neg hcolLast',
        residueTwoAffineStepFace]
      apply congrArg₂ GridFace.cell <;> apply Fin.ext
      · simp [e']
        omega
      · simp [e']
  refine ⟨?_, Or.inr ⟨e', he₁', he₂', Or.inl ⟨hleft.symm, hright.symm⟩⟩⟩
  rw [← hleft, ← hright]
  by_cases hcol0' : e'.col.val = 0
  · simp [verticalDualEndpoints, hcol0']
  by_cases hcolLast' : e'.col.val + 1 = 3 * (k + 1) + 2
  · simp [verticalDualEndpoints, hcol0', hcolLast']
  simp only [verticalDualEndpoints, dif_neg hcol0', dif_neg hcolLast']
  intro h
  simp only [GridFace.cell.injEq, Fin.mk.injEq] at h
  omega

/-- Every horizontal old edge away from the horizontal dual row seam
transports to a successor dual path. -/
theorem residueTwoAffineStep_horizontal_away_dualSeam_reachable
    (k : Nat) (hk : 5 ≤ k)
    (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2))
    (hdualSeam : e.row.val ≠ 3 * k - 6)
    (he₁ : (horizontalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (horizontalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).1)
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).2) := by
  by_cases hprimalSeam : e.col.val + 1 = 3 * k - 11
  · exact (residueTwoAffineStep_horizontal_primalSeam_adj k hk e
      hprimalSeam hdualSeam he₁ he₂).reachable
  · exact residueTwoAffineStep_horizontal_nonexceptional_reachable k hk e
      hdualSeam hprimalSeam he₁ he₂

/-- The possible horizontal U-U runs in the final old copy of base row 9.
This is a symbolic occurrence calculation; no generated affine board is
evaluated. -/
private theorem residueTwoAffine_rowSeam_run
    (k : Nat) (hk : 5 ≤ k)
    (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2))
    (hrow : e.row.val = 3 * k - 6)
    (he₁ : (horizontalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (horizontalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    e.col.val = 1 ∨
      (∃ i, i < k - 4 ∧ e.col.val = 4 + 3 * i) ∨
      e.col.val = 7 + 3 * (k - 5) ∨ e.col.val = 8 + 3 * (k - 5) ∨
      e.col.val = 9 + 3 * (k - 5) ∨ e.col.val = 14 + 3 * (k - 5) := by
  classical
  simp only [uResidueTwoAffine, dif_pos hk, Finset.mem_image,
    residueTwoAffineOccurrences, Finset.mem_univ, true_and] at he₁ he₂
  obtain ⟨⟨r₁, c₁, x₁⟩, hx₁⟩ := he₁
  obtain ⟨⟨r₂, c₂, x₂⟩, hx₂⟩ := he₂
  have hr₁ := congrArg (fun v => v.1.val) hx₁
  have hr₂ := congrArg (fun v => v.1.val) hx₂
  have hc₁ := congrArg (fun v => v.2.val) hx₁
  have hc₂ := congrArg (fun v => v.2.val) hx₂
  have hir₁ := x₁.val.1.isLt
  have hir₂ := x₂.val.1.isLt
  have hic₁ := x₁.val.2.isLt
  have hic₂ := x₂.val.2.isLt
  have hr₁lt := r₁.isLt
  have hr₂lt := r₂.isLt
  have hc₁lt := c₁.isLt
  have hc₂lt := c₂.isLt
  have hb₁ := x₁.property
  have hb₂ := x₂.property
  have hk5 : k - 5 + 5 = k := by omega
  have hkm4 : k - 4 = k - 5 + 1 := by omega
  have hrowExpanded : 3 * k - 6 = 9 + 3 * (k - 5) := by omega
  simp only [horizontalPrimalEndpoints] at hr₁ hr₂ hc₁ hc₂
  rw [hrow] at hr₁ hr₂
  rw [hrowExpanded] at hr₁ hr₂
  have hr₁val : r₁.val = 9 := by
    change (residueTwoExpandIndex 9 (k - 5) (by omega)
      ⟨r₁, x₁.val.1⟩).val = 9 + 3 * (k - 5) at hr₁
    by_cases hp : 9 ≤ r₁.val ∧ r₁.val < 12
    · rw [residueTwoExpandIndex_of_pump _ _ _ _ hp] at hr₁
      dsimp only at hr₁
      simp [residueTwoPumpMultiplicity, hp] at hir₁
      have hcases : r₁.val = 9 ∨ r₁.val = 10 ∨ r₁.val = 11 := by omega
      rcases hcases with hcases | hcases | hcases <;> omega
    · by_cases ha : 12 ≤ r₁.val
      · rw [residueTwoExpandIndex_of_above _ _ _ _ hp ha] at hr₁
        dsimp only at hr₁
        omega
      · rw [residueTwoExpandIndex_of_below _ _ _ _ hp ha] at hr₁
        dsimp only at hr₁
        omega
  have hr₂val : r₂.val = 9 := by
    change (residueTwoExpandIndex 9 (k - 5) (by omega)
      ⟨r₂, x₂.val.1⟩).val = 9 + 3 * (k - 5) at hr₂
    by_cases hp : 9 ≤ r₂.val ∧ r₂.val < 12
    · rw [residueTwoExpandIndex_of_pump _ _ _ _ hp] at hr₂
      dsimp only at hr₂
      simp [residueTwoPumpMultiplicity, hp] at hir₂
      have hcases : r₂.val = 9 ∨ r₂.val = 10 ∨ r₂.val = 11 := by omega
      rcases hcases with hcases | hcases | hcases <;> omega
    · by_cases ha : 12 ≤ r₂.val
      · rw [residueTwoExpandIndex_of_above _ _ _ _ hp ha] at hr₂
        dsimp only at hr₂
        omega
      · rw [residueTwoExpandIndex_of_below _ _ _ _ hp ha] at hr₂
        dsimp only at hr₂
        omega
  simp [IsResidueTwoAffineBase, residueTwoAffineBaseRow, hr₁val, hr₂val] at hb₁ hb₂
  change (residueTwoExpandIndex 4 (k - 5) (by omega)
    ⟨c₁, x₁.val.2⟩).val = e.col.val at hc₁
  change (residueTwoExpandIndex 4 (k - 5) (by omega)
    ⟨c₂, x₂.val.2⟩).val = e.col.val + 1 at hc₂
  have hc₁form :
      (4 ≤ c₁.val ∧ c₁.val < 7 ∧
        c₁.val + 3 * x₁.val.2.val = e.col.val ∧ x₁.val.2.val < k - 4) ∨
      (7 ≤ c₁.val ∧ c₁.val + 3 * (k - 5) = e.col.val) ∨
      (c₁.val < 4 ∧ c₁.val = e.col.val) := by
    by_cases hp : 4 ≤ c₁.val ∧ c₁.val < 7
    · rw [residueTwoExpandIndex_of_pump _ _ _ _ hp] at hc₁
      simp [residueTwoPumpMultiplicity, hp] at hic₁
      exact Or.inl ⟨hp.1, hp.2, hc₁, by omega⟩
    · by_cases ha : 7 ≤ c₁.val
      · rw [residueTwoExpandIndex_of_above _ _ _ _ hp ha] at hc₁
        exact Or.inr (Or.inl ⟨ha, hc₁⟩)
      · rw [residueTwoExpandIndex_of_below _ _ _ _ hp ha] at hc₁
        exact Or.inr (Or.inr ⟨by omega, hc₁⟩)
  have hc₂form :
      (4 ≤ c₂.val ∧ c₂.val < 7 ∧
        c₂.val + 3 * x₂.val.2.val = e.col.val + 1 ∧ x₂.val.2.val < k - 4) ∨
      (7 ≤ c₂.val ∧ c₂.val + 3 * (k - 5) = e.col.val + 1) ∨
      (c₂.val < 4 ∧ c₂.val = e.col.val + 1) := by
    by_cases hp : 4 ≤ c₂.val ∧ c₂.val < 7
    · rw [residueTwoExpandIndex_of_pump _ _ _ _ hp] at hc₂
      simp [residueTwoPumpMultiplicity, hp] at hic₂
      exact Or.inl ⟨hp.1, hp.2, hc₂, by omega⟩
    · by_cases ha : 7 ≤ c₂.val
      · rw [residueTwoExpandIndex_of_above _ _ _ _ hp ha] at hc₂
        exact Or.inr (Or.inl ⟨ha, hc₂⟩)
      · rw [residueTwoExpandIndex_of_below _ _ _ _ hp ha] at hc₂
        exact Or.inr (Or.inr ⟨by omega, hc₂⟩)
  clear hx₁ hx₂ hr₁ hr₂ hc₁ hc₂ hir₁ hir₂ hic₁ hic₂ hr₁lt hr₂lt
    hc₁lt hc₂lt hrowExpanded hr₁val hr₂val hrow
  rcases hc₁form with hc₁form | hc₁form | hc₁form <;>
    rcases hc₂form with hc₂form | hc₂form | hc₂form <;>
    rcases hb₁ with hb₁ | hb₁ | hb₁ | hb₁ | hb₁ | hb₁ | hb₁ | hb₁ | hb₁ | hb₁ | hb₁ <;>
    simp only [hkm4] at * <;>
    first
    | (refine Or.inr (Or.inl ⟨x₁.val.2.val, ?_, ?_⟩) <;> omega)
    | omega

/-- A fixed base occurrence gives the corresponding explicitly indexed
successor vertex.  Fixed finite row membership is discharged propositionally
at call sites. -/
private theorem residueTwoAffine_successor_expanded_mem
    (k : Nat) (hk : 5 ≤ k) (r c : Fin 17)
    (ir : Fin (residueTwoPumpMultiplicity 9 ((k + 1) - 5) r))
    (ic : Fin (residueTwoPumpMultiplicity 4 ((k + 1) - 5) c))
    (hbase : IsResidueTwoAffineBase r c) :
    let row := residueTwoExpandIndex 9 ((k + 1) - 5) (by omega)
      (⟨r, ir⟩ : ResidueTwoAffineIndex 9 ((k + 1) - 5))
    let col := residueTwoExpandIndex 4 ((k + 1) - 5) (by omega)
      (⟨c, ic⟩ : ResidueTwoAffineIndex 4 ((k + 1) - 5))
    ((⟨row.val, by have := row.isLt; omega⟩,
      ⟨col.val, by have := col.isLt; omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
      uResidueTwoAffine (k + 1) :=
  residueTwoAffine_expanded_mem (k + 1) (by omega) r c ir ic hbase

private theorem residueTwoAffine_successor_repeated_right_mem
    (k : Nat) (hk : 5 ≤ k) (r c j : Nat)
    (hr : 9 ≤ r ∧ r < 12) (hc : 7 ≤ c) (hclt : c < 17)
    (hj : j < k - 3)
    (hbase : c ∈ residueTwoAffineBaseRow r) :
    ((⟨r + 3 * j, by omega⟩, ⟨c + 3 * (k - 4), by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
  have hk4 : k - 4 + 4 = k := by omega
  have hk3 : k - 3 + 3 = k := by omega
  have ht : (k + 1) - 5 = k - 4 := by omega
  have hn : ¬(4 ≤ c ∧ c < 7) := by omega
  have hm := residueTwoAffine_successor_expanded_mem k hk
    ⟨r, by omega⟩ ⟨c, by omega⟩
    ⟨j, by simp [residueTwoPumpMultiplicity, hr]; omega⟩
    ⟨0, by simp [residueTwoPumpMultiplicity, hn]⟩
    (by simpa [IsResidueTwoAffineBase] using hbase)
  convert hm using 1
  apply Prod.ext <;> apply Fin.ext <;>
    simp [residueTwoExpandIndex, hr, hc, hn]

private theorem residueTwoAffine_successor_repeated_below_mem
    (k : Nat) (hk : 5 ≤ k) (r c j : Nat)
    (hr : 9 ≤ r ∧ r < 12) (hc : c < 4) (hj : j < k - 3)
    (hbase : c ∈ residueTwoAffineBaseRow r) :
    ((⟨r + 3 * j, by omega⟩, ⟨c, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
  have hn : ¬(4 ≤ c ∧ c < 7) := by omega
  have hn7 : ¬7 ≤ c := by omega
  have hm := residueTwoAffine_successor_expanded_mem k hk
    ⟨r, by omega⟩ ⟨c, by omega⟩
    ⟨j, by simp [residueTwoPumpMultiplicity, hr]; omega⟩
    ⟨0, by simp [residueTwoPumpMultiplicity, hn]⟩
    (by simpa [IsResidueTwoAffineBase] using hbase)
  convert hm using 1
  apply Prod.ext <;> apply Fin.ext <;>
    simp [residueTwoExpandIndex, hr, hn, hn7]

private theorem residueTwoAffine_successor_repeated_pump_mem
    (k : Nat) (hk : 5 ≤ k) (r c jr jc : Nat)
    (hr : 9 ≤ r ∧ r < 12) (hc : 4 ≤ c ∧ c < 7)
    (hjr : jr < k - 3) (hjc : jc < k - 3)
    (hbase : c ∈ residueTwoAffineBaseRow r) :
    ((⟨r + 3 * jr, by omega⟩, ⟨c + 3 * jc, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
  have hm := residueTwoAffine_successor_expanded_mem k hk
    ⟨r, by omega⟩ ⟨c, by omega⟩
    ⟨jr, by simp [residueTwoPumpMultiplicity, hr]; omega⟩
    ⟨jc, by simp [residueTwoPumpMultiplicity, hc]; omega⟩
    (by simpa [IsResidueTwoAffineBase] using hbase)
  convert hm using 1
  apply Prod.ext <;> apply Fin.ext <;>
    simp [residueTwoExpandIndex, hr, hc]

/-- The ordinary seam replacement: cross the inserted copies of rows 9, 10,
11 and then the shifted final copy of row 9. -/
private theorem residueTwoAffine_rowSeam_straight
    (k : Nat) (hk : 5 ≤ k)
    (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2))
    (hrow : e.row.val = 3 * k - 6)
    (hprimalSeam : e.col.val + 1 ≠ 3 * k - 11)
    (he₁ : (horizontalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (horizontalPrimalEndpoints e).2 ∈ uResidueTwoAffine k)
    (hm10₁ : ((⟨3 * k - 5, by omega⟩,
      ⟨if 3 * k - 11 ≤ e.col.val then e.col.val + 3 else e.col.val,
        by split <;> have := e.col.isLt <;> omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1))
    (hm10₂ : ((⟨3 * k - 5, by omega⟩,
      ⟨if 3 * k - 11 ≤ e.col.val then e.col.val + 4 else e.col.val + 1,
        by split <;> have := e.col.isLt <;> omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1))
    (hm11₁ : ((⟨3 * k - 4, by omega⟩,
      ⟨if 3 * k - 11 ≤ e.col.val then e.col.val + 3 else e.col.val,
        by split <;> have := e.col.isLt <;> omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1))
    (hm11₂ : ((⟨3 * k - 4, by omega⟩,
      ⟨if 3 * k - 11 ≤ e.col.val then e.col.val + 4 else e.col.val + 1,
        by split <;> have := e.col.isLt <;> omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1)) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).1)
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).2) := by
  let d := if 3 * k ≤ e.col.val + 11 then e.col.val + 3 else e.col.val
  have hrowCut : 3 * k - 3 = (3 * k - 6) + 3 := by omega
  have htop₁ := residueTwoAffineKeepStepVertex_mem k hk he₁
  have htop₂ := residueTwoAffineKeepStepVertex_mem k hk he₂
  have hbottom₁ := residueTwoAffineStepVertex_mem k hk he₁
  have hbottom₂ := residueTwoAffineStepVertex_mem k hk he₂
  have h0 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 6) d (by omega) (by omega) (by
      dsimp [d]; split <;> have := e.col.isLt <;> omega) (by
      convert htop₁ using 1
      apply Prod.ext <;> apply Fin.ext <;>
        simp [residueTwoAffineKeepStepVertex, horizontalPrimalEndpoints, d, hrow,
          hrowCut]) (by
      convert htop₂ using 1
      apply Prod.ext <;> apply Fin.ext <;>
        simp [residueTwoAffineKeepStepVertex, horizontalPrimalEndpoints, d, hrow,
          hrowCut]
      split_ifs <;> omega)
  have h1 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 5) d (by omega) (by omega) (by
      dsimp [d]; split <;> have := e.col.isLt <;> omega) (by
      simpa [d] using hm10₁) (by
      convert hm10₂ using 1
      apply Prod.ext <;> apply Fin.ext <;> simp [d]
      split_ifs <;> omega)
  have h2 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 4) d (by omega) (by omega) (by
      dsimp [d]; split <;> have := e.col.isLt <;> omega) (by
      simpa [d] using hm11₁) (by
      convert hm11₂ using 1
      apply Prod.ext <;> apply Fin.ext <;> simp [d]
      split_ifs <;> omega)
  have h3 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 3) d (by omega) (by omega) (by
      dsimp [d]; split <;> have := e.col.isLt <;> omega) (by
      convert hbottom₁ using 1
      apply Prod.ext <;> apply Fin.ext <;>
        simp [residueTwoAffineStepVertex, horizontalPrimalEndpoints, d, hrow,
          hrowCut]) (by
      convert hbottom₂ using 1
      apply Prod.ext <;> apply Fin.ext <;>
        simp [residueTwoAffineStepVertex, horizontalPrimalEndpoints, d, hrow,
          hrowCut]
      split_ifs <;> omega)
  have hp := h0.reachable.trans (h1.reachable.trans (h2.reachable.trans h3.reachable))
  have hrow0 : e.row.val ≠ 0 := by omega
  have hrowLast : e.row.val + 1 ≠ 3 * k + 2 := by omega
  have hrow0' : 3 * k - 6 ≠ 0 := by omega
  have hrowLast' : 3 * k - 6 + 1 ≠ 3 * k + 2 := by omega
  have hd : (if 3 * k - 11 ≤ e.col.val then e.col.val + 3 else e.col.val) = d := by
    dsimp [d]
    split_ifs <;> omega
  have hs : residueTwoAffineStepFace k (horizontalDualEndpoints e).1 =
      .cell ⟨3 * k - 6 - 1, by omega⟩ ⟨d, by
        dsimp [d]; split_ifs <;> have := e.col.isLt <;> omega⟩ := by
    simp only [horizontalDualEndpoints, dif_neg hrow0, residueTwoAffineStepFace]
    simp only [hd]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext
    · simp [hrow]
      omega
    · rfl
  have ht : residueTwoAffineStepFace k (horizontalDualEndpoints e).2 =
      .cell ⟨3 * k - 3, by omega⟩ ⟨d, by
        dsimp [d]; split_ifs <;> have := e.col.isLt <;> omega⟩ := by
    simp only [horizontalDualEndpoints, dif_neg hrowLast, residueTwoAffineStepFace]
    simp only [hd]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext
    · simp [hrow, hrowCut]
    · rfl
  rw [hs, ht]
  exact hp

/-- The run ending at expanded base columns 8 and 9 crosses the inserted rows
one dual cell to the left, where rows 10 and 11 both contain the run 7--8. -/
private theorem residueTwoAffine_rowSeam_detour_left
    (k : Nat) (hk : 5 ≤ k)
    (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2))
    (hrow : e.row.val = 3 * k - 6)
    (hcol : e.col.val = 8 + 3 * (k - 5)) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).1)
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).2) := by
  have hkm5 : k - 5 + 5 = k := by omega
  have m98 : ((⟨3 * k - 6, by omega⟩, ⟨3 * k - 4, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffine_successor_repeated_right_mem k hk 9 8 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;> (dsimp only; omega)
  have m99 : ((⟨3 * k - 6, by omega⟩, ⟨3 * k - 3, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffine_successor_repeated_right_mem k hk 9 9 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;> (dsimp only; omega)
  have m107 : ((⟨3 * k - 5, by omega⟩, ⟨3 * k - 5, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffine_successor_repeated_right_mem k hk 10 7 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;> (dsimp only; omega)
  have m108 : ((⟨3 * k - 5, by omega⟩, ⟨3 * k - 4, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffine_successor_repeated_right_mem k hk 10 8 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;> (dsimp only; omega)
  have m117 : ((⟨3 * k - 4, by omega⟩, ⟨3 * k - 5, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffine_successor_repeated_right_mem k hk 11 7 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;> (dsimp only; omega)
  have m118 : ((⟨3 * k - 4, by omega⟩, ⟨3 * k - 4, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffine_successor_repeated_right_mem k hk 11 8 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;> (dsimp only; omega)
  have m98' : ((⟨3 * k - 3, by omega⟩, ⟨3 * k - 4, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffine_successor_repeated_right_mem k hk 9 8 (k - 4)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;> (dsimp only; omega)
  have m99' : ((⟨3 * k - 3, by omega⟩, ⟨3 * k - 3, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffine_successor_repeated_right_mem k hk 9 9 (k - 4)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;> (dsimp only; omega)
  have h0 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 6) (3 * k - 4) (by omega) (by omega) (by omega) m98
    (by simpa only [show 3 * k - 4 + 1 = 3 * k - 3 by omega] using m99)
  have hv0 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 6) (3 * k - 4) (by omega) (by omega) (by omega) m98
    (by simpa only [show 3 * k - 6 + 1 = 3 * k - 5 by omega] using m108)
  have h1 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 5) (3 * k - 5) (by omega) (by omega) (by omega) m107
    (by simpa only [show 3 * k - 5 + 1 = 3 * k - 4 by omega] using m108)
  have h2 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 4) (3 * k - 5) (by omega) (by omega) (by omega) m117
    (by simpa only [show 3 * k - 5 + 1 = 3 * k - 4 by omega] using m118)
  have hv1 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 4) (3 * k - 4) (by omega) (by omega) (by omega) m118
    (by simpa only [show 3 * k - 4 + 1 = 3 * k - 3 by omega] using m98')
  have h3 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 3) (3 * k - 4) (by omega) (by omega) (by omega) m98'
    (by simpa only [show 3 * k - 4 + 1 = 3 * k - 3 by omega] using m99')
  have hp := h0.reachable.trans (hv0.reachable.symm.trans
    (h1.reachable.trans (h2.reachable.trans (hv1.reachable.trans h3.reachable))))
  have hs : residueTwoAffineStepFace k (horizontalDualEndpoints e).1 =
      .cell ⟨3 * k - 7, by omega⟩ ⟨3 * k - 4, by omega⟩ := by
    simp only [horizontalDualEndpoints, dif_neg (by omega : e.row.val ≠ 0),
      residueTwoAffineStepFace]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
      simp [hrow, hcol] <;> (try split_ifs) <;> omega
  have ht : residueTwoAffineStepFace k (horizontalDualEndpoints e).2 =
      .cell ⟨3 * k - 3, by omega⟩ ⟨3 * k - 4, by omega⟩ := by
    simp only [horizontalDualEndpoints,
      dif_neg (by omega : e.row.val + 1 ≠ 3 * k + 2), residueTwoAffineStepFace]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
      simp [hrow, hcol] <;> (try split_ifs) <;> omega
  rw [hs, ht]
  exact hp

/-- The run ending at expanded base columns 9 and 10 crosses the inserted rows
one dual cell to the right, where rows 10 and 11 both contain the run 10--11. -/
private theorem residueTwoAffine_rowSeam_detour_right
    (k : Nat) (hk : 5 ≤ k)
    (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2))
    (hrow : e.row.val = 3 * k - 6)
    (hcol : e.col.val = 9 + 3 * (k - 5)) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).1)
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).2) := by
  have hkm5 : k - 5 + 5 = k := by omega
  have hr9 : 9 + 3 * (k - 5) = 3 * k - 6 := by omega
  have hr10 : 10 + 3 * (k - 5) = 3 * k - 5 := by omega
  have hr11 : 11 + 3 * (k - 5) = 3 * k - 4 := by omega
  have hr9' : 9 + 3 * (k - 4) = 3 * k - 3 := by omega
  have hc9 : 9 + 3 * (k - 4) = 3 * k - 3 := by omega
  have hc10 : 10 + 3 * (k - 4) = 3 * k - 2 := by omega
  have hc11 : 11 + 3 * (k - 4) = 3 * k - 1 := by omega
  have mem (r c j : Nat) (hr : 9 ≤ r ∧ r < 12) (hc : 7 ≤ c)
      (hclt : c < 17) (hj : j < k - 3)
      (hbase : c ∈ residueTwoAffineBaseRow r) :
      ((⟨r + 3 * j, by omega⟩, ⟨c + 3 * (k - 4), by omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1) :=
    residueTwoAffine_successor_repeated_right_mem k hk r c j hr hc
      hclt hj hbase
  have m99 := mem 9 9 (k - 5) (by omega) (by omega) (by omega) (by omega)
    (by simp [residueTwoAffineBaseRow])
  have m910 := mem 9 10 (k - 5) (by omega) (by omega) (by omega) (by omega)
    (by simp [residueTwoAffineBaseRow])
  have m1010 := mem 10 10 (k - 5) (by omega) (by omega) (by omega) (by omega)
    (by simp [residueTwoAffineBaseRow])
  have m1011 := mem 10 11 (k - 5) (by omega) (by omega) (by omega) (by omega)
    (by simp [residueTwoAffineBaseRow])
  have m1110 := mem 11 10 (k - 5) (by omega) (by omega) (by omega) (by omega)
    (by simp [residueTwoAffineBaseRow])
  have m1111 := mem 11 11 (k - 5) (by omega) (by omega) (by omega) (by omega)
    (by simp [residueTwoAffineBaseRow])
  have m99' := mem 9 9 (k - 4) (by omega) (by omega) (by omega) (by omega)
    (by simp [residueTwoAffineBaseRow])
  have m910' := mem 9 10 (k - 4) (by omega) (by omega) (by omega) (by omega)
    (by simp [residueTwoAffineBaseRow])
  have p99 : ((⟨3 * k - 6, by omega⟩, ⟨3 * k - 3, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    simpa only [hr9, hc9] using m99
  have p910 : ((⟨3 * k - 6, by omega⟩, ⟨3 * k - 2, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    simpa only [hr9, hc10] using m910
  have p1010 : ((⟨3 * k - 5, by omega⟩, ⟨3 * k - 2, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    simpa only [hr10, hc10] using m1010
  have p1011 : ((⟨3 * k - 5, by omega⟩, ⟨3 * k - 1, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    simpa only [hr10, hc11] using m1011
  have p1110 : ((⟨3 * k - 4, by omega⟩, ⟨3 * k - 2, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    simpa only [hr11, hc10] using m1110
  have p1111 : ((⟨3 * k - 4, by omega⟩, ⟨3 * k - 1, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    simpa only [hr11, hc11] using m1111
  have p99' : ((⟨3 * k - 3, by omega⟩, ⟨3 * k - 3, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    simpa only [hr9', hc9] using m99'
  have p910' : ((⟨3 * k - 3, by omega⟩, ⟨3 * k - 2, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    simpa only [hr9', hc10] using m910'
  have h0 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 6) (3 * k - 3) (by omega) (by omega) (by omega)
    p99 (by simpa only [show 3 * k - 3 + 1 = 3 * k - 2 by omega] using p910)
  have hv0 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 6) (3 * k - 2) (by omega) (by omega) (by omega)
    p910 (by simpa only [show 3 * k - 6 + 1 = 3 * k - 5 by omega] using p1010)
  have h1 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 5) (3 * k - 2) (by omega) (by omega) (by omega)
    p1010 (by simpa only [show 3 * k - 2 + 1 = 3 * k - 1 by omega] using p1011)
  have h2 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 4) (3 * k - 2) (by omega) (by omega) (by omega)
    p1110 (by simpa only [show 3 * k - 2 + 1 = 3 * k - 1 by omega] using p1111)
  have hv1 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 4) (3 * k - 2) (by omega) (by omega) (by omega)
    p1110 (by simpa only [show 3 * k - 4 + 1 = 3 * k - 3 by omega] using p910')
  have h3 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
    (3 * k - 3) (3 * k - 3) (by omega) (by omega) (by omega)
    p99' (by simpa only [show 3 * k - 3 + 1 = 3 * k - 2 by omega] using p910')
  have hp := h0.reachable.trans (hv0.reachable.trans
    (h1.reachable.trans (h2.reachable.trans (hv1.reachable.symm.trans h3.reachable))))
  have hs : residueTwoAffineStepFace k (horizontalDualEndpoints e).1 =
      .cell ⟨3 * k - 7, by omega⟩ ⟨3 * k - 3, by omega⟩ := by
    simp only [horizontalDualEndpoints, dif_neg (by omega : e.row.val ≠ 0),
      residueTwoAffineStepFace]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
      simp [hrow, hcol] <;> (try split_ifs) <;> omega
  have ht : residueTwoAffineStepFace k (horizontalDualEndpoints e).2 =
      .cell ⟨3 * k - 3, by omega⟩ ⟨3 * k - 3, by omega⟩ := by
    simp only [horizontalDualEndpoints,
      dif_neg (by omega : e.row.val + 1 ≠ 3 * k + 2), residueTwoAffineStepFace]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
      simp [hrow, hcol] <;> (try split_ifs) <;> omega
  rw [hs, ht]
  exact hp

/-- Every horizontal U-U edge on the inserted-row seam has an explicit
successor dual path. -/
theorem residueTwoAffineStep_horizontal_rowSeam_reachable
    (k : Nat) (hk : 5 ≤ k)
    (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2))
    (hrow : e.row.val = 3 * k - 6)
    (he₁ : (horizontalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (horizontalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).1)
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).2) := by
  have hkm5 : k - 5 + 5 = k := by omega
  rcases residueTwoAffine_rowSeam_run k hk e hrow he₁ he₂ with
    hcol | ⟨i, hi, hcol⟩ | hcol | hcol | hcol | hcol
  · have m10c := residueTwoAffine_successor_repeated_below_mem k hk 10 1 (k - 5)
      (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    have m10r := residueTwoAffine_successor_repeated_below_mem k hk 10 2 (k - 5)
      (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    have m11c := residueTwoAffine_successor_repeated_below_mem k hk 11 1 (k - 5)
      (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    have m11r := residueTwoAffine_successor_repeated_below_mem k hk 11 2 (k - 5)
      (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    exact residueTwoAffine_rowSeam_straight k hk e hrow (by omega) he₁ he₂
      (by convert m10c using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol] <;> omega)
      (by convert m10r using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol] <;> omega)
      (by convert m11c using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol] <;> omega)
      (by convert m11r using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol] <;> omega)
  · let q := if i = k - 5 then i + 1 else i
    have hq : q < k - 3 := by dsimp [q]; split_ifs <;> omega
    have m10c := residueTwoAffine_successor_repeated_pump_mem k hk 10 4
      (k - 5) q (by omega) (by omega) (by omega) hq
      (by simp [residueTwoAffineBaseRow])
    have m10r := residueTwoAffine_successor_repeated_pump_mem k hk 10 5
      (k - 5) q (by omega) (by omega) (by omega) hq
      (by simp [residueTwoAffineBaseRow])
    have m11c := residueTwoAffine_successor_repeated_pump_mem k hk 11 4
      (k - 5) q (by omega) (by omega) (by omega) hq
      (by simp [residueTwoAffineBaseRow])
    have m11r := residueTwoAffine_successor_repeated_pump_mem k hk 11 5
      (k - 5) q (by omega) (by omega) (by omega) hq
      (by simp [residueTwoAffineBaseRow])
    exact residueTwoAffine_rowSeam_straight k hk e hrow (by omega) he₁ he₂
      (by convert m10c using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol, q] <;> (try split_ifs) <;> omega)
      (by convert m10r using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol, q] <;> (try split_ifs) <;> omega)
      (by convert m11c using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol, q] <;> (try split_ifs) <;> omega)
      (by convert m11r using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol, q] <;> (try split_ifs) <;> omega)
  · have m10c := residueTwoAffine_successor_repeated_right_mem k hk 10 7 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    have m10r := residueTwoAffine_successor_repeated_right_mem k hk 10 8 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    have m11c := residueTwoAffine_successor_repeated_right_mem k hk 11 7 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    have m11r := residueTwoAffine_successor_repeated_right_mem k hk 11 8 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    exact residueTwoAffine_rowSeam_straight k hk e hrow (by omega) he₁ he₂
      (by convert m10c using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol] <;> (try split_ifs) <;> omega)
      (by convert m10r using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol] <;> (try split_ifs) <;> omega)
      (by convert m11c using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol] <;> (try split_ifs) <;> omega)
      (by convert m11r using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol] <;> (try split_ifs) <;> omega)
  · exact residueTwoAffine_rowSeam_detour_left k hk e hrow hcol
  · exact residueTwoAffine_rowSeam_detour_right k hk e hrow hcol
  · have m10c := residueTwoAffine_successor_repeated_right_mem k hk 10 14 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    have m10r := residueTwoAffine_successor_repeated_right_mem k hk 10 15 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    have m11c := residueTwoAffine_successor_repeated_right_mem k hk 11 14 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    have m11r := residueTwoAffine_successor_repeated_right_mem k hk 11 15 (k - 5)
      (by omega) (by omega) (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    exact residueTwoAffine_rowSeam_straight k hk e hrow (by omega) he₁ he₂
      (by convert m10c using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol] <;> (try split_ifs) <;> omega)
      (by convert m10r using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol] <;> (try split_ifs) <;> omega)
      (by convert m11c using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol] <;> (try split_ifs) <;> omega)
      (by convert m11r using 1; apply Prod.ext <;> apply Fin.ext <;>
        simp [hcol] <;> (try split_ifs) <;> omega)

/-- Every old horizontal U-U edge transports to a successor dual path. -/
theorem residueTwoAffineStep_horizontal_reachable
    (k : Nat) (hk : 5 ≤ k)
    (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2))
    (he₁ : (horizontalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (horizontalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).1)
      (residueTwoAffineStepFace k (horizontalDualEndpoints e).2) := by
  by_cases hrow : e.row.val = 3 * k - 6
  · exact residueTwoAffineStep_horizontal_rowSeam_reachable k hk e hrow he₁ he₂
  · exact residueTwoAffineStep_horizontal_away_dualSeam_reachable k hk e hrow he₁ he₂

/-- Every vertical old edge away from the vertical dual column seam transports
to a successor dual path. -/
theorem residueTwoAffineStep_vertical_away_dualSeam_reachable
    (k : Nat) (hk : 5 ≤ k)
    (e : VerticalGridEdge (3 * k + 2) (3 * k + 2))
    (hdualSeam : e.col.val ≠ 3 * k - 11)
    (he₁ : (verticalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (verticalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (verticalDualEndpoints e).1)
      (residueTwoAffineStepFace k (verticalDualEndpoints e).2) := by
  by_cases hprimalSeam : e.row.val + 1 = 3 * k - 6
  · exact (residueTwoAffineStep_vertical_primalSeam_adj k hk e
      hprimalSeam hdualSeam he₁ he₂).reachable
  · exact residueTwoAffineStep_vertical_nonexceptional_reachable k hk e
      hprimalSeam hdualSeam he₁ he₂

/-- Membership on the final old copy of base column 4 can only occur on the
continuous vertical spine formed by base rows 1 through 15. -/
private theorem residueTwoAffine_colSeam_row_bounds
    (k : Nat) (hk : 5 ≤ k) (r : Fin (3 * k + 2))
    (hmem : ((r, ⟨3 * k - 11, by omega⟩) :
      GridVertex (3 * k + 2) (3 * k + 2)) ∈ uResidueTwoAffine k) :
    1 ≤ r.val ∧ r.val ≤ 3 * k := by
  classical
  simp only [uResidueTwoAffine, dif_pos hk, Finset.mem_image,
    residueTwoAffineOccurrences, Finset.mem_univ, true_and] at hmem
  obtain ⟨⟨br, bc, copies⟩, hx⟩ := hmem
  have hr := congrArg (fun v => v.1.val) hx
  have hc := congrArg (fun v => v.2.val) hx
  have hir := copies.val.1.isLt
  have hic := copies.val.2.isLt
  have hbr := br.isLt
  have hbc := bc.isLt
  have hb := copies.property
  change (residueTwoExpandIndex 4 (k - 5) (by omega)
    ⟨bc, copies.val.2⟩).val = 3 * k - 11 at hc
  have hcut : 3 * k - 11 = 4 + 3 * (k - 5) := by omega
  rw [hcut] at hc
  have hbc4 : bc.val = 4 := by
    by_cases hp : 4 ≤ bc.val ∧ bc.val < 7
    · rw [residueTwoExpandIndex_of_pump _ _ _ _ hp] at hc
      dsimp only at hc
      have hic' : copies.val.2.val < k - 5 + 1 := by
        simpa [residueTwoPumpMultiplicity, hp] using hic
      omega
    · by_cases ha : 7 ≤ bc.val
      · rw [residueTwoExpandIndex_of_above _ _ _ _ hp ha] at hc
        dsimp only at hc
        omega
      · rw [residueTwoExpandIndex_of_below _ _ _ _ hp ha] at hc
        dsimp only at hc
        omega
  have hbaseRows : 1 ≤ br.val ∧ br.val ≤ 15 := by
    simp only [IsResidueTwoAffineBase, hbc4] at hb
    by_contra h
    have hends : br.val = 0 ∨ br.val = 16 := by omega
    rcases hends with hends | hends <;> simp [residueTwoAffineBaseRow, hends] at hb
  change (residueTwoExpandIndex 9 (k - 5) (by omega)
    ⟨br, copies.val.1⟩).val = r.val at hr
  by_cases hp : 9 ≤ br.val ∧ br.val < 12
  · rw [residueTwoExpandIndex_of_pump _ _ _ _ hp] at hr
    dsimp only at hr
    have hir' : copies.val.1.val < k - 5 + 1 := by
      simpa [residueTwoPumpMultiplicity, hp] using hir
    omega
  · by_cases ha : 12 ≤ br.val
    · rw [residueTwoExpandIndex_of_above _ _ _ _ hp ha] at hr
      dsimp only at hr
      omega
    · rw [residueTwoExpandIndex_of_below _ _ _ _ hp ha] at hr
      dsimp only at hr
      omega

/-- Every successor corridor row from base row 3 through shifted base row 15
contains copied base column 4 or 5. -/
private theorem residueTwoAffine_successor_corridor_mem
    (k : Nat) (hk : 5 ≤ k) (r c j : Nat)
    (hr0 : 3 ≤ r) (hr1 : r ≤ 3 * k + 3)
    (hc : c = 4 ∨ c = 5) (hj : j = k - 5 ∨ j = k - 4) :
    ((⟨r, by omega⟩, ⟨c + 3 * j, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
  have ht : (k + 1) - 5 = k - 4 := by omega
  have hcpump : 4 ≤ c ∧ c < 7 := by rcases hc with rfl | rfl <;> omega
  have hjlt : j < k - 3 := by rcases hj with rfl | rfl <;> omega
  by_cases hlo : r < 9
  · have hnp : ¬(9 ≤ r ∧ r < 12) := by omega
    have hna : ¬12 ≤ r := by omega
    have hm := residueTwoAffine_successor_expanded_mem k hk
      ⟨r, by omega⟩ ⟨c, by omega⟩
      ⟨0, by simp [residueTwoPumpMultiplicity, hnp]⟩
      ⟨j, by simp [residueTwoPumpMultiplicity, hcpump, ht]; omega⟩
      (by
        change c ∈ residueTwoAffineBaseRow r
        interval_cases r <;> rcases hc with rfl | rfl <;>
          simp [residueTwoAffineBaseRow])
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;>
      simp [residueTwoExpandIndex, hnp, hna, hcpump]
  · by_cases hmid : r < 3 * k
    · let q := (r - 9) / 3
      let b := 9 + (r - 9) % 3
      have hmod : (r - 9) % 3 < 3 := Nat.mod_lt _ (by omega)
      have hdecomp : r = b + 3 * q := by
        dsimp [b, q]
        have := (Nat.mod_add_div (r - 9) 3).symm
        omega
      have hq : q < k - 3 := by
        dsimp [q]
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).2
        omega
      have hb : 9 ≤ b ∧ b < 12 := by dsimp [b]; omega
      have hm := residueTwoAffine_successor_expanded_mem k hk
        ⟨b, by omega⟩ ⟨c, by omega⟩
        ⟨q, by simp [residueTwoPumpMultiplicity, hb, ht]; omega⟩
        ⟨j, by simp [residueTwoPumpMultiplicity, hcpump, ht]; omega⟩
        (by
          change c ∈ residueTwoAffineBaseRow b
          obtain ⟨hb0, hb1⟩ := hb
          interval_cases h : b <;> rcases hc with rfl | rfl <;>
            simp [residueTwoAffineBaseRow])
      convert hm using 1
      apply Prod.ext <;> apply Fin.ext <;>
        simp [residueTwoExpandIndex, hb, hcpump]
      omega
    · let b := r - 3 * (k - 4)
      have hb : 12 ≤ b ∧ b ≤ 15 := by dsimp [b]; omega
      have hnp : ¬(9 ≤ b ∧ b < 12) := by omega
      have hm := residueTwoAffine_successor_expanded_mem k hk
        ⟨b, by omega⟩ ⟨c, by omega⟩
        ⟨0, by simp [residueTwoPumpMultiplicity, hnp]⟩
        ⟨j, by simp [residueTwoPumpMultiplicity, hcpump, ht]; omega⟩
        (by
          change c ∈ residueTwoAffineBaseRow b
          obtain ⟨hb0, hb1⟩ := hb
          interval_cases h : b <;> rcases hc with rfl | rfl <;>
            simp [residueTwoAffineBaseRow])
      convert hm using 1
      apply Prod.ext <;> apply Fin.ext <;>
        simp [residueTwoExpandIndex, hb, hnp, hcpump, ht]
      omega

/-- Copied columns 4 and 5 give a vertical dual corridor from every row at
least 3 down to dual row 3. -/
private theorem residueTwoAffine_successor_corridor_reachable
    (k : Nat) (hk : 5 ≤ k) (r j : Nat)
    (hr0 : 3 ≤ r) (hr1 : r ≤ 3 * k + 3)
    (hj : j = k - 5 ∨ j = k - 4) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨r, by omega⟩ ⟨4 + 3 * j, by omega⟩)
      (.cell ⟨3, by omega⟩ ⟨4 + 3 * j, by omega⟩) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr0
  induction d with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ d ih =>
      have hm4 := residueTwoAffine_successor_corridor_mem k hk (4 + d) 4 j
        (by omega) (by omega) (Or.inl rfl) hj
      have hm5 := residueTwoAffine_successor_corridor_mem k hk (4 + d) 5 j
        (by omega) (by omega) (Or.inr rfl) hj
      have ha := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
        (4 + d) (4 + 3 * j) (by omega) (by omega) (by omega)
        (by simpa only [show 4 + 3 * j = 4 + 3 * j by rfl] using hm4)
        (by
          convert hm5 using 1
          apply Prod.ext <;> apply Fin.ext <;> dsimp only
          omega)
      have hs : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
          (.cell ⟨4 + d, by omega⟩ ⟨4 + 3 * j, by omega⟩)
          (.cell ⟨3 + d, by omega⟩ ⟨4 + 3 * j, by omega⟩) := by
        simpa only [show 4 + d - 1 = 3 + d by omega] using ha.reachable.symm
      have hi := ih (by omega) (by omega)
      simpa only [show 3 + (d + 1) = 4 + d by omega] using hs.trans hi

/-- The crossbar avoids the missing base-row-2/base-column-5 vertex by crossing
column 5 on rows 3--4 and column 6 on rows 2--3. -/
private theorem residueTwoAffine_successor_crossbar_reachable
    (k : Nat) (hk : 5 ≤ k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨3, by omega⟩ ⟨4 + 3 * (k - 5), by omega⟩)
      (.cell ⟨3, by omega⟩ ⟨4 + 3 * (k - 4), by omega⟩) := by
  have m35 := residueTwoAffine_successor_corridor_mem k hk 3 5 (k - 5)
    (by omega) (by omega) (Or.inr rfl) (Or.inl rfl)
  have m45 := residueTwoAffine_successor_corridor_mem k hk 4 5 (k - 5)
    (by omega) (by omega) (Or.inr rfl) (Or.inl rfl)
  have m34' := residueTwoAffine_successor_corridor_mem k hk 3 4 (k - 4)
    (by omega) (by omega) (Or.inl rfl) (Or.inr rfl)
  have m35' := residueTwoAffine_successor_corridor_mem k hk 3 5 (k - 4)
    (by omega) (by omega) (Or.inr rfl) (Or.inr rfl)
  have mem6 (r : Nat) (hr : r = 2 ∨ r = 3) :
      ((⟨r, by omega⟩, ⟨6 + 3 * (k - 5), by omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1) := by
    have hnp : ¬(9 ≤ r ∧ r < 12) := by omega
    have hna : ¬12 ≤ r := by omega
    have hm := residueTwoAffine_successor_expanded_mem k hk
      ⟨r, by omega⟩ ⟨6, by omega⟩
      ⟨0, by simp [residueTwoPumpMultiplicity, hnp]⟩
      ⟨k - 5, by simp [residueTwoPumpMultiplicity]; omega⟩
      (by rcases hr with rfl | rfl <;>
        simp [IsResidueTwoAffineBase, residueTwoAffineBaseRow])
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;>
      simp [residueTwoExpandIndex, hnp, hna]
  have m26 := mem6 2 (Or.inl rfl)
  have m36 := mem6 3 (Or.inr rfl)
  have m24' : ((⟨2, by omega⟩, ⟨4 + 3 * (k - 4), by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    have hm := residueTwoAffine_successor_expanded_mem k hk
      ⟨2, by omega⟩ ⟨4, by omega⟩
      ⟨0, by simp [residueTwoPumpMultiplicity]⟩
      ⟨k - 4, by simp [residueTwoPumpMultiplicity]⟩
      (by simp [IsResidueTwoAffineBase, residueTwoAffineBaseRow])
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;> simp [residueTwoExpandIndex]
  have h0 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 3
    (5 + 3 * (k - 5)) (by omega) (by omega) (by omega) m35
    m45
  have h1 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 3
    (5 + 3 * (k - 5)) (by omega) (by omega) (by omega) m35
    (by simpa only [show 5 + 3 * (k - 5) + 1 = 6 + 3 * (k - 5) by omega]
      using m36)
  have h2 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 2
    (6 + 3 * (k - 5)) (by omega) (by omega) (by omega) m26
    m36
  have h3 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 2
    (4 + 3 * (k - 4)) (by omega) (by omega) (by omega) m24'
    m34'
  have h4 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 3
    (4 + 3 * (k - 4)) (by omega) (by omega) (by omega) m34'
    (by simpa only [show 4 + 3 * (k - 4) + 1 = 5 + 3 * (k - 4) by omega]
      using m35')
  have p0 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨3, by omega⟩ ⟨4 + 3 * (k - 5), by omega⟩)
      (.cell ⟨3, by omega⟩ ⟨5 + 3 * (k - 5), by omega⟩) := by
    simpa only [show 5 + 3 * (k - 5) - 1 = 4 + 3 * (k - 5) by omega] using
      h0.reachable
  have p1 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨3, by omega⟩ ⟨5 + 3 * (k - 5), by omega⟩)
      (.cell ⟨2, by omega⟩ ⟨5 + 3 * (k - 5), by omega⟩) := by
    simpa only [show 3 - 1 = 2 by omega] using h1.reachable.symm
  have p2 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨2, by omega⟩ ⟨5 + 3 * (k - 5), by omega⟩)
      (.cell ⟨2, by omega⟩ ⟨6 + 3 * (k - 5), by omega⟩) := by
    simpa only [show 6 + 3 * (k - 5) - 1 = 5 + 3 * (k - 5) by omega] using
      h2.reachable
  have p3 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨2, by omega⟩ ⟨6 + 3 * (k - 5), by omega⟩)
      (.cell ⟨2, by omega⟩ ⟨4 + 3 * (k - 4), by omega⟩) := by
    simpa only [show 4 + 3 * (k - 4) - 1 = 6 + 3 * (k - 5) by omega] using
      h3.reachable
  have p4 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨2, by omega⟩ ⟨4 + 3 * (k - 4), by omega⟩)
      (.cell ⟨3, by omega⟩ ⟨4 + 3 * (k - 4), by omega⟩) := by
    simpa only [show 3 - 1 = 2 by omega] using h4.reachable
  exact p0.trans (p1.trans (p2.trans (p3.trans p4)))

/-- Every face in the first inserted column from row 3 down reaches the old
rectangle.  The copied columns 4 and 5 take the face to row 3, and the
crossbar takes it across the inserted column slab. -/
theorem residueTwoAffineStepFace_insertedColumnLeft_reachable
    (k : Nat) (hk : 5 ≤ k) (r : Fin (3 * (k + 1) + 1))
    (hr : 3 ≤ r.val) :
    ∃ y : GridFace (3 * k + 2) (3 * k + 2),
      (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
        (.cell r ⟨3 * k - 11, by omega⟩) (residueTwoAffineStepFace k y) := by
  have hdown := residueTwoAffine_successor_corridor_reachable k hk r.val (k - 5)
    hr (by have := r.isLt; omega) (Or.inl rfl)
  have hacross := residueTwoAffine_successor_crossbar_reachable k hk
  let targetRow : Fin (3 * (k + 1) + 1) := ⟨3, by omega⟩
  let targetCol : Fin (3 * (k + 1) + 1) := ⟨3 * k - 8, by omega⟩
  obtain ⟨y, hy⟩ := exists_residueTwoAffineStepFace_preimage k hk targetRow targetCol
    (Or.inl (by simp [targetRow]; omega)) (Or.inr (by simp [targetCol]))
  refine ⟨y, ?_⟩
  rw [hy]
  have hroute := hdown.trans hacross
  convert hroute using 1 <;> apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
    simp [targetRow, targetCol] <;> omega

/-- From row 3 down, the middle inserted face-column crosses copied column 5
into the left corridor.  On the final face row it first rises across the
all-U shifted base row 15. -/
private theorem residueTwoAffineStepFace_insertedColumnMiddle_reachable
    (k : Nat) (hk : 5 ≤ k) (r : Fin (3 * (k + 1) + 1))
    (hr : 3 ≤ r.val) :
    ∃ y : GridFace (3 * k + 2) (3 * k + 2),
      (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
        (.cell r ⟨3 * k - 10, by omega⟩) (residueTwoAffineStepFace k y) := by
  by_cases hbottom : r.val = 3 * k + 3
  · have hre : r = ⟨3 * k + 3, by omega⟩ := Fin.ext hbottom
    rw [hre]
    have m5 := residueTwoAffine_successor_corridor_mem k hk (3 * k + 3) 5 (k - 5)
      (by omega) (by omega) (Or.inr rfl) (Or.inl rfl)
    have m6 : ((⟨3 * k + 3, by omega⟩, ⟨6 + 3 * (k - 5), by omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1) := by
      have hm := residueTwoAffine_successor_expanded_mem k hk
        ⟨15, by omega⟩ ⟨6, by omega⟩
        ⟨0, by simp [residueTwoPumpMultiplicity]⟩
        ⟨k - 5, by simp [residueTwoPumpMultiplicity]; omega⟩
        (by simp [IsResidueTwoAffineBase, residueTwoAffineBaseRow])
      convert hm using 1
      apply Prod.ext <;> apply Fin.ext <;> simp [residueTwoExpandIndex]
      omega
    have hup := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
      (3 * k + 3) (5 + 3 * (k - 5)) (by omega) (by omega) (by omega) m5
      (by simpa only [show 5 + 3 * (k - 5) + 1 = 6 + 3 * (k - 5) by omega]
        using m6)
    let r' : Fin (3 * (k + 1) + 1) := ⟨3 * k + 2, by omega⟩
    obtain ⟨y, hy⟩ := residueTwoAffineStepFace_insertedColumnLeft_reachable k hk r'
      (by simp [r']; omega)
    refine ⟨y, ?_⟩
    have m5' := residueTwoAffine_successor_corridor_mem k hk (3 * k + 2) 5 (k - 5)
      (by omega) (by omega) (Or.inr rfl) (Or.inl rfl)
    have macross := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
      (3 * k + 2) (5 + 3 * (k - 5)) (by omega) (by omega) (by omega) m5'
      m5
    have hacross : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
        (.cell r' ⟨3 * k - 10, by omega⟩) (.cell r' ⟨3 * k - 11, by omega⟩) := by
      simpa only [show 5 + 3 * (k - 5) = 3 * k - 10 by omega,
        show 3 * k - 10 - 1 = 3 * k - 11 by omega] using
          macross.reachable.symm
    have huppath : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
        (.cell ⟨3 * k + 3, by omega⟩ ⟨3 * k - 10, by omega⟩)
        (.cell r' ⟨3 * k - 10, by omega⟩) := by
      simpa only [show 3 * k + 3 - 1 = 3 * k + 2 by omega,
        show 5 + 3 * (k - 5) = 3 * k - 10 by omega] using hup.reachable.symm
    have path := huppath.trans (hacross.trans hy)
    exact path
  · have m5 := residueTwoAffine_successor_corridor_mem k hk r.val 5 (k - 5)
      hr (by have := r.isLt; omega) (Or.inr rfl) (Or.inl rfl)
    have m5' := residueTwoAffine_successor_corridor_mem k hk (r.val + 1) 5 (k - 5)
      (by omega) (by have := r.isLt; omega) (Or.inr rfl) (Or.inl rfl)
    have macross := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) r.val
      (5 + 3 * (k - 5)) (by have := r.isLt; omega) (by omega) (by omega) m5
      (by simpa only [show r.val + 1 = r.val + 1 by rfl] using m5')
    obtain ⟨y, hy⟩ := residueTwoAffineStepFace_insertedColumnLeft_reachable k hk r hr
    refine ⟨y, ?_⟩
    have hacross : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
        (.cell r ⟨3 * k - 10, by omega⟩) (.cell r ⟨3 * k - 11, by omega⟩) := by
      convert macross.reachable.symm using 1 <;>
        apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> dsimp only <;> omega
    have path := hacross.trans hy
    exact path

/-- From row 3 down, the right inserted face-column crosses the next copy of
base column 4 into the regular old rectangle.  The bottom face again first
rises across shifted base row 15. -/
private theorem residueTwoAffineStepFace_insertedColumnRight_reachable
    (k : Nat) (hk : 5 ≤ k) (r : Fin (3 * (k + 1) + 1))
    (hr : 3 ≤ r.val)
    (hrslab : r.val < 3 * k - 6 ∨ 3 * k - 3 ≤ r.val) :
    ∃ y : GridFace (3 * k + 2) (3 * k + 2),
      (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
        (.cell r ⟨3 * k - 9, by omega⟩) (residueTwoAffineStepFace k y) := by
  let targetCol : Fin (3 * (k + 1) + 1) := ⟨3 * k - 8, by omega⟩
  obtain ⟨y, hy⟩ := residueTwoAffineStepFace_regular_reachable k hk r targetCol
    hrslab (Or.inr (by simp [targetCol]))
  by_cases hbottom : r.val = 3 * k + 3
  · have hre : r = ⟨3 * k + 3, by omega⟩ := Fin.ext hbottom
    rw [hre]
    let r' : Fin (3 * (k + 1) + 1) := ⟨3 * k + 2, by omega⟩
    obtain ⟨y', hy'⟩ := residueTwoAffineStepFace_regular_reachable k hk r' targetCol
      (Or.inr (by simp [r']; omega)) (Or.inr (by simp [targetCol]))
    refine ⟨y', ?_⟩
    have m6 : ((⟨3 * k + 3, by omega⟩, ⟨6 + 3 * (k - 5), by omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1) := by
      have hm := residueTwoAffine_successor_expanded_mem k hk
        ⟨15, by omega⟩ ⟨6, by omega⟩
        ⟨0, by simp [residueTwoPumpMultiplicity]⟩
        ⟨k - 5, by simp [residueTwoPumpMultiplicity]; omega⟩
        (by simp [IsResidueTwoAffineBase, residueTwoAffineBaseRow])
      convert hm using 1
      apply Prod.ext <;> apply Fin.ext <;> simp [residueTwoExpandIndex]
      omega
    have m4 := residueTwoAffine_successor_corridor_mem k hk (3 * k + 3) 4 (k - 4)
      (by omega) (by omega) (Or.inl rfl) (Or.inr rfl)
    have hup := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
      (3 * k + 3) (6 + 3 * (k - 5)) (by omega) (by omega) (by omega) m6
      (by simpa only [show 6 + 3 * (k - 5) + 1 = 4 + 3 * (k - 4) by omega]
        using m4)
    have m4' := residueTwoAffine_successor_corridor_mem k hk (3 * k + 2) 4 (k - 4)
      (by omega) (by omega) (Or.inl rfl) (Or.inr rfl)
    have macross := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1))
      (3 * k + 2) (4 + 3 * (k - 4)) (by omega) (by omega) (by omega) m4'
      m4
    have hacross : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
        (.cell ⟨3 * k + 2, by omega⟩ ⟨3 * k - 9, by omega⟩)
        (.cell ⟨3 * k + 2, by omega⟩ targetCol) := by
      simpa only [show 3 * k - 8 - 1 = 3 * k - 9 by omega,
        show 4 + 3 * (k - 4) = 3 * k - 8 by omega, targetCol] using
          macross.reachable
    have huppath : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
        (.cell ⟨3 * k + 3, by omega⟩ ⟨3 * k - 9, by omega⟩)
        (.cell ⟨3 * k + 2, by omega⟩ ⟨3 * k - 9, by omega⟩) := by
      simpa only [show 3 * k + 3 - 1 = 3 * k + 2 by omega,
        show 6 + 3 * (k - 5) = 3 * k - 9 by omega] using hup.reachable.symm
    have path := huppath.trans (hacross.trans hy')
    exact path
  · have m4 := residueTwoAffine_successor_corridor_mem k hk r.val 4 (k - 4)
      hr (by have := r.isLt; omega) (Or.inl rfl) (Or.inr rfl)
    have m4' := residueTwoAffine_successor_corridor_mem k hk (r.val + 1) 4 (k - 4)
      (by omega) (by have := r.isLt; omega) (Or.inl rfl) (Or.inr rfl)
    have macross := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) r.val
      (4 + 3 * (k - 4)) (by have := r.isLt; omega) (by omega) (by omega) m4
      (by simpa only [show r.val + 1 = r.val + 1 by rfl] using m4')
    refine ⟨y, ?_⟩
    have hacross : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
        (.cell r ⟨3 * k - 9, by omega⟩) (.cell r targetCol) := by
      convert macross.reachable using 1 <;>
        apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> dsimp [targetCol] <;> omega
    have path := hacross.trans hy
    exact path

/-- The three top face rows enter the copied-column machinery through the
explicit base-row-1, base-row-2, and base-row-3 pattern on columns 4, 5, 6. -/
private theorem residueTwoAffineStepFace_insertedColumns_top_reachable
    (k : Nat) (hk : 5 ≤ k) (r c : Fin (3 * (k + 1) + 1))
    (hr : r.val < 3)
    (hc : 3 * k - 11 ≤ c.val ∧ c.val < 3 * k - 8) :
    ∃ y : GridFace (3 * k + 2) (3 * k + 2),
      (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable (.cell r c)
        (residueTwoAffineStepFace k y) := by
  have mem (br bc j : Nat) (hbr : br = 1 ∨ br = 2 ∨ br = 3)
      (hbc : bc = 4 ∨ bc = 5 ∨ bc = 6) (hj : j = k - 5 ∨ j = k - 4)
      (hb : bc ∈ residueTwoAffineBaseRow br) :
      ((⟨br, by omega⟩, ⟨bc + 3 * j, by omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1) := by
    have hrnp : ¬(9 ≤ br ∧ br < 12) := by omega
    have hrna : ¬12 ≤ br := by omega
    have hcp : 4 ≤ bc ∧ bc < 7 := by omega
    have hjlt : j < k - 3 := by rcases hj with rfl | rfl <;> omega
    have hm := residueTwoAffine_successor_expanded_mem k hk
      ⟨br, by omega⟩ ⟨bc, by omega⟩
      ⟨0, by simp [residueTwoPumpMultiplicity, hrnp]⟩
      ⟨j, by simp [residueTwoPumpMultiplicity, hcp]; omega⟩
      (by simpa [IsResidueTwoAffineBase] using hb)
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;>
      simp [residueTwoExpandIndex, hrnp, hrna, hcp]
  have m14 := mem 1 4 (k - 5) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    (by simp [residueTwoAffineBaseRow])
  have m15 := mem 1 5 (k - 5) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inl rfl)
    (by simp [residueTwoAffineBaseRow])
  have m16 := mem 1 6 (k - 5) (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inl rfl)
    (by simp [residueTwoAffineBaseRow])
  have m14' := mem 1 4 (k - 4) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
    (by simp [residueTwoAffineBaseRow])
  have m24 := mem 2 4 (k - 5) (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inl rfl)
    (by simp [residueTwoAffineBaseRow])
  have m26 := mem 2 6 (k - 5) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
    (Or.inl rfl) (by simp [residueTwoAffineBaseRow])
  have m24' := mem 2 4 (k - 4) (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr rfl)
    (by simp [residueTwoAffineBaseRow])
  have m34 := mem 3 4 (k - 5) (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inl rfl)
    (by simp [residueTwoAffineBaseRow])
  have m35 := mem 3 5 (k - 5) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
    (Or.inl rfl) (by simp [residueTwoAffineBaseRow])
  have m36 := mem 3 6 (k - 5) (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl))
    (Or.inl rfl) (by simp [residueTwoAffineBaseRow])
  have m34' := mem 3 4 (k - 4) (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr rfl)
    (by simp [residueTwoAffineBaseRow])
  have d00 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 1
    (4 + 3 * (k - 5)) (by omega) (by omega) (by omega) m14
    (by simpa only [show 4 + 3 * (k - 5) + 1 = 5 + 3 * (k - 5) by omega] using m15)
  have d01 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 1
    (5 + 3 * (k - 5)) (by omega) (by omega) (by omega) m15
    (by simpa only [show 5 + 3 * (k - 5) + 1 = 6 + 3 * (k - 5) by omega] using m16)
  have d02 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 1
    (6 + 3 * (k - 5)) (by omega) (by omega) (by omega) m16
    (by simpa only [show 6 + 3 * (k - 5) + 1 = 4 + 3 * (k - 4) by omega] using m14')
  have left1 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 1
    (4 + 3 * (k - 5)) (by omega) (by omega) (by omega) m14
    m24
  have right1 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 1
    (6 + 3 * (k - 5)) (by omega) (by omega) (by omega) m16
    m26
  have d12 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 2
    (6 + 3 * (k - 5)) (by omega) (by omega) (by omega) m26
    (by simpa only [show 6 + 3 * (k - 5) + 1 = 4 + 3 * (k - 4) by omega] using m24')
  have d20 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 3
    (4 + 3 * (k - 5)) (by omega) (by omega) (by omega) m34
    (by simpa only [show 4 + 3 * (k - 5) + 1 = 5 + 3 * (k - 5) by omega] using m35)
  have d21 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 3
    (5 + 3 * (k - 5)) (by omega) (by omega) (by omega) m35
    (by simpa only [show 5 + 3 * (k - 5) + 1 = 6 + 3 * (k - 5) by omega] using m36)
  have d22 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 3
    (6 + 3 * (k - 5)) (by omega) (by omega) (by omega) m36
    (by simpa only [show 6 + 3 * (k - 5) + 1 = 4 + 3 * (k - 4) by omega] using m34')
  let r1 : Fin (3 * (k + 1) + 1) := ⟨1, by omega⟩
  let r3 : Fin (3 * (k + 1) + 1) := ⟨3, by omega⟩
  let cleft : Fin (3 * (k + 1) + 1) := ⟨3 * k - 12, by omega⟩
  obtain ⟨yleft, hyleft⟩ := residueTwoAffineStepFace_regular_reachable k hk r1 cleft
    (Or.inl (by simp [r1]; omega)) (Or.inl (by simp [cleft]; omega))
  obtain ⟨y0, hy0⟩ := residueTwoAffineStepFace_insertedColumnLeft_reachable k hk r3
    (by simp [r3])
  obtain ⟨y1, hy1⟩ := residueTwoAffineStepFace_insertedColumnMiddle_reachable k hk r3
    (by simp [r3])
  obtain ⟨y2, hy2⟩ := residueTwoAffineStepFace_insertedColumnRight_reachable k hk r3
    (by simp [r3]) (Or.inl (by simp [r3]; omega))
  have pleft : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell r1 ⟨3 * k - 11, by omega⟩) (.cell r1 cleft) := by
    simpa only [show 4 + 3 * (k - 5) = 3 * k - 11 by omega,
      show 3 * k - 11 - 1 = 3 * k - 12 by omega, r1, cleft] using
        left1.reachable.symm
  have p12 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell r1 ⟨3 * k - 10, by omega⟩) (.cell r1 ⟨3 * k - 9, by omega⟩) := by
    simpa only [show 3 * k - 9 - 1 = 3 * k - 10 by omega,
      show 6 + 3 * (k - 5) = 3 * k - 9 by omega, r1] using right1.reachable
  have pd00 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨0, by omega⟩ ⟨3 * k - 11, by omega⟩)
      (.cell r1 ⟨3 * k - 11, by omega⟩) := by
    simpa only [show 1 - 1 = 0 by omega,
      show 4 + 3 * (k - 5) = 3 * k - 11 by omega, r1] using d00.reachable
  have pd01 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨0, by omega⟩ ⟨3 * k - 10, by omega⟩)
      (.cell r1 ⟨3 * k - 10, by omega⟩) := by
    simpa only [show 1 - 1 = 0 by omega,
      show 5 + 3 * (k - 5) = 3 * k - 10 by omega, r1] using d01.reachable
  have pd02 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨0, by omega⟩ ⟨3 * k - 9, by omega⟩)
      (.cell r1 ⟨3 * k - 9, by omega⟩) := by
    simpa only [show 1 - 1 = 0 by omega,
      show 6 + 3 * (k - 5) = 3 * k - 9 by omega, r1] using d02.reachable
  have pd12 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell r1 ⟨3 * k - 9, by omega⟩)
      (.cell ⟨2, by omega⟩ ⟨3 * k - 9, by omega⟩) := by
    simpa only [show 2 - 1 = 1 by omega,
      show 6 + 3 * (k - 5) = 3 * k - 9 by omega, r1] using d12.reachable
  have pd20 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨2, by omega⟩ ⟨3 * k - 11, by omega⟩)
      (.cell r3 ⟨3 * k - 11, by omega⟩) := by
    simpa only [show 3 - 1 = 2 by omega,
      show 4 + 3 * (k - 5) = 3 * k - 11 by omega, r3] using d20.reachable
  have pd21 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨2, by omega⟩ ⟨3 * k - 10, by omega⟩)
      (.cell r3 ⟨3 * k - 10, by omega⟩) := by
    simpa only [show 3 - 1 = 2 by omega,
      show 5 + 3 * (k - 5) = 3 * k - 10 by omega, r3] using d21.reachable
  have pd22 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨2, by omega⟩ ⟨3 * k - 9, by omega⟩)
      (.cell r3 ⟨3 * k - 9, by omega⟩) := by
    simpa only [show 3 - 1 = 2 by omega,
      show 6 + 3 * (k - 5) = 3 * k - 9 by omega, r3] using d22.reachable
  have hrow : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
  have hcol : c.val = 3 * k - 11 ∨ c.val = 3 * k - 10 ∨ c.val = 3 * k - 9 := by omega
  rcases hrow with hrow | hrow | hrow <;> rcases hcol with hcol | hcol | hcol
  · refine ⟨yleft, ?_⟩
    have path := pd00.trans (pleft.trans hyleft)
    convert path using 1
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> simp [hrow, hcol]
  · refine ⟨y2, ?_⟩
    have path := pd01.trans (p12.trans (pd12.trans (pd22.trans hy2)))
    convert path using 1
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> simp [hrow, hcol]
  · refine ⟨y2, ?_⟩
    have path := pd02.trans (pd12.trans (pd22.trans hy2))
    convert path using 1
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> simp [hrow, hcol]
  · exact ⟨yleft, by
      have path := pleft.trans hyleft
      convert path using 1
      apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> simp [r1, hrow, hcol]⟩
  · exact ⟨y2, by
      have path := p12.trans (pd12.trans (pd22.trans hy2))
      convert path using 1
      apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> simp [r1, hrow, hcol]⟩
  · exact ⟨y2, by
      have path := pd12.trans (pd22.trans hy2)
      convert path using 1
      apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> simp [r1, hrow, hcol]⟩
  · exact ⟨y0, by
      have path := pd20.trans hy0
      convert path using 1
      apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> simp [hrow, hcol]⟩
  · exact ⟨y1, by
      have path := pd21.trans hy1
      convert path using 1
      apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> simp [hrow, hcol]⟩
  · exact ⟨y2, by
      have path := pd22.trans hy2
      convert path using 1
      apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> simp [hrow, hcol]⟩

/-- Every face in one of the three inserted columns whose row lies outside the
inserted row slab attaches to an embedded old face. -/
theorem residueTwoAffineStepFace_insertedColumns_reachable
    (k : Nat) (hk : 5 ≤ k) (r c : Fin (3 * (k + 1) + 1))
    (hr : r.val < 3 * k - 6 ∨ 3 * k - 3 ≤ r.val)
    (hc : 3 * k - 11 ≤ c.val ∧ c.val < 3 * k - 8) :
    ∃ y : GridFace (3 * k + 2) (3 * k + 2),
      (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable (.cell r c)
        (residueTwoAffineStepFace k y) := by
  by_cases htop : r.val < 3
  · exact residueTwoAffineStepFace_insertedColumns_top_reachable k hk r c htop hc
  · have hr3 : 3 ≤ r.val := by omega
    have hcol : c.val = 3 * k - 11 ∨ c.val = 3 * k - 10 ∨ c.val = 3 * k - 9 := by
      omega
    rcases hcol with hcol | hcol | hcol
    · have hceq : c = ⟨3 * k - 11, by omega⟩ := Fin.ext hcol
      rw [hceq]
      exact residueTwoAffineStepFace_insertedColumnLeft_reachable k hk r hr3
    · have hceq : c = ⟨3 * k - 10, by omega⟩ := Fin.ext hcol
      rw [hceq]
      exact residueTwoAffineStepFace_insertedColumnMiddle_reachable k hk r hr3
    · have hceq : c = ⟨3 * k - 9, by omega⟩ := Fin.ext hcol
      rw [hceq]
      exact residueTwoAffineStepFace_insertedColumnRight_reachable k hk r hr3 hr

/-- Every seam edge whose top endpoint is at least row 2 reaches the copied
crossbar through the column-4/5 corridor. -/
private theorem residueTwoAffineStep_vertical_colSeam_of_two_le
    (k : Nat) (hk : 5 ≤ k)
    (e : VerticalGridEdge (3 * k + 2) (3 * k + 2))
    (hcol : e.col.val = 3 * k - 11) (hrow2 : 2 ≤ e.row.val)
    (he₂ : (verticalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (verticalDualEndpoints e).1)
      (residueTwoAffineStepFace k (verticalDualEndpoints e).2) := by
  let R := if 3 * k - 6 ≤ e.row.val then e.row.val + 3 else e.row.val
  have hR2 : 2 ≤ R := by dsimp [R]; split_ifs <;> omega
  have hRmax : R ≤ 3 * k + 3 := by
    dsimp [R]
    split_ifs <;> have := e.row.isLt <;> omega
  let er2 : Fin (3 * k + 2) := ⟨e.row.val + 1, by have := e.row.isLt; omega⟩
  have her2 : ((er2, ⟨3 * k - 11, by omega⟩) :
      GridVertex (3 * k + 2) (3 * k + 2)) ∈ uResidueTwoAffine k := by
    convert he₂ using 1
    apply Prod.ext <;> apply Fin.ext <;>
      simp [er2, verticalPrimalEndpoints, hcol]
  have hb2 := residueTwoAffine_colSeam_row_bounds k hk er2 her2
  have hRsuccmax : R + 1 ≤ 3 * k + 3 := by
    dsimp [R, er2] at hb2 ⊢
    split_ifs <;> omega
  have mem4 (r j : Nat) (hr0 : 2 ≤ r) (hr1 : r ≤ 3 * k + 3)
      (hj : j = k - 5 ∨ j = k - 4) :
      ((⟨r, by omega⟩, ⟨4 + 3 * j, by omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1) := by
    by_cases hr : r = 2
    · subst r
      have hjlt : j < k - 3 := by rcases hj with rfl | rfl <;> omega
      have hm := residueTwoAffine_successor_expanded_mem k hk
        ⟨2, by omega⟩ ⟨4, by omega⟩
        ⟨0, by simp [residueTwoPumpMultiplicity]⟩
        ⟨j, by simp [residueTwoPumpMultiplicity]; omega⟩
        (by simp [IsResidueTwoAffineBase, residueTwoAffineBaseRow])
      convert hm using 1
      apply Prod.ext <;> apply Fin.ext <;> simp [residueTwoExpandIndex]
    · exact residueTwoAffine_successor_corridor_mem k hk r 4 j
        (by omega) hr1 (Or.inl rfl) hj
  have mc1 : ((⟨R, by omega⟩, ⟨4 + 3 * (k - 5), by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := mem4 R (k - 5) hR2 hRmax (Or.inl rfl)
  have mc2 : ((⟨R + 1, by omega⟩, ⟨4 + 3 * (k - 5), by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := mem4 (R + 1) (k - 5) (by omega)
          hRsuccmax (Or.inl rfl)
  have hs := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) R
    (4 + 3 * (k - 5)) (by omega) (by omega) (by omega) mc1
    (by simpa only [show R + 1 = R + 1 by rfl] using mc2)
  have corridor (j : Nat) (hj : j = k - 5 ∨ j = k - 4) :
      (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
        (.cell ⟨R, by omega⟩ ⟨4 + 3 * j, by omega⟩)
        (.cell ⟨3, by omega⟩ ⟨4 + 3 * j, by omega⟩) := by
    by_cases hR : R = 2
    · have m24 := residueTwoAffine_successor_corridor_mem k hk 3 4 j
        (by omega) (by omega) (Or.inl rfl) hj
      have m25 := residueTwoAffine_successor_corridor_mem k hk 3 5 j
        (by omega) (by omega) (Or.inr rfl) hj
      have ha := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 3
        (4 + 3 * j) (by omega) (by omega) (by omega) m24
        (by simpa only [show 4 + 3 * j + 1 = 5 + 3 * j by omega] using m25)
      simpa only [hR, show 3 - 1 = 2 by omega] using ha.reachable
    · exact residueTwoAffine_successor_corridor_reachable k hk R j
        (by omega) hRmax hj
  have pc := corridor (k - 5) (Or.inl rfl)
  have pf := corridor (k - 4) (Or.inr rfl)
  have path := hs.reachable.trans (pc.trans
    (residueTwoAffine_successor_crossbar_reachable k hk |>.trans
      pf.symm))
  have hsource : residueTwoAffineStepFace k (verticalDualEndpoints e).1 =
      .cell ⟨R, by omega⟩ ⟨4 + 3 * (k - 5) - 1, by omega⟩ := by
    simp only [verticalDualEndpoints, dif_neg (by omega : e.col.val ≠ 0),
      residueTwoAffineStepFace]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
      simp [R, hcol]
    split_ifs <;> omega
  have htarget : residueTwoAffineStepFace k (verticalDualEndpoints e).2 =
      .cell ⟨R, by omega⟩ ⟨4 + 3 * (k - 4), by omega⟩ := by
    simp only [verticalDualEndpoints,
      dif_neg (by omega : e.col.val + 1 ≠ 3 * k + 2), residueTwoAffineStepFace]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
      simp [R, hcol]
    omega
  rw [hsource, htarget]
  simpa only [show 4 + 3 * (k - 5) - 1 = 3 * k - 12 by omega,
    show 4 + 3 * (k - 4) = 3 * k - 8 by omega] using path

/-- At the first valid seam edge, use the preceding column-6 copy to get below
the missing row-2/column-5 vertex, then use the same crossbar zigzag. -/
private theorem residueTwoAffineStep_vertical_colSeam_row_one
    (k : Nat) (hk : 5 ≤ k)
    (e : VerticalGridEdge (3 * k + 2) (3 * k + 2))
    (hcol : e.col.val = 3 * k - 11) (hrow : e.row.val = 1) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (verticalDualEndpoints e).1)
      (residueTwoAffineStepFace k (verticalDualEndpoints e).2) := by
  have mem (r c j : Nat) (hr : r = 1 ∨ r = 2 ∨ r = 3)
      (hc : c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6) (hj : j < k - 3)
      (hc3 : c = 3 → j = 0)
      (hb : c ∈ residueTwoAffineBaseRow r) :
      ((⟨r, by omega⟩, ⟨c + 3 * j, by omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1) := by
    have hrnp : ¬(9 ≤ r ∧ r < 12) := by omega
    have hrna : ¬12 ≤ r := by omega
    have hcp : 4 ≤ c ∧ c < 7 ∨ c = 3 := by omega
    have hm := residueTwoAffine_successor_expanded_mem k hk
      ⟨r, by omega⟩ ⟨c, by omega⟩
      ⟨0, by simp [residueTwoPumpMultiplicity, hrnp]⟩
      ⟨j, by
        rcases hcp with hcp | rfl
        · simp [residueTwoPumpMultiplicity, hcp]; omega
        · simp [residueTwoPumpMultiplicity, hc3 rfl]⟩
      (by simpa [IsResidueTwoAffineBase] using hb)
    convert hm using 1
    apply Prod.ext <;> apply Fin.ext <;> simp [residueTwoExpandIndex, hrnp, hrna]
    rcases hcp with hcp | rfl <;> simp_all
  have m24 := mem 2 4 (k - 5) (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
    (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
  have m34 := mem 3 4 (k - 5) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
    (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
  have m35 := mem 3 5 (k - 5) (Or.inr (Or.inr rfl)) (Or.inr (Or.inr (Or.inl rfl)))
    (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
  have m26 := mem 2 6 (k - 5) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl)))
    (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
  have m36 := mem 3 6 (k - 5) (Or.inr (Or.inr rfl)) (Or.inr (Or.inr (Or.inr rfl)))
    (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
  have m14' := mem 1 4 (k - 4) (Or.inl rfl) (Or.inr (Or.inl rfl))
    (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
  have m24' := mem 2 4 (k - 4) (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
    (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
  have mleft : ((⟨2, by omega⟩, ⟨3 * k - 12, by omega⟩) :
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
        uResidueTwoAffine (k + 1) := by
    by_cases h5 : k = 5
    · subst k
      simpa only using mem 2 3 0 (Or.inr (Or.inl rfl)) (Or.inl rfl)
        (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
    · have hm := mem 2 6 (k - 6) (Or.inr (Or.inl rfl))
        (Or.inr (Or.inr (Or.inr rfl))) (by omega)
        (by omega) (by simp [residueTwoAffineBaseRow])
      simpa only [show 6 + 3 * (k - 6) = 3 * k - 12 by omega] using hm
  have m45 := residueTwoAffine_successor_corridor_mem k hk 4 5 (k - 5)
    (by omega) (by omega) (Or.inr rfl) (Or.inl rfl)
  have a0 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 2
    (3 * k - 12) (by omega) (by omega) (by omega) mleft
    (by simpa only [show 3 * k - 12 + 1 = 4 + 3 * (k - 5) by omega] using m24)
  have a1 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 2
    (4 + 3 * (k - 5)) (by omega) (by omega) (by omega) m24
    m34
  have a2 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 3
    (4 + 3 * (k - 5)) (by omega) (by omega) (by omega) m34
    (by simpa only [show 4 + 3 * (k - 5) + 1 = 5 + 3 * (k - 5) by omega] using m35)
  have a3 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 3
    (5 + 3 * (k - 5)) (by omega) (by omega) (by omega) m35
    m45
  have a4 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 3
    (5 + 3 * (k - 5)) (by omega) (by omega) (by omega) m35
    (by simpa only [show 5 + 3 * (k - 5) + 1 = 6 + 3 * (k - 5) by omega] using m36)
  have a5 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 2
    (6 + 3 * (k - 5)) (by omega) (by omega) (by omega) m26
    m36
  have a6 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 2
    (6 + 3 * (k - 5)) (by omega) (by omega) (by omega) m26
    (by simpa only [show 6 + 3 * (k - 5) + 1 = 4 + 3 * (k - 4) by omega]
      using m24')
  have a7 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) 1
    (4 + 3 * (k - 4)) (by omega) (by omega) (by omega) m14'
    m24'
  have p6 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨2, by omega⟩ ⟨6 + 3 * (k - 5), by omega⟩)
      (.cell ⟨1, by omega⟩ ⟨6 + 3 * (k - 5), by omega⟩) := by
    simpa only [show 2 - 1 = 1 by omega] using a6.reachable.symm
  have p7 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨1, by omega⟩ ⟨6 + 3 * (k - 5), by omega⟩)
      (.cell ⟨1, by omega⟩ ⟨4 + 3 * (k - 4), by omega⟩) := by
    simpa only [show 4 + 3 * (k - 4) - 1 = 6 + 3 * (k - 5) by omega] using
      a7.reachable
  have p0 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨1, by omega⟩ ⟨3 * k - 12, by omega⟩)
      (.cell ⟨2, by omega⟩ ⟨3 * k - 12, by omega⟩) := by
    simpa only [show 2 - 1 = 1 by omega] using a0.reachable
  have p1 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨2, by omega⟩ ⟨3 * k - 12, by omega⟩)
      (.cell ⟨2, by omega⟩ ⟨4 + 3 * (k - 5), by omega⟩) := by
    simpa only [show 4 + 3 * (k - 5) - 1 = 3 * k - 12 by omega] using a1.reachable
  have p2 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨2, by omega⟩ ⟨4 + 3 * (k - 5), by omega⟩)
      (.cell ⟨3, by omega⟩ ⟨4 + 3 * (k - 5), by omega⟩) := by
    simpa only [show 3 - 1 = 2 by omega] using a2.reachable
  have p3 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨3, by omega⟩ ⟨4 + 3 * (k - 5), by omega⟩)
      (.cell ⟨3, by omega⟩ ⟨5 + 3 * (k - 5), by omega⟩) := by
    simpa only [show 5 + 3 * (k - 5) - 1 = 4 + 3 * (k - 5) by omega] using a3.reachable
  have p4 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨3, by omega⟩ ⟨5 + 3 * (k - 5), by omega⟩)
      (.cell ⟨2, by omega⟩ ⟨5 + 3 * (k - 5), by omega⟩) := by
    simpa only [show 3 - 1 = 2 by omega] using a4.reachable.symm
  have p5 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (.cell ⟨2, by omega⟩ ⟨5 + 3 * (k - 5), by omega⟩)
      (.cell ⟨2, by omega⟩ ⟨6 + 3 * (k - 5), by omega⟩) := by
    simpa only [show 6 + 3 * (k - 5) - 1 = 5 + 3 * (k - 5) by omega] using a5.reachable
  have path := p0.trans (p1.trans (p2.trans (p3.trans (p4.trans
    (p5.trans (p6.trans p7))))))
  have hs : residueTwoAffineStepFace k (verticalDualEndpoints e).1 =
      .cell ⟨1, by omega⟩ ⟨3 * k - 12, by omega⟩ := by
    simp only [verticalDualEndpoints, dif_neg (by omega : e.col.val ≠ 0),
      residueTwoAffineStepFace]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
      simp [hrow, hcol] <;> (try split_ifs) <;> omega
  have ht : residueTwoAffineStepFace k (verticalDualEndpoints e).2 =
      .cell ⟨1, by omega⟩ ⟨3 * k - 8, by omega⟩ := by
    simp only [verticalDualEndpoints,
      dif_neg (by omega : e.col.val + 1 ≠ 3 * k + 2), residueTwoAffineStepFace]
    apply congrArg₂ GridFace.cell <;> apply Fin.ext <;>
      simp [hrow, hcol] <;> omega
  rw [hs, ht]
  simpa only [show 4 + 3 * (k - 4) = 3 * k - 8 by omega] using path

/-- Uniform transport for every old vertical U-U edge on the dual column seam. -/
theorem residueTwoAffineStep_vertical_colSeam_reachable
    (k : Nat) (hk : 5 ≤ k)
    (e : VerticalGridEdge (3 * k + 2) (3 * k + 2))
    (hcol : e.col.val = 3 * k - 11)
    (he₁ : (verticalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (verticalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (verticalDualEndpoints e).1)
      (residueTwoAffineStepFace k (verticalDualEndpoints e).2) := by
  let er : Fin (3 * k + 2) := ⟨e.row.val, by have := e.row.isLt; omega⟩
  have her : ((er, ⟨3 * k - 11, by omega⟩) :
      GridVertex (3 * k + 2) (3 * k + 2)) ∈ uResidueTwoAffine k := by
    convert he₁ using 1
    apply Prod.ext <;> apply Fin.ext <;>
      simp [er, verticalPrimalEndpoints, hcol]
  have hr := (residueTwoAffine_colSeam_row_bounds k hk er her).1
  dsimp [er] at hr
  by_cases hrow : e.row.val = 1
  · exact residueTwoAffineStep_vertical_colSeam_row_one k hk e hcol hrow
  · exact residueTwoAffineStep_vertical_colSeam_of_two_le k hk e hcol (by omega) he₂

/-- Every old vertical U-U edge transports to a successor dual path. -/
theorem residueTwoAffineStep_vertical_reachable
    (k : Nat) (hk : 5 ≤ k)
    (e : VerticalGridEdge (3 * k + 2) (3 * k + 2))
    (he₁ : (verticalPrimalEndpoints e).1 ∈ uResidueTwoAffine k)
    (he₂ : (verticalPrimalEndpoints e).2 ∈ uResidueTwoAffine k) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (residueTwoAffineStepFace k (verticalDualEndpoints e).1)
      (residueTwoAffineStepFace k (verticalDualEndpoints e).2) := by
  by_cases hcol : e.col.val = 3 * k - 11
  · exact residueTwoAffineStep_vertical_colSeam_reachable k hk e hcol he₁ he₂
  · exact residueTwoAffineStep_vertical_away_dualSeam_reachable k hk e hcol he₁ he₂

/-- A solid four-row rectangle of U vertices routes each of its three face
rows to the face immediately above the rectangle. -/
private theorem uuDual_threeRowRectangle_reachable
    (k : Nat) (U : Finset (GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)))
    (a lo hi gate r c : Nat)
    (ha : 0 < a) (hr : a ≤ r ∧ r < a + 3)
    (hc : lo ≤ c ∧ c ≤ hi) (hg : lo ≤ gate ∧ gate < hi)
    (hNrow : a + 3 < 3 * (k + 1) + 2)
    (hNcol : hi + 1 < 3 * (k + 1) + 2)
    (hmove : ∀ rr vv (hrr : a ≤ rr) (hrr' : rr ≤ a + 3),
      lo < vv → ∀ (hvv' : vv ≤ hi),
      ((⟨rr, by omega⟩, ⟨vv, by omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈ U)
    (hgate : ∀ rr (hrr : a ≤ rr) (hrr' : rr ≤ a + 3),
      ((⟨rr, by omega⟩, ⟨gate, by omega⟩) :
          GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈ U ∧
      ((⟨rr, by omega⟩, ⟨gate + 1, by omega⟩) :
          GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈ U) :
    (uuDualGraph U).Reachable
      (.cell ⟨r, by omega⟩ ⟨c, by omega⟩)
      (.cell ⟨a - 1, by omega⟩ ⟨gate, by omega⟩) := by
  have toLeft (rr x : Nat) (hrr : a ≤ rr) (hrr' : rr < a + 3)
      (hx : lo ≤ x) (hx' : x ≤ hi) :
      (uuDualGraph U).Reachable
        (.cell ⟨rr, by omega⟩ ⟨x, by omega⟩)
        (.cell ⟨rr, by omega⟩ ⟨lo, by omega⟩) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hx
    induction d with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ d ih =>
        have hm0 := hmove rr (lo + d + 1) hrr (by omega) (by omega) (by omega)
        have hm1 := hmove (rr + 1) (lo + d + 1) (by omega) (by omega)
          (by omega) (by omega)
        have hs := vertical_uu_dual_cells_adj U rr (lo + d + 1)
          (by omega) (by omega) (by omega) hm0 hm1
        have hp : (uuDualGraph U).Reachable
            (.cell ⟨rr, by omega⟩ ⟨lo + d + 1, by omega⟩)
            (.cell ⟨rr, by omega⟩ ⟨lo + d, by omega⟩) := by
          simpa only [show lo + d + 1 - 1 = lo + d by omega] using hs.reachable.symm
        exact hp.trans (ih (by omega) (by omega))
  have fromLeft (rr x : Nat) (hrr : a ≤ rr) (hrr' : rr < a + 3)
      (hx : lo ≤ x) (hx' : x ≤ hi) :
      (uuDualGraph U).Reachable
        (.cell ⟨rr, by omega⟩ ⟨lo, by omega⟩)
        (.cell ⟨rr, by omega⟩ ⟨x, by omega⟩) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hx
    induction d with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ d ih =>
        have hm0 := hmove rr (lo + d + 1) hrr (by omega) (by omega) (by omega)
        have hm1 := hmove (rr + 1) (lo + d + 1) (by omega) (by omega)
          (by omega) (by omega)
        have hs := vertical_uu_dual_cells_adj U rr (lo + d + 1)
          (by omega) (by omega) (by omega) hm0 hm1
        exact (ih (by omega) (by omega)).trans (by
          simpa only [Nat.add_assoc, show lo + (d + 1) - 1 = lo + d by omega]
            using hs.reachable)
  have across : (uuDualGraph U).Reachable
      (.cell ⟨r, by omega⟩ ⟨c, by omega⟩)
      (.cell ⟨r, by omega⟩ ⟨gate, by omega⟩) :=
    (toLeft r c hr.1 hr.2 hc.1 hc.2).trans
      (fromLeft r gate hr.1 hr.2 hg.1 (by omega))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hr.1
  have hdlt : d < 3 := by omega
  subst r
  have up (d : Nat) (hd : d < 3) :
      (uuDualGraph U).Reachable
        (.cell ⟨a + d, by omega⟩ ⟨gate, by omega⟩)
        (.cell ⟨a - 1, by omega⟩ ⟨gate, by omega⟩) := by
    induction d with
    | zero =>
        have hm0 := (hgate a (by omega) (by omega)).1
        have hm1 := (hgate a (by omega) (by omega)).2
        simpa only [Nat.add_zero] using
          (horizontal_uu_dual_cells_adj U a gate (by omega) (by omega) (by omega)
            hm0 hm1).reachable.symm
    | succ d ih =>
        have hm0 := (hgate (a + d + 1) (by omega) (by omega)).1
        have hm1 := (hgate (a + d + 1) (by omega) (by omega)).2
        have hs := horizontal_uu_dual_cells_adj U (a + d + 1) gate
          (by omega) (by omega) (by omega) hm0 hm1
        have hp : (uuDualGraph U).Reachable
            (.cell ⟨a + d + 1, by omega⟩ ⟨gate, by omega⟩)
            (.cell ⟨a + d, by omega⟩ ⟨gate, by omega⟩) := by
          simpa only [show a + d + 1 - 1 = a + d by omega] using hs.reachable.symm
        exact hp.trans (ih (by omega))
  exact across.trans (up d hdlt)

/-- Every face in one of the three newly inserted row copies attaches to an
embedded old face, including the cells in the inserted column slab. -/
theorem residueTwoAffineStepFace_insertedRows_reachable
    (k : Nat) (hk : 5 ≤ k) (r c : Fin (3 * (k + 1) + 1))
    (hr : 3 * k - 6 ≤ r.val ∧ r.val < 3 * k - 3) :
    ∃ y : GridFace (3 * k + 2) (3 * k + 2),
      (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable (.cell r c)
        (residueTwoAffineStepFace k y) := by
  let a := 3 * k - 6
  have hra : a ≤ r.val ∧ r.val < a + 3 := by dsimp [a]; omega
  have belowMem (rr bc : Nat) (hrr : a ≤ rr) (hrr' : rr ≤ a + 3)
      (hbc : bc = 1 ∨ bc = 2) :
      ((⟨rr, by omega⟩, ⟨bc, by omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1) := by
    have hrows : rr = a ∨ rr = a + 1 ∨ rr = a + 2 ∨ rr = a + 3 := by omega
    have hb (br : Nat) (hbr : br = 9 ∨ br = 10 ∨ br = 11) :
        bc ∈ residueTwoAffineBaseRow br := by
      rcases hbr with rfl | rfl | rfl <;> rcases hbc with rfl | rfl <;>
        simp [residueTwoAffineBaseRow]
    rcases hrows with rfl | rfl | rfl | rfl
    all_goals
      first
      | simpa only [show 9 + 3 * (k - 5) = a by dsimp [a]; omega] using
          residueTwoAffine_successor_repeated_below_mem k hk 9 bc (k - 5)
          (by omega) (by omega) (by omega) (hb 9 (by omega))
      | simpa only [show 10 + 3 * (k - 5) = a + 1 by dsimp [a]; omega] using
          residueTwoAffine_successor_repeated_below_mem k hk 10 bc (k - 5)
          (by omega) (by omega) (by omega) (hb 10 (by omega))
      | simpa only [show 11 + 3 * (k - 5) = a + 2 by dsimp [a]; omega] using
          residueTwoAffine_successor_repeated_below_mem k hk 11 bc (k - 5)
          (by omega) (by omega) (by omega) (hb 11 (by omega))
      | simpa only [show 9 + 3 * (k - 4) = a + 3 by dsimp [a]; omega] using
          residueTwoAffine_successor_repeated_below_mem k hk 9 bc (k - 4)
          (by omega) (by omega) (by omega) (hb 9 (by omega))
  have pumpMem (q rr bc : Nat) (hq : q < k - 3)
      (hrr : a ≤ rr) (hrr' : rr ≤ a + 3) (hbc : bc = 4 ∨ bc = 5) :
      ((⟨rr, by omega⟩, ⟨bc + 3 * q, by omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1) := by
    have hrows : rr = a ∨ rr = a + 1 ∨ rr = a + 2 ∨ rr = a + 3 := by omega
    have hb (br : Nat) (hbr : br = 9 ∨ br = 10 ∨ br = 11) :
        bc ∈ residueTwoAffineBaseRow br := by
      rcases hbr with rfl | rfl | rfl <;> rcases hbc with rfl | rfl <;>
        simp [residueTwoAffineBaseRow]
    rcases hrows with rfl | rfl | rfl | rfl
    all_goals
      first
      | simpa only [show 9 + 3 * (k - 5) = a by dsimp [a]; omega] using
          residueTwoAffine_successor_repeated_pump_mem k hk 9 bc (k - 5) q
          (by omega) (by omega) (by omega) hq (hb 9 (by omega))
      | simpa only [show 10 + 3 * (k - 5) = a + 1 by dsimp [a]; omega] using
          residueTwoAffine_successor_repeated_pump_mem k hk 10 bc (k - 5) q
          (by omega) (by omega) (by omega) hq (hb 10 (by omega))
      | simpa only [show 11 + 3 * (k - 5) = a + 2 by dsimp [a]; omega] using
          residueTwoAffine_successor_repeated_pump_mem k hk 11 bc (k - 5) q
          (by omega) (by omega) (by omega) hq (hb 11 (by omega))
      | simpa only [show 9 + 3 * (k - 4) = a + 3 by dsimp [a]; omega] using
          residueTwoAffine_successor_repeated_pump_mem k hk 9 bc (k - 4) q
          (by omega) (by omega) (by omega) hq (hb 9 (by omega))
  have rightMem (rr bc : Nat) (hrr : a ≤ rr) (hrr' : rr ≤ a + 3)
      (hbc : bc = 7 ∨ bc = 8 ∨ bc = 14 ∨ bc = 15) :
      ((⟨rr, by omega⟩, ⟨bc + 3 * (k - 4), by omega⟩) :
        GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
          uResidueTwoAffine (k + 1) := by
    have hrows : rr = a ∨ rr = a + 1 ∨ rr = a + 2 ∨ rr = a + 3 := by omega
    have hb (br : Nat) (hbr : br = 9 ∨ br = 10 ∨ br = 11) :
        bc ∈ residueTwoAffineBaseRow br := by
      rcases hbr with rfl | rfl | rfl <;> rcases hbc with rfl | rfl | rfl | rfl <;>
        simp [residueTwoAffineBaseRow]
    rcases hrows with rfl | rfl | rfl | rfl
    all_goals
      first
      | simpa only [show 9 + 3 * (k - 5) = a by dsimp [a]; omega] using
          residueTwoAffine_successor_repeated_right_mem k hk 9 bc (k - 5)
          (by omega) (by omega) (by omega) (by omega) (hb 9 (by omega))
      | simpa only [show 10 + 3 * (k - 5) = a + 1 by dsimp [a]; omega] using
          residueTwoAffine_successor_repeated_right_mem k hk 10 bc (k - 5)
          (by omega) (by omega) (by omega) (by omega) (hb 10 (by omega))
      | simpa only [show 11 + 3 * (k - 5) = a + 2 by dsimp [a]; omega] using
          residueTwoAffine_successor_repeated_right_mem k hk 11 bc (k - 5)
          (by omega) (by omega) (by omega) (by omega) (hb 11 (by omega))
      | simpa only [show 9 + 3 * (k - 4) = a + 3 by dsimp [a]; omega] using
          residueTwoAffine_successor_repeated_right_mem k hk 9 bc (k - 4)
          (by omega) (by omega) (by omega) (by omega) (hb 9 (by omega))
  have attachAbove (g : Nat) (hg : g < 3 * (k + 1) + 1) :
      ∃ y : GridFace (3 * k + 2) (3 * k + 2),
        (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
          (.cell ⟨a - 1, by omega⟩ ⟨g, hg⟩) (residueTwoAffineStepFace k y) := by
    by_cases hins : 3 * k - 11 ≤ g ∧ g < 3 * k - 8
    · exact residueTwoAffineStepFace_insertedColumns_reachable k hk
        ⟨a - 1, by omega⟩ ⟨g, hg⟩ (Or.inl (by dsimp [a]; omega)) hins
    · exact residueTwoAffineStepFace_regular_reachable k hk
        ⟨a - 1, by omega⟩ ⟨g, hg⟩ (Or.inl (by dsimp [a]; omega)) (by
          have : g < 3 * k - 11 ∨ 3 * k - 8 ≤ g := by omega
          simpa only using this)
  have finish (g : Nat) (hg : g < 3 * (k + 1) + 1)
      (hp : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable (.cell r c)
        (.cell ⟨a - 1, by omega⟩ ⟨g, hg⟩)) :
      ∃ y : GridFace (3 * k + 2) (3 * k + 2),
        (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable (.cell r c)
          (residueTwoAffineStepFace k y) := by
    obtain ⟨y, hy⟩ := attachAbove g hg
    exact ⟨y, hp.trans hy⟩
  by_cases hprefix : c.val < 3
  · have hp := uuDual_threeRowRectangle_reachable k
      (uResidueTwoAffine (k + 1)) a 0 2 1 r.val c.val
      (by dsimp [a]; omega) hra (by omega) (by omega) (by omega) (by omega)
      (by
        intro rr vv hrr hrr' hvv hvv'
        exact belowMem rr vv hrr hrr' (by omega))
      (by
        intro rr hrr hrr'
        exact ⟨belowMem rr 1 hrr hrr' (Or.inl rfl),
          belowMem rr 2 hrr hrr' (Or.inr rfl)⟩)
    exact finish 1 (by omega) (by simpa [a] using hp)
  · by_cases hpump : c.val < 3 * k - 6
    · let q := (c.val - 3) / 3
      let lo := 3 + 3 * q
      have hmod : (c.val - 3) % 3 < 3 := Nat.mod_lt _ (by omega)
      have hcdecomp : c.val = lo + (c.val - 3) % 3 := by
        dsimp [lo, q]
        have := (Nat.mod_add_div (c.val - 3) 3).symm
        omega
      have hq : q < k - 3 := by
        dsimp [q]
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).2
        omega
      have hp := uuDual_threeRowRectangle_reachable k
        (uResidueTwoAffine (k + 1)) a lo (lo + 2) (lo + 1) r.val c.val
        (by dsimp [a]; omega) hra (by omega) (by omega) (by omega) (by omega)
        (by
          intro rr vv hrr hrr' hvv hvv'
          have hv : vv = 4 + 3 * q ∨ vv = 5 + 3 * q := by dsimp [lo] at *; omega
          rcases hv with rfl | rfl
          · exact pumpMem q rr 4 hq hrr hrr' (Or.inl rfl)
          · exact pumpMem q rr 5 hq hrr hrr' (Or.inr rfl))
        (by
          intro rr hrr hrr'
          constructor
          · convert pumpMem q rr 4 hq hrr hrr' (Or.inl rfl) using 1
            apply Prod.ext <;> apply Fin.ext <;> simp [lo]
            omega
          · convert pumpMem q rr 5 hq hrr hrr' (Or.inr rfl) using 1
            apply Prod.ext <;> apply Fin.ext <;> simp [lo]
            omega)
      exact finish (lo + 1) (by dsimp [lo, q]; omega) (by simpa [a] using hp)
    · let s := 3 * k - 6
      have hcs : s ≤ c.val := by dsimp [s]; omega
      by_cases hfirst : c.val ≤ s + 2
      · have hp := uuDual_threeRowRectangle_reachable k
          (uResidueTwoAffine (k + 1)) a s (s + 2) (s + 1) r.val c.val
          (by dsimp [a]; omega) hra (by omega) (by omega) (by omega) (by omega)
          (by
            intro rr vv hrr hrr' hvv hvv'
            have hv : vv = 7 + 3 * (k - 4) ∨ vv = 8 + 3 * (k - 4) := by
              dsimp [s] at *; omega
            rcases hv with rfl | rfl
            · exact rightMem rr 7 hrr hrr' (Or.inl rfl)
            · exact rightMem rr 8 hrr hrr' (Or.inr (Or.inl rfl)))
          (by
            intro rr hrr hrr'
            constructor
            · convert rightMem rr 7 hrr hrr' (Or.inl rfl) using 1
              apply Prod.ext <;> apply Fin.ext <;> simp [s]
              omega
            · convert rightMem rr 8 hrr hrr' (Or.inr (Or.inl rfl)) using 1
              apply Prod.ext <;> apply Fin.ext <;> simp [s]
              omega)
        exact finish (s + 1) (by dsimp [s]; omega) (by simpa [a] using hp)
      · by_cases hlast : s + 7 ≤ c.val
        · have hp := uuDual_threeRowRectangle_reachable k
            (uResidueTwoAffine (k + 1)) a (s + 7) (s + 9) (s + 8) r.val c.val
            (by dsimp [a]; omega) hra (by omega) (by omega) (by omega) (by omega)
            (by
              intro rr vv hrr hrr' hvv hvv'
              have hv : vv = 14 + 3 * (k - 4) ∨ vv = 15 + 3 * (k - 4) := by
                dsimp [s] at *; omega
              rcases hv with rfl | rfl
              · exact rightMem rr 14 hrr hrr' (Or.inr (Or.inr (Or.inl rfl)))
              · exact rightMem rr 15 hrr hrr' (Or.inr (Or.inr (Or.inr rfl))))
            (by
              intro rr hrr hrr'
              constructor
              · convert rightMem rr 14 hrr hrr' (Or.inr (Or.inr (Or.inl rfl))) using 1
                apply Prod.ext <;> apply Fin.ext <;> simp [s]
                omega
              · convert rightMem rr 15 hrr hrr' (Or.inr (Or.inr (Or.inr rfl))) using 1
                apply Prod.ext <;> apply Fin.ext <;> simp [s]
                omega)
          exact finish (s + 8) (by dsimp [s]; omega) (by simpa [a] using hp)
        · have smem (br bc j : Nat) (hbr : 9 ≤ br ∧ br < 12)
              (hbc : 7 ≤ bc) (hbc' : bc < 17) (hj : j < k - 3)
              (hb : bc ∈ residueTwoAffineBaseRow br) :
              ((⟨br + 3 * j, by omega⟩, ⟨bc + 3 * (k - 4), by omega⟩) :
                GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
                  uResidueTwoAffine (k + 1) :=
            residueTwoAffine_successor_repeated_right_mem k hk br bc j hbr hbc hbc' hj hb
          have A (bc : Nat) (hbc : 7 ≤ bc) (hbc' : bc < 17)
              (hb : bc ∈ residueTwoAffineBaseRow 9) :
              ((⟨a, by omega⟩, ⟨bc + 3 * (k - 4), by omega⟩) :
                GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
                  uResidueTwoAffine (k + 1) := by
            convert smem 9 bc (k - 5) (by omega) hbc hbc' (by omega) hb using 1
            apply Prod.ext <;> apply Fin.ext <;> simp [a]
            omega
          have B (bc : Nat) (hbc : 7 ≤ bc) (hbc' : bc < 17)
              (hb : bc ∈ residueTwoAffineBaseRow 10) :
              ((⟨a + 1, by omega⟩, ⟨bc + 3 * (k - 4), by omega⟩) :
                GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
                  uResidueTwoAffine (k + 1) := by
            convert smem 10 bc (k - 5) (by omega) hbc hbc' (by omega) hb using 1
            apply Prod.ext <;> apply Fin.ext <;> simp [a]
            omega
          have C (bc : Nat) (hbc : 7 ≤ bc) (hbc' : bc < 17)
              (hb : bc ∈ residueTwoAffineBaseRow 11) :
              ((⟨a + 2, by omega⟩, ⟨bc + 3 * (k - 4), by omega⟩) :
                GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
                  uResidueTwoAffine (k + 1) := by
            convert smem 11 bc (k - 5) (by omega) hbc hbc' (by omega) hb using 1
            apply Prod.ext <;> apply Fin.ext <;> simp [a]
            omega
          have D (bc : Nat) (hbc : 7 ≤ bc) (hbc' : bc < 17)
              (hb : bc ∈ residueTwoAffineBaseRow 9) :
              ((⟨a + 3, by omega⟩, ⟨bc + 3 * (k - 4), by omega⟩) :
                GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2)) ∈
                  uResidueTwoAffine (k + 1) := by
            convert smem 9 bc (k - 4) (by omega) hbc hbc' (by omega) hb using 1
            apply Prod.ext <;> apply Fin.ext <;> simp [a]
            omega
          let p := s + 3
          have ma9 := A 9 (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
          have ma10 := A 10 (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
          have ma12 := A 12 (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
          have mb10 := B 10 (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
          have mb11 := B 11 (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
          have mb12 := B 12 (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
          have mc10 := C 10 (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
          have mc11 := C 11 (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
          have mc12 := C 12 (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
          have md10 := D 10 (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
          have md12 := D 12 (by omega) (by omega) (by simp [residueTwoAffineBaseRow])
          have up0 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) a p
            (by omega) (by omega) (by omega)
            (by convert ma9 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
            (by convert ma10 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
          have va10 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) a (p + 1)
            (by omega) (by omega) (by omega)
            (by convert ma10 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
            (by convert mb10 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
          have va12 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) a (p + 3)
            (by omega) (by omega) (by omega)
            (by convert ma12 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
            (by convert mb12 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
          have vb10 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) (a + 1) (p + 1)
            (by omega) (by omega) (by omega)
            (by convert mb10 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
            (by convert mc10 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
          have vb11 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) (a + 1) (p + 2)
            (by omega) (by omega) (by omega)
            (by convert mb11 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
            (by convert mc11 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
          have vb12 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) (a + 1) (p + 3)
            (by omega) (by omega) (by omega)
            (by convert mb12 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
            (by convert mc12 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
          have vc10 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) (a + 2) (p + 1)
            (by omega) (by omega) (by omega)
            (by convert mc10 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
            (by convert md10 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
          have vc12 := vertical_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) (a + 2) (p + 3)
            (by omega) (by omega) (by omega)
            (by convert mc12 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
            (by convert md12 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
          have ab10 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) (a + 1) (p + 1)
            (by omega) (by omega) (by omega)
            (by convert mb10 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
            (by convert mb11 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
          have ab11 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) (a + 1) (p + 2)
            (by omega) (by omega) (by omega)
            (by convert mb11 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
            (by convert mb12 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
          have bc10 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) (a + 2) (p + 1)
            (by omega) (by omega) (by omega)
            (by convert mc10 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
            (by convert mc11 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
          have bc11 := horizontal_uu_dual_cells_adj (uResidueTwoAffine (k + 1)) (a + 2) (p + 2)
            (by omega) (by omega) (by omega)
            (by convert mc11 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
            (by convert mc12 using 1; apply Prod.ext <;> apply Fin.ext <;> simp [p, s]; omega)
          have top : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
              (.cell ⟨a, by omega⟩ ⟨p, by omega⟩)
              (.cell ⟨a - 1, by omega⟩ ⟨p, by omega⟩) := by
            simpa only [show a - 1 = a - 1 by rfl] using up0.reachable.symm
          have a4 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
              (.cell ⟨a, by omega⟩ ⟨p + 1, by omega⟩)
              (.cell ⟨a, by omega⟩ ⟨p, by omega⟩) := by
            simpa only [show p + 1 - 1 = p by omega] using va10.reachable.symm
          have a6 : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
              (.cell ⟨a, by omega⟩ ⟨p + 3, by omega⟩)
              (.cell ⟨a, by omega⟩ ⟨p + 2, by omega⟩) := by
            simpa only [show p + 3 - 1 = p + 2 by omega] using va12.reachable.symm
          have b4a4 := ab10.reachable.symm
          have a5b5 := ab11.reachable
          have c4b4 := bc10.reachable.symm
          have c5b5 := bc11.reachable.symm
          have b3b4 := vb10.reachable
          have b5b4 := vb11.reachable.symm
          have b6b5 := vb12.reachable.symm
          have c3c4 := vc10.reachable
          have c6c5 := vc12.reachable.symm
          have routeA4 := a4.trans top
          have routeB4 := b4a4.trans routeA4
          have routeB3 := b3b4.trans routeB4
          have routeB5 := b5b4.trans routeB4
          have routeB6 := b6b5.trans routeB5
          have routeA5 := a5b5.trans routeB5
          have routeA6 := a6.trans routeA5
          have routeC4 := c4b4.trans routeB4
          have routeC3 := c3c4.trans routeC4
          have routeC5 := c5b5.trans routeB5
          have routeC6 := c6c5.trans routeC5
          have hrow : r.val = a ∨ r.val = a + 1 ∨ r.val = a + 2 := by omega
          have hcol : c.val = p ∨ c.val = p + 1 ∨ c.val = p + 2 ∨ c.val = p + 3 := by
            dsimp [p, s]; omega
          have close (rr cc : Nat) (hrr : r.val = rr) (hcc : c.val = cc)
              (route : (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
                (.cell ⟨rr, by omega⟩ ⟨cc, by omega⟩)
                (.cell ⟨a - 1, by omega⟩ ⟨p, by omega⟩)) :
              ∃ y : GridFace (3 * k + 2) (3 * k + 2),
                (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable (.cell r c)
                  (residueTwoAffineStepFace k y) := by
            apply finish p (by dsimp [p, s]; omega)
            convert route using 1
            apply congrArg₂ GridFace.cell <;> apply Fin.ext <;> simp [hrr, hcc]
          rcases hrow with hrow | hrow | hrow <;>
            rcases hcol with hcol | hcol | hcol | hcol
          · exact close a p hrow hcol top
          · exact close a (p + 1) hrow hcol routeA4
          · exact close a (p + 2) hrow hcol routeA5
          · exact close a (p + 3) hrow hcol routeA6
          · exact close (a + 1) p hrow hcol routeB3
          · exact close (a + 1) (p + 1) hrow hcol routeB4
          · exact close (a + 1) (p + 2) hrow hcol routeB5
          · exact close (a + 1) (p + 3) hrow hcol routeB6
          · exact close (a + 2) p hrow hcol routeC3
          · exact close (a + 2) (p + 1) hrow hcol routeC4
          · exact close (a + 2) (p + 2) hrow hcol routeC5
          · exact close (a + 2) (p + 3) hrow hcol routeC6

/-- Attachment on the unbounded face and every successor cell outside the
inserted row slab and column slab intersection. -/
theorem residueTwoAffineStepFace_attaches_on_completed_regions
    (k : Nat) (hk : 5 ≤ k)
    (x : GridFace (3 * (k + 1) + 2) (3 * (k + 1) + 2))
    (hx : match x with
      | .out => True
      | .cell r c =>
          (((r.val < 3 * k - 6 ∨ 3 * k - 3 ≤ r.val) ∧
            (c.val < 3 * k - 11 ∨ 3 * k - 8 ≤ c.val)) ∨
           ((r.val < 3 * k - 6 ∨ 3 * k - 3 ≤ r.val) ∧
            3 * k - 11 ≤ c.val ∧ c.val < 3 * k - 8))) :
    ∃ y : GridFace (3 * k + 2) (3 * k + 2),
      (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable x
        (residueTwoAffineStepFace k y) := by
  cases x with
  | out =>
      exact ⟨.out, SimpleGraph.Reachable.refl _⟩
  | cell r c =>
      rcases hx with ⟨hr, hc⟩ | ⟨hc, hr⟩
      · exact residueTwoAffineStepFace_regular_reachable k hk r c hr hc
      · exact residueTwoAffineStepFace_insertedColumns_reachable k hk r c hc hr

/-- Every successor face attaches to the embedded old dual graph. -/
theorem residueTwoAffineStepGeometry_attaches
    (k : Nat) (hk : 5 ≤ k)
    (x : GridFace (3 * (k + 1) + 2) (3 * (k + 1) + 2)) :
    ∃ y : GridFace (3 * k + 2) (3 * k + 2),
      (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable x
        (residueTwoAffineStepFace k y) := by
  cases x with
  | out => exact ⟨.out, SimpleGraph.Reachable.refl _⟩
  | cell r c =>
      by_cases hr : 3 * k - 6 ≤ r.val ∧ r.val < 3 * k - 3
      · exact residueTwoAffineStepFace_insertedRows_reachable k hk r c hr
      · by_cases hc : 3 * k - 11 ≤ c.val ∧ c.val < 3 * k - 8
        · exact residueTwoAffineStepFace_insertedColumns_reachable k hk r c (by omega) hc
        · exact residueTwoAffineStepFace_regular_reachable k hk r c (by omega) (by omega)

/-- Exact local obligations for inserting one repeated block of three rows and
three columns.  Old dual edges may become paths after the insertion. -/
structure ResidueTwoAffineStepGeometry (k : Nat) where
  embed : GridFace (3 * k + 2) (3 * k + 2) →
    GridFace (3 * (k + 1) + 2) (3 * (k + 1) + 2)
  embed_eq : embed = residueTwoAffineStepFace k
  horizontal : ∀ (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2)),
    (horizontalPrimalEndpoints e).1 ∈ uResidueTwoAffine k →
    (horizontalPrimalEndpoints e).2 ∈ uResidueTwoAffine k →
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (embed (horizontalDualEndpoints e).1)
      (embed (horizontalDualEndpoints e).2)
  vertical : ∀ (e : VerticalGridEdge (3 * k + 2) (3 * k + 2)),
    (verticalPrimalEndpoints e).1 ∈ uResidueTwoAffine k →
    (verticalPrimalEndpoints e).2 ∈ uResidueTwoAffine k →
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable
      (embed (verticalDualEndpoints e).1)
      (embed (verticalDualEndpoints e).2)
  attaches : ∀ x : GridFace (3 * (k + 1) + 2) (3 * (k + 1) + 2),
    ∃ y : GridFace (3 * k + 2) (3 * k + 2),
      (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable x (embed y)

/-- The symbolic row and column routes discharge every local obligation for
one affine width-three step. -/
def residueTwoAffineStepGeometry (k : Nat) (hk : 5 ≤ k) :
    ResidueTwoAffineStepGeometry k where
  embed := residueTwoAffineStepFace k
  embed_eq := rfl
  horizontal := residueTwoAffineStep_horizontal_reachable k hk
  vertical := residueTwoAffineStep_vertical_reachable k hk
  attaches := residueTwoAffineStepGeometry_attaches k hk

namespace ResidueTwoAffineStepGeometry

/-- Every old dual adjacency lifts to a successor path. -/
theorem reachable_of_adj {k : Nat} (S : ResidueTwoAffineStepGeometry k)
    {x y : GridFace (3 * k + 2) (3 * k + 2)}
    (hxy : (uuDualGraph (uResidueTwoAffine k)).Adj x y) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable (S.embed x) (S.embed y) := by
  rcases hxy with ⟨_, h | h⟩
  · rcases h with ⟨e, he₁, he₂, hends⟩
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.horizontal e he₁ he₂
    · exact (S.horizontal e he₁ he₂).symm
  · rcases h with ⟨e, he₁, he₂, hends⟩
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.vertical e he₁ he₂
    · exact (S.vertical e he₁ he₂).symm

/-- Every old dual path lifts by replacing each edge with its local path. -/
theorem reachable_of_reachable {k : Nat} (S : ResidueTwoAffineStepGeometry k)
    {x y : GridFace (3 * k + 2) (3 * k + 2)}
    (hxy : (uuDualGraph (uResidueTwoAffine k)).Reachable x y) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Reachable (S.embed x) (S.embed y) :=
  reachable_map_of_adj_reachable S.embed S.reachable_of_adj hxy

/-- One completed local geometry transports dual connectivity through a
width-three affine step and attaches all newly created faces. -/
theorem connected {k : Nat} (S : ResidueTwoAffineStepGeometry k)
    (hold : (uuDualGraph (uResidueTwoAffine k)).Connected) :
    (uuDualGraph (uResidueTwoAffine (k + 1))).Connected :=
  connected_of_reachable_map_of_attaches S.embed hold S.reachable_of_adj S.attaches

end ResidueTwoAffineStepGeometry

/-- The exact four local obligations, uniformly discharged, imply arbitrary-k
dual connectivity. -/
theorem uResidueTwoAffine_dual_connected_of_stepGeometry
    (steps : ∀ k, 5 ≤ k → ResidueTwoAffineStepGeometry k) :
    ∀ k, 5 ≤ k → (uuDualGraph (uResidueTwoAffine k)).Connected := by
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simpa using uResidueTwoAffine_five_dual_connected
  | succ d ih =>
      rw [show 5 + d.succ = 5 + d + 1 by omega]
      exact (steps (5 + d) (by omega)).connected (ih (by omega))

/-- The affine residue-two U-U dual is connected at every admissible size. -/
theorem uResidueTwoAffine_dual_connected (k : Nat) (hk : 5 ≤ k) :
    (uuDualGraph (uResidueTwoAffine k)).Connected :=
  uResidueTwoAffine_dual_connected_of_stepGeometry residueTwoAffineStepGeometry k hk

end GridGraphs
