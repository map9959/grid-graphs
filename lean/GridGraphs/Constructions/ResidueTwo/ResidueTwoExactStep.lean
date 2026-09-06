import GridGraphs.Constructions.ResidueTwo.ResidueTwoExact
import GridGraphs.Results.DiagonalFormula
import GridGraphs.Constructions.ConnectivityTransport

/-!
# One-step geometry for the exact residue-two family

The insertion is made immediately before the last repeated three-row and
three-column blocks.  Consequently an old dual edge crossing an insertion line
must be replaced by a path, rather than by a single successor edge.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- Embed an old face after inserting three rows at `3k-13` and three columns
at `3k-7`.  These are respectively `5+3(k-6)` and `11+3(k-6)`. -/
def residueTwoExactStepFace (k : Nat) :
    GridFace (3 * k + 2) (3 * k + 2) →
      GridFace (3 * (k + 1) + 2) (3 * (k + 1) + 2)
  | .out => .out
  | .cell r c =>
      .cell
        ⟨if 3 * k - 13 ≤ r.val then r.val + 3 else r.val, by
          split <;> have := r.isLt <;> omega⟩
        ⟨if 3 * k - 7 ≤ c.val then c.val + 3 else c.val, by
          split <;> have := c.isLt <;> omega⟩

@[simp] theorem residueTwoExactStepFace_out (k : Nat) :
    residueTwoExactStepFace k .out = .out := rfl

/-- The symbolic local obligations for one exact width-three insertion. -/
structure ResidueTwoExactStepGeometry (k : Nat) where
  horizontal : ∀ (e : HorizontalGridEdge (3 * k + 2) (3 * k + 2)),
    (horizontalPrimalEndpoints e).1 ∈ uResidueTwoExact k →
    (horizontalPrimalEndpoints e).2 ∈ uResidueTwoExact k →
    (uuDualGraph (uResidueTwoExact (k + 1))).Reachable
      (residueTwoExactStepFace k (horizontalDualEndpoints e).1)
      (residueTwoExactStepFace k (horizontalDualEndpoints e).2)
  vertical : ∀ (e : VerticalGridEdge (3 * k + 2) (3 * k + 2)),
    (verticalPrimalEndpoints e).1 ∈ uResidueTwoExact k →
    (verticalPrimalEndpoints e).2 ∈ uResidueTwoExact k →
    (uuDualGraph (uResidueTwoExact (k + 1))).Reachable
      (residueTwoExactStepFace k (verticalDualEndpoints e).1)
      (residueTwoExactStepFace k (verticalDualEndpoints e).2)
  attaches : ∀ x : GridFace (3 * (k + 1) + 2) (3 * (k + 1) + 2),
    ∃ y : GridFace (3 * k + 2) (3 * k + 2),
      (uuDualGraph (uResidueTwoExact (k + 1))).Reachable x
        (residueTwoExactStepFace k y)

namespace ResidueTwoExactStepGeometry

/-- Every old dual edge is replaced by its specified successor path. -/
theorem reachable_of_adj {k : Nat} (S : ResidueTwoExactStepGeometry k)
    {x y : GridFace (3 * k + 2) (3 * k + 2)}
    (hxy : (uuDualGraph (uResidueTwoExact k)).Adj x y) :
    (uuDualGraph (uResidueTwoExact (k + 1))).Reachable
      (residueTwoExactStepFace k x) (residueTwoExactStepFace k y) := by
  rcases hxy with ⟨_, h | h⟩
  · rcases h with ⟨e, he₁, he₂, hends⟩
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.horizontal e he₁ he₂
    · exact (S.horizontal e he₁ he₂).symm
  · rcases h with ⟨e, he₁, he₂, hends⟩
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.vertical e he₁ he₂
    · exact (S.vertical e he₁ he₂).symm

/-- Replacing each edge transports every old dual path. -/
theorem reachable_of_reachable {k : Nat} (S : ResidueTwoExactStepGeometry k)
    {x y : GridFace (3 * k + 2) (3 * k + 2)}
    (hxy : (uuDualGraph (uResidueTwoExact k)).Reachable x y) :
    (uuDualGraph (uResidueTwoExact (k + 1))).Reachable
      (residueTwoExactStepFace k x) (residueTwoExactStepFace k y) := by
  exact reachable_map_of_adj_reachable (residueTwoExactStepFace k)
    S.reachable_of_adj hxy

/-- Path replacement and attachment transport connectivity through a step. -/
theorem connected {k : Nat} (S : ResidueTwoExactStepGeometry k)
    (hold : (uuDualGraph (uResidueTwoExact k)).Connected) :
    (uuDualGraph (uResidueTwoExact (k + 1))).Connected :=
  connected_of_reachable_map_of_attaches (residueTwoExactStepFace k) hold
    S.reachable_of_adj S.attaches

end ResidueTwoExactStepGeometry

/-- The exact base has connected U-U dual. -/
theorem uResidueTwoExact_six_dual_connected :
    (uuDualGraph (uResidueTwoExact 6)).Connected := by
  rw [uResidueTwoExact_six]
  exact finiteU20RankedDualCertificate.connected

/-! ## The first exact pump is obstructed -/

/-- The face exposed by the checkerboard at the first repeated-column seam. -/
private abbrev residueTwoExactSevenCutFace : GridFace 23 23 :=
  .cell ⟨4, by omega⟩ ⟨13, by omega⟩

/-- At `k=7`, the lower-left vertex of the obstructing checkerboard is not in
the exact pattern.  Symbolically, row `5` has base type `5`, while column `13`
has base type `13`, and that base entry is absent. -/
private theorem residueTwoExact_seven_5_13_not_mem :
    (⟨5, by omega⟩, ⟨13, by omega⟩) ∉ uResidueTwoExact 7 := by
  classical
  simp only [uResidueTwoExact, dif_pos (by omega : 6 ≤ 7), Finset.mem_image,
    residueTwoExactOccurrences, Finset.mem_univ, true_and, not_exists]
  intro x
  change ResidueTwoExactOccurrence 1 at x
  intro hx
  have hr := congrArg (fun z => z.1.val) hx
  have hc := congrArg (fun z => z.2.val) hx
  simp only [residueTwoExactVertex] at hr hc
  have xr := x.1.isLt
  have xc := x.2.1.isLt
  have hrow : x.1.val = 5 := by
    by_cases hrp : 5 ≤ x.1.val ∧ x.1.val < 5 + 3
    · rw [residueTwoExactExpandIndex_of_pump 5 1 (by omega) _ hrp] at hr
      have hcopy := x.2.2.val.1.isLt
      simp [residueTwoExactMultiplicity, hrp] at hcopy
      simp only at hr
      omega
    · by_cases hra : 5 + 3 ≤ x.1.val
      · rw [residueTwoExactExpandIndex_of_above 5 1 (by omega) _ hrp hra] at hr
        simp only at hr
        omega
      · rw [residueTwoExactExpandIndex_of_below 5 1 (by omega) _ hrp hra] at hr
        omega
  have hcol : x.2.1.val = 13 := by
    by_cases hcp : 11 ≤ x.2.1.val ∧ x.2.1.val < 11 + 3
    · rw [residueTwoExactExpandIndex_of_pump 11 1 (by omega) _ hcp] at hc
      have hcopy := x.2.2.val.2.isLt
      simp [residueTwoExactMultiplicity, hcp] at hcopy
      simp only at hc
      omega
    · by_cases hca : 11 + 3 ≤ x.2.1.val
      · rw [residueTwoExactExpandIndex_of_above 11 1 (by omega) _ hcp hca] at hc
        simp only at hc
        omega
      · rw [residueTwoExactExpandIndex_of_below 11 1 (by omega) _ hcp hca] at hc
        simp only at hc
        omega
  have hbase := x.2.2.property
  simp [IsResidueTwoExactBase, residueTwoExactBaseRow, hrow, hcol] at hbase

/-- At `k=7`, the upper-right vertex of the same checkerboard is absent:
column `14` is the second copy of base column `11`, absent from base row `4`. -/
private theorem residueTwoExact_seven_4_14_not_mem :
    (⟨4, by omega⟩, ⟨14, by omega⟩) ∉ uResidueTwoExact 7 := by
  classical
  simp only [uResidueTwoExact, dif_pos (by omega : 6 ≤ 7), Finset.mem_image,
    residueTwoExactOccurrences, Finset.mem_univ, true_and, not_exists]
  intro x
  change ResidueTwoExactOccurrence 1 at x
  intro hx
  have hr := congrArg (fun z => z.1.val) hx
  have hc := congrArg (fun z => z.2.val) hx
  simp only [residueTwoExactVertex] at hr hc
  have xr := x.1.isLt
  have xc := x.2.1.isLt
  have hrow : x.1.val = 4 := by
    by_cases hrp : 5 ≤ x.1.val ∧ x.1.val < 5 + 3
    · rw [residueTwoExactExpandIndex_of_pump 5 1 (by omega) _ hrp] at hr
      have hcopy := x.2.2.val.1.isLt
      simp [residueTwoExactMultiplicity, hrp] at hcopy
      simp only at hr
      omega
    · by_cases hra : 5 + 3 ≤ x.1.val
      · rw [residueTwoExactExpandIndex_of_above 5 1 (by omega) _ hrp hra] at hr
        simp only at hr
        omega
      · rw [residueTwoExactExpandIndex_of_below 5 1 (by omega) _ hrp hra] at hr
        omega
  have hcol : x.2.1.val = 11 := by
    by_cases hcp : 11 ≤ x.2.1.val ∧ x.2.1.val < 11 + 3
    · rw [residueTwoExactExpandIndex_of_pump 11 1 (by omega) _ hcp] at hc
      have hcopy := x.2.2.val.2.isLt
      simp [residueTwoExactMultiplicity, hcp] at hcopy
      simp only at hc
      omega
    · by_cases hca : 11 + 3 ≤ x.2.1.val
      · rw [residueTwoExactExpandIndex_of_above 11 1 (by omega) _ hcp hca] at hc
        simp only at hc
        omega
      · rw [residueTwoExactExpandIndex_of_below 11 1 (by omega) _ hcp hca] at hc
        simp only at hc
        omega
  have hbase := x.2.2.property
  simp [IsResidueTwoExactBase, residueTwoExactBaseRow, hrow, hcol] at hbase

/-- No U-U dual edge is incident to the checkerboard face. -/
private theorem residueTwoExactSevenCutFace_not_adj
    (y : GridFace 23 23) :
    ¬(uuDualGraph (uResidueTwoExact 7)).Adj residueTwoExactSevenCutFace y := by
  intro h
  rcases h.2 with hhorizontal | hvertical
  · obtain ⟨e, he₁, he₂, hends⟩ := hhorizontal
    rcases hends with hends | hends
    · by_cases htop : e.row.val = 0
      · simp [residueTwoExactSevenCutFace, horizontalDualEndpoints, htop] at hends
      · simp only [residueTwoExactSevenCutFace, horizontalDualEndpoints,
          dif_neg htop] at hends
        have hr := congrArg (fun f => match f with
          | .out => 0
          | .cell r _ => r.val + 1) hends.1
        have hc := congrArg (fun f => match f with
          | .out => 0
          | .cell _ c => c.val) hends.1
        simp at hr hc
        apply residueTwoExact_seven_5_13_not_mem
        have hv : (horizontalPrimalEndpoints e).1 =
            (⟨5, by omega⟩, ⟨13, by omega⟩) := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [horizontalPrimalEndpoints] <;> omega
        rwa [hv] at he₁
    · by_cases hbottom : e.row.val + 1 = 23
      · simp [residueTwoExactSevenCutFace, horizontalDualEndpoints, hbottom] at hends
      · simp only [residueTwoExactSevenCutFace, horizontalDualEndpoints,
          dif_neg hbottom] at hends
        have hr := congrArg (fun f => match f with
          | .out => 0
          | .cell r _ => r.val) hends.1
        have hc := congrArg (fun f => match f with
          | .out => 0
          | .cell _ c => c.val) hends.1
        simp at hr hc
        apply residueTwoExact_seven_4_14_not_mem
        have hv : (horizontalPrimalEndpoints e).2 =
            (⟨4, by omega⟩, ⟨14, by omega⟩) := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [horizontalPrimalEndpoints] <;> omega
        rwa [hv] at he₂
  · obtain ⟨e, he₁, he₂, hends⟩ := hvertical
    rcases hends with hends | hends
    · by_cases hleft : e.col.val = 0
      · simp [residueTwoExactSevenCutFace, verticalDualEndpoints, hleft] at hends
      · simp only [residueTwoExactSevenCutFace, verticalDualEndpoints,
          dif_neg hleft] at hends
        have hr := congrArg (fun f => match f with
          | .out => 0
          | .cell r _ => r.val) hends.1
        have hc := congrArg (fun f => match f with
          | .out => 0
          | .cell _ c => c.val + 1) hends.1
        simp at hr hc
        apply residueTwoExact_seven_4_14_not_mem
        have hv : (verticalPrimalEndpoints e).1 =
            (⟨4, by omega⟩, ⟨14, by omega⟩) := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [verticalPrimalEndpoints] <;> omega
        rwa [hv] at he₁
    · by_cases hright : e.col.val + 1 = 23
      · simp [residueTwoExactSevenCutFace, verticalDualEndpoints, hright] at hends
      · simp only [residueTwoExactSevenCutFace, verticalDualEndpoints,
          dif_neg hright] at hends
        have hr := congrArg (fun f => match f with
          | .out => 0
          | .cell r _ => r.val) hends.1
        have hc := congrArg (fun f => match f with
          | .out => 0
          | .cell _ c => c.val) hends.1
        simp at hr hc
        apply residueTwoExact_seven_5_13_not_mem
        have hv : (verticalPrimalEndpoints e).2 =
            (⟨5, by omega⟩, ⟨13, by omega⟩) := by
          apply Prod.ext <;> apply Fin.ext <;>
            simp [verticalPrimalEndpoints] <;> omega
        rwa [hv] at he₂

/-- The singleton checkerboard face is a respected, nontrivial face cut. -/
theorem uResidueTwoExact_seven_not_dual_connected :
    ¬(uuDualGraph (uResidueTwoExact 7)).Connected := by
  let S : Set (GridFace 23 23) := {residueTwoExactSevenCutFace}
  apply not_connected_of_respectsCut (S := S)
  · intro x y hxy
    constructor
    · intro hx
      simp only [S, Set.mem_singleton_iff] at hx ⊢
      subst x
      exact (residueTwoExactSevenCutFace_not_adj y hxy).elim
    · intro hy
      simp only [S, Set.mem_singleton_iff] at hy ⊢
      subst y
      exact (residueTwoExactSevenCutFace_not_adj x hxy.symm).elim
  · exact ⟨residueTwoExactSevenCutFace, Set.mem_singleton _⟩
  · exact ⟨GridFace.out, by simp [S, residueTwoExactSevenCutFace]⟩

/-- In particular, the proposed one-step geometry cannot be discharged even at
its first step. -/
theorem not_residueTwoExactStepGeometry_six :
    ¬ResidueTwoExactStepGeometry 6 := by
  intro S
  exact uResidueTwoExact_seven_not_dual_connected
    (S.connected uResidueTwoExact_six_dual_connected)

/-- Uniform local step geometry implies connectivity of every exact member. -/
theorem uResidueTwoExact_dual_connected_of_stepGeometry
    (steps : ∀ k, 6 ≤ k → ResidueTwoExactStepGeometry k) :
    ∀ k, 6 ≤ k → (uuDualGraph (uResidueTwoExact k)).Connected := by
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simpa using uResidueTwoExact_six_dual_connected
  | succ d ih =>
      rw [← Nat.add_assoc]
      exact (steps (6 + d) (by omega)).connected (ih (by omega))

/-- Connectedness of one exact member realizes its exact complement count. -/
theorem residueTwoExact_le_maxPreserved_of_dual_connected
    (k : Nat) (hk : 6 ≤ k)
    (h : (uuDualGraph (uResidueTwoExact k)).Connected) :
    3 * k ^ 2 + 7 * k ≤ maxPreserved (3 * k + 2) (3 * k + 2) := by
  rw [← uResidueTwoExact_compl_card k hk]
  exact compl_card_le_maxPreserved_of_uuDual_connected
    (by omega) (by omega) (uResidueTwoExact k) h

/-- A completed family of exact local steps discharges the remaining diagonal
construction obligation. -/
theorem remainingMatchingDiagonalConstructions_of_exactStepGeometry
    (steps : ∀ k, 6 ≤ k → ResidueTwoExactStepGeometry k) :
    RemainingMatchingDiagonalConstructions where
  residueTwoTail k hk := by
    rw [diagonalFormulaP_three_mul_add_two_ge_five k (by omega)]
    exact residueTwoExact_le_maxPreserved_of_dual_connected k (by omega)
      (uResidueTwoExact_dual_connected_of_stepGeometry steps k (by omega))

end GridGraphs
