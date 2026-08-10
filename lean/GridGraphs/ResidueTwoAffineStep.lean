import GridGraphs.ResidueTwoAffine
import GridGraphs.ConnectivityTransport
import GridGraphs.FiniteDiagonalSeventeen

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
      simpa [Nat.add_assoc] using
        (steps (5 + d) (by omega)).connected (ih (by omega))

end GridGraphs
