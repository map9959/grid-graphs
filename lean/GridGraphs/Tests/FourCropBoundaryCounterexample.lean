import GridGraphs.Constructions.Finite.FiniteDiagonalTwelve
import GridGraphs.Surgery.FourCropSurgery

/-!
# A four-crop boundary-count counterexample

The complement of the certified twelve-by-twelve construction is a
forced-acyclic set whose loss at every corner crop is greater than `2n + 1`.
Thus forced-forest identities alone cannot imply that proposed bound.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The forced set complementary to the certified `finiteU12` construction. -/
def fourCropBoundaryCounterexample12 : Finset (GridVertex 12 12) :=
  (Finset.univ : Finset (GridVertex 12 12)) \ finiteU12

theorem fourCropBoundaryCounterexample12_card :
    fourCropBoundaryCounterexample12.card = 58 := by
  exact finiteU12_compl_card

theorem fourCropBoundaryCounterexample12_isAcyclic :
    (forcedEdgeGraph (gridGraph 12 12)
      (↑fourCropBoundaryCounterexample12 : Set (GridVertex 12 12))).IsAcyclic := by
  obtain ⟨T, _hTG, htree, hpreserves⟩ :=
    exists_isTree_preserving_compl_of_uuDual_connected_grid finiteU12
      finiteU12RankedDualCertificate.connected
      (gridGraph_connected (by omega) (by omega))
  apply grid_forcedEdgeGraph_isAcyclic_of_preserves htree.isAcyclic
  intro v hv
  exact hpreserves (by simpa [fourCropBoundaryCounterexample12] using hv)

theorem fourCropBoundaryCounterexample12_frameLosses :
    fourCropFrameLoss 12 .northWest (by omega) fourCropBoundaryCounterexample12 = 27 ∧
    fourCropFrameLoss 12 .northEast (by omega) fourCropBoundaryCounterexample12 = 27 ∧
    fourCropFrameLoss 12 .southWest (by omega) fourCropBoundaryCounterexample12 = 26 ∧
    fourCropFrameLoss 12 .southEast (by omega) fourCropBoundaryCounterexample12 = 26 := by
  native_decide

theorem fourCropBoundaryCounterexample12_loss_gt_two_mul_add_one
    (c : FourCropCorner) :
    2 * 12 + 1 <
      fourCropFrameLoss 12 c (by omega) fourCropBoundaryCounterexample12 := by
  fin_cases c <;> native_decide

end GridGraphs
