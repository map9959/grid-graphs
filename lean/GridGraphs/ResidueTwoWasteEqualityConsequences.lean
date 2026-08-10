import GridGraphs.ResidueTwoWasteEqualityBasic

/-!
# Unconditional consequences of residue-two waste equality

All results in this file are implications from an equality for one specified
spanning subtree.  No universal waste bound is used.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- Complete arithmetic and component profile forced by `W = n + 2` in the
residue-two family. -/
theorem residueTwo_wasteEquality_profile
    (k : Nat) (hk : 1 ≤ k)
    (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (heq : incidenceWaste
      (gridGraph (3 * k + 2) (3 * k + 2) \ T) = (3 * k + 2) + 2) :
    numPreserved (3 * k + 2) (3 * k + 2) T = 3 * k ^ 2 + 7 * k + 2 ∧
    (residueTwoCotreeSupport T).card = 6 * k ^ 2 + 5 * k + 2 ∧
    incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) % 3 = 1 ∧
    residueTwoAttachmentCharge (residueTwoCotreeSupport T) = 3 * k + 6 ∧
    fourSideComponentRank (3 * k + 2) (residueTwoCotreeSupport T) = 3 * k + 6 := by
  have hw := grid_cotree_incidenceWaste_identity (by omega) (by omega) hT
  have hD := D_expand (m := 3 * k + 2) (n := 3 * k + 2)
    (by omega) (by omega)
  have hsupport := grid_cotree_support_card_add_numPreserved hT.le
  have hcharge := residueTwoAttachmentCharge_eq_waste_add_two (by omega) hT
  have hrank := fourSideComponentRank_eq_residueTwoAttachmentCharge
    (by omega) (residueTwoCotreeSupport T)
  have hsquare : (3 * k + 2) * (3 * k + 2) =
      9 * k ^ 2 + 12 * k + 4 := by ring
  change (residueTwoCotreeSupport T).card +
      numPreserved (3 * k + 2) (3 * k + 2) T =
        (3 * k + 2) * (3 * k + 2) at hsupport
  rw [hsquare] at hw hD hsupport
  have hp : numPreserved (3 * k + 2) (3 * k + 2) T =
      3 * k ^ 2 + 7 * k + 2 := by omega
  have hu : (residueTwoCotreeSupport T).card =
      6 * k ^ 2 + 5 * k + 2 := by omega
  refine ⟨hp, hu, ?_⟩
  constructor
  · omega
  constructor <;> omega

/-- Equality fixes the total of all row occupancies. -/
theorem residueTwo_wasteEquality_row_identity
    (k : Nat) (hk : 1 ≤ k)
    (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (heq : incidenceWaste
      (gridGraph (3 * k + 2) (3 * k + 2) \ T) = (3 * k + 2) + 2) :
    ∑ r : Fin (3 * k + 2),
      residueTwoRowOccupancy (residueTwoCotreeSupport T) r =
        6 * k ^ 2 + 5 * k + 2 := by
  rw [sum_residueTwoRowOccupancy]
  exact (residueTwo_wasteEquality_profile k hk T hT heq).2.1

/-- Equality fixes the analogous total of column occupancies. -/
theorem residueTwo_wasteEquality_column_identity
    (k : Nat) (hk : 1 ≤ k)
    (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (heq : incidenceWaste
      (gridGraph (3 * k + 2) (3 * k + 2) \ T) = (3 * k + 2) + 2) :
    ∑ c : Fin (3 * k + 2),
      residueTwoColumnOccupancy (residueTwoCotreeSupport T) c =
        6 * k ^ 2 + 5 * k + 2 := by
  rw [sum_residueTwoColumnOccupancy]
  exact (residueTwo_wasteEquality_profile k hk T hT heq).2.1

/-- Equality leaves the forced graph on full vertices acyclic. -/
theorem residueTwo_wasteEquality_forced_acyclic
    (k : Nat)
    (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T) :
    (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑(residueTwoFullSet T) : Set (GridVertex (3 * k + 2) (3 * k + 2)))).IsAcyclic := by
  simpa only [residueTwoFullSet, residueTwoCotreeSupport] using
    grid_tree_complement_forcedEdgeGraph_isAcyclic hT

/-- Every cell has a cotree-support edge.  This is the local boundary
attachment condition available without any global waste inequality. -/
theorem residueTwo_wasteEquality_cell_attachment
    (k : Nat)
    (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (r c : Fin (3 * k + 2 - 1)) :
    let U := residueTwoCotreeSupport T
    (cell00 r c ∈ U ∧ cell01 r c ∈ U) ∨
      (cell01 r c ∈ U ∧ cell11 r c ∈ U) ∨
      (cell11 r c ∈ U ∧ cell10 r c ∈ U) ∨
      (cell10 r c ∈ U ∧ cell00 r c ∈ U) := by
  simpa only [residueTwoCotreeSupport] using
    grid_tree_cotree_support_hits_cell_edge hT r c

end GridGraphs
