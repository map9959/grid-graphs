import GridGraphs.DiagonalUpperResidue
import GridGraphs.LinearWaste

/-!
# Basic objects for residue-two waste equality

This module only introduces notation and proves bookkeeping identities.  In
particular, it does not assume a lower bound for incidence waste.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- Cotree support of a spanning subtree. -/
def residueTwoCotreeSupport {n : Nat}
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj] :
    Finset (GridVertex n n) :=
  supportFinset (gridGraph n n \ T)

/-- Vertices at which a spanning subtree preserves every grid edge. -/
def residueTwoFullSet {n : Nat}
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj] :
    Finset (GridVertex n n) :=
  (Finset.univ : Finset (GridVertex n n)) \ residueTwoCotreeSupport T

/-- Boundary incidence plus the component counts of the two complementary
forests.  Corners contribute twice through `boundaryDeficiencySum`. -/
def residueTwoAttachmentCharge {n : Nat}
    (U : Finset (GridVertex n n)) : Nat :=
  let F := (Finset.univ : Finset (GridVertex n n)) \ U
  boundaryDeficiencySum n n U +
    Fintype.card ((gridGraph n n).induce
      (↑F : Set (GridVertex n n))).ConnectedComponent +
    Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set (GridVertex n n))).ConnectedComponent

/-- Number of selected vertices in a fixed row. -/
def residueTwoRowOccupancy {n : Nat} (U : Finset (GridVertex n n))
    (r : Fin n) : Nat :=
  (U.filter fun v => v.1 = r).card

/-- Number of selected vertices in a fixed column. -/
def residueTwoColumnOccupancy {n : Nat} (U : Finset (GridVertex n n))
    (c : Fin n) : Nat :=
  (U.filter fun v => v.2 = c).card

/-- The row occupancies count every selected grid vertex exactly once. -/
theorem sum_residueTwoRowOccupancy {n : Nat}
    (U : Finset (GridVertex n n)) :
    ∑ r : Fin n, residueTwoRowOccupancy U r = U.card := by
  classical
  simp only [residueTwoRowOccupancy, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- The column counterpart of `sum_residueTwoRowOccupancy`. -/
theorem sum_residueTwoColumnOccupancy {n : Nat}
    (U : Finset (GridVertex n n)) :
    ∑ c : Fin n, residueTwoColumnOccupancy U c = U.card := by
  classical
  simp only [residueTwoColumnOccupancy, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- The attachment charge is exactly cotree waste plus two. -/
theorem residueTwoAttachmentCharge_eq_waste_add_two {n : Nat}
    (hn : 2 ≤ n) {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    residueTwoAttachmentCharge (residueTwoCotreeSupport T) =
      incidenceWaste (gridGraph n n \ T) + 2 := by
  simpa only [residueTwoAttachmentCharge, residueTwoCotreeSupport] using
    square_grid_tree_component_bridge hn hT

/-- The four side/run-boundary presentation of the same attachment charge. -/
theorem fourSideComponentRank_eq_residueTwoAttachmentCharge {n : Nat}
    (hn : 2 ≤ n) (U : Finset (GridVertex n n)) :
    fourSideComponentRank n U = residueTwoAttachmentCharge U := by
  simpa only [residueTwoAttachmentCharge] using
    fourSideComponentRank_eq_component_charge hn U

end GridGraphs
