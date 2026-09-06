import GridGraphs.Results.DiagonalUpperResidue
import GridGraphs.Accounting.LinearWaste

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

/-- For a residue-two spanning tree, tight waste is exactly the corresponding
cotree-support cardinality profile. -/
theorem residueTwo_support_card_eq_tight_iff_waste_eq
    (k : Nat)
    (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T) :
    (residueTwoCotreeSupport T).card = 6 * k ^ 2 + 5 * k + 2 ↔
      incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) =
        (3 * k + 2) + 2 := by
  have hledger := incidenceWaste_add_degreeSum
    (gridGraph (3 * k + 2) (3 * k + 2) \ T)
    (grid_cotree_degree_le_three (by omega) (by omega) hT)
  rw [sum_grid_cotree_degrees_support hT] at hledger
  have hD := D_expand (m := 3 * k + 2) (n := 3 * k + 2)
    (by omega) (by omega)
  have hsquare : (3 * k + 2) * (3 * k + 2) =
      9 * k ^ 2 + 12 * k + 4 := by ring
  rw [hsquare] at hD
  change incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) +
      D (3 * k + 2) (3 * k + 2) =
        3 * (residueTwoCotreeSupport T).card at hledger
  constructor
  · intro h
    rw [h] at hledger
    omega
  · intro h
    rw [h] at hledger
    omega

/-- Near-tight stable waste is exactly the old-baseline support cardinality. -/
theorem residueTwo_support_card_eq_near_iff_waste_eq
    (k : Nat)
    (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T) :
    (residueTwoCotreeSupport T).card = 6 * k ^ 2 + 5 * k + 3 ↔
      incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) =
        (3 * k + 2) + 5 := by
  have hledger := incidenceWaste_add_degreeSum
    (gridGraph (3 * k + 2) (3 * k + 2) \ T)
    (grid_cotree_degree_le_three (by omega) (by omega) hT)
  rw [sum_grid_cotree_degrees_support hT] at hledger
  have hD := D_expand (m := 3 * k + 2) (n := 3 * k + 2)
    (by omega) (by omega)
  have hsquare : (3 * k + 2) * (3 * k + 2) =
      9 * k ^ 2 + 12 * k + 4 := by ring
  rw [hsquare] at hD
  change incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) +
      D (3 * k + 2) (3 * k + 2) =
        3 * (residueTwoCotreeSupport T).card at hledger
  constructor
  · intro h
    rw [h] at hledger
    omega
  · intro h
    rw [h] at hledger
    omega

/-- The tight exclusion is exactly nonexistence of its spanning-tree support
profile. -/
theorem residueTwoExactWasteExcluded_iff_no_tight_support_profile :
    ResidueTwoExactWasteExcluded ↔
      ∀ (k : Nat), 1 ≤ k →
        ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
          [DecidableRel T.Adj],
          IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
          (residueTwoCotreeSupport T).card ≠ 6 * k ^ 2 + 5 * k + 2 := by
  constructor
  · intro hexcluded k hk T _ hT hcard
    exact hexcluded k hk T hT
      ((residueTwo_support_card_eq_tight_iff_waste_eq k T hT).mp hcard)
  · intro hprofile k hk T _ hT hwaste
    exact hprofile k hk T hT
      ((residueTwo_support_card_eq_tight_iff_waste_eq k T hT).mpr hwaste)

/-- The stable near-tight exclusion is exactly nonexistence of its
spanning-tree support profile. -/
theorem stableResidueTwoNearWasteExcluded_iff_no_near_support_profile :
    StableResidueTwoNearWasteExcluded ↔
      ∀ (k : Nat), 5 ≤ k →
        ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
          [DecidableRel T.Adj],
          IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
          (residueTwoCotreeSupport T).card ≠ 6 * k ^ 2 + 5 * k + 3 := by
  constructor
  · intro hexcluded k hk T _ hT hcard
    exact hexcluded k hk T hT
      ((residueTwo_support_card_eq_near_iff_waste_eq k T hT).mp hcard)
  · intro hprofile k hk T _ hT hwaste
    exact hprofile k hk T hT
      ((residueTwo_support_card_eq_near_iff_waste_eq k T hT).mpr hwaste)

end GridGraphs
