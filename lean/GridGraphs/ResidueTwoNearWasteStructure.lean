import GridGraphs.LinearWaste

/-!
# Structural consequences of residue-two near waste

This file contains only unconditional consequences of the hypothetical equality
`W = n + 5` for `n = 3k + 2`.  In particular, it does not import any finite
search certificate.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- The part of a grid finset in row `r`. -/
def gridRow {m n : Nat} (U : Finset (GridVertex m n)) (r : Fin m) :
    Finset (GridVertex m n) :=
  U.filter fun v => v.1 = r

/-- The incidence waste contributed by one row of a graph. -/
def incidenceWasteRow {m n : Nat} (G : SimpleGraph (GridVertex m n))
    [DecidableRel G.Adj] (r : Fin m) : Nat :=
  ∑ v ∈ gridRow (supportFinset G) r, (3 - G.degree v)

/-- Exact row partition of an arbitrary grid finset. -/
theorem sum_gridRow_card {m n : Nat} (U : Finset (GridVertex m n)) :
    ∑ r : Fin m, (gridRow U r).card = U.card := by
  classical
  simp only [gridRow, Finset.card_filter]
  rw [Finset.sum_comm]
  simp

/-- Incidence waste is exactly the sum of its row contributions. -/
theorem sum_incidenceWasteRow {m n : Nat}
    (G : SimpleGraph (GridVertex m n)) [DecidableRel G.Adj] :
    ∑ r : Fin m, incidenceWasteRow G r = incidenceWaste G := by
  classical
  unfold incidenceWasteRow incidenceWaste gridRow
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- Near waste fixes the cotree-support cardinality at the old residue-two
baseline exactly. -/
theorem residueTwo_nearWaste_support_card {k : Nat}
    {T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2))}
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree
      (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (hnear : incidenceWaste
      (gridGraph (3 * k + 2) (3 * k + 2) \ T) = (3 * k + 2) + 5) :
    (supportFinset
      (gridGraph (3 * k + 2) (3 * k + 2) \ T)).card =
        6 * k ^ 2 + 5 * k + 3 := by
  have hledger := incidenceWaste_add_degreeSum
    (gridGraph (3 * k + 2) (3 * k + 2) \ T)
    (grid_cotree_degree_le_three (by omega) (by omega) hT)
  rw [sum_grid_cotree_degrees_support hT, hnear] at hledger
  have hD := D_expand (m := 3 * k + 2) (n := 3 * k + 2)
    (by omega) (by omega)
  have hsquare : (3 * k + 2) * (3 * k + 2) =
      9 * k ^ 2 + 12 * k + 4 := by ring
  rw [hsquare] at hD
  omega

/-- Row form of the exact support-cardinality consequence. -/
theorem residueTwo_nearWaste_row_support_identity {k : Nat}
    {T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2))}
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree
      (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (hnear : incidenceWaste
      (gridGraph (3 * k + 2) (3 * k + 2) \ T) = (3 * k + 2) + 5) :
    ∑ r : Fin (3 * k + 2),
        (gridRow
          (supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T)) r).card =
      6 * k ^ 2 + 5 * k + 3 := by
  rw [sum_gridRow_card]
  exact residueTwo_nearWaste_support_card hT hnear

/-- Row form of the hypothetical near-waste equality itself. -/
theorem residueTwo_nearWaste_row_waste_identity {k : Nat}
    {T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2))}
    [DecidableRel T.Adj]
    (_hT : IsSpanningSubtree
      (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (hnear : incidenceWaste
      (gridGraph (3 * k + 2) (3 * k + 2) \ T) = (3 * k + 2) + 5) :
    ∑ r : Fin (3 * k + 2),
        incidenceWasteRow (gridGraph (3 * k + 2) (3 * k + 2) \ T) r =
      3 * k + 7 := by
  rw [sum_incidenceWasteRow, hnear]

/-- The exact component charge forced by `W = n + 5`. -/
theorem residueTwo_nearWaste_component_identity {k : Nat}
    {T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2))}
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree
      (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (hnear : incidenceWaste
      (gridGraph (3 * k + 2) (3 * k + 2) \ T) = (3 * k + 2) + 5) :
    let U := supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T)
    let F := (Finset.univ :
      Finset (GridVertex (3 * k + 2) (3 * k + 2))) \ U
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2) U +
        Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
          (↑F : Set (GridVertex (3 * k + 2) (3 * k + 2)))).ConnectedComponent +
        Fintype.card (forcedEdgeGraph
          (gridGraph (3 * k + 2) (3 * k + 2))
          (↑F : Set (GridVertex (3 * k + 2) (3 * k + 2)))).ConnectedComponent =
      3 * k + 9 := by
  dsimp only
  have hbridge := square_grid_tree_component_bridge (n := 3 * k + 2)
    (by omega) hT
  dsimp only at hbridge
  rw [hnear] at hbridge
  omega

/-- Four-side form of the exact component identity. -/
theorem residueTwo_nearWaste_fourSide_identity {k : Nat}
    {T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2))}
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree
      (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (hnear : incidenceWaste
      (gridGraph (3 * k + 2) (3 * k + 2) \ T) = (3 * k + 2) + 5) :
    fourSideComponentRank (3 * k + 2)
      (supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T)) =
        3 * k + 9 := by
  let U := supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T)
  have hcomponents := residueTwo_nearWaste_component_identity hT hnear
  dsimp only at hcomponents
  rw [fourSideComponentRank_eq_component_charge (by omega) U]
  exact hcomponents

end GridGraphs
