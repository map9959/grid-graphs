import GridGraphs.Accounting.CheckerboardComponent
import GridGraphs.Accounting.UniversalWasteBoundReduction

/-!
# Checkerboard reduction of the universal waste bound

This module restates the open linear waste inequality using the two ambient
checkerboard forests.  The formulation is subtraction-free: every vertex not
present in a star forest contributes one isolated-component credit.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- Sum of the component counts of the black-center and white-center forced
forests associated to the complement of `U`. -/
def checkerboardComponentCount (n : Nat)
    (U : Finset (GridVertex n n)) : Nat :=
  let F := (Finset.univ : Finset (GridVertex n n)) \ U
  Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑(blackCenters F) : Set (GridVertex n n))).ConnectedComponent +
    Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑(whiteCenters F) : Set (GridVertex n n))).ConnectedComponent

/-- The ambient checkerboard count is `|U|` plus the component charge appearing
in `fourSideComponentRank`. -/
theorem checkerboardComponentCount_eq_component_charge_add_support
    {n : Nat} (U : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n)
      (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
        Set (GridVertex n n))).IsAcyclic) :
    checkerboardComponentCount n U =
      U.card +
        Fintype.card ((gridGraph n n).induce
          (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
            Set (GridVertex n n))).ConnectedComponent +
        Fintype.card (forcedEdgeGraph (gridGraph n n)
          (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
            Set (GridVertex n n))).ConnectedComponent := by
  let F := (Finset.univ : Finset (GridVertex n n)) \ U
  have h := checkerboard_component_sum_eq_component_charge_add_compl F hacyc
  change checkerboardComponentCount n U = _
  rw [checkerboardComponentCount]
  change Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑(blackCenters F) : Set (GridVertex n n))).ConnectedComponent +
    Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑(whiteCenters F) : Set (GridVertex n n))).ConnectedComponent = _
  rw [h]
  simp [F]

/-- Subtraction-free checkerboard form of the geometric target.  The left side
is full-boundary charge plus the isolated-component normalization; the right
side is the free three-side allowance plus both checkerboard component counts.
-/
def CheckerboardBoundaryBound (n : Nat)
    (U : Finset (GridVertex n n)) : Prop :=
  let F := (Finset.univ : Finset (GridVertex n n)) \ U
  boundaryDeficiencySum n n F + U.card + 4 ≤
    3 * n + checkerboardComponentCount n U

/-- After applying the two exact color ledgers, all boundary terms cancel: the
checkerboard boundary bound is precisely the sharp forced-cardinality bound. -/
theorem checkerboardBoundaryBound_iff_forced_card
    {n : Nat} (U : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n)
      (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
        Set (GridVertex n n))).IsAcyclic) :
    CheckerboardBoundaryBound n U ↔
      3 * ((Finset.univ : Finset (GridVertex n n)) \ U).card + 4 ≤
        n * n + 3 * n := by
  let F := (Finset.univ : Finset (GridVertex n n)) \ U
  have hchecker := grid_checkerboard_ambient_component_reduction F hacyc
  have hcard := card_compl_add_card_grid n n U
  change 4 * F.card +
      Fintype.card (forcedEdgeGraph (gridGraph n n)
        (↑(blackCenters F) : Set (GridVertex n n))).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (gridGraph n n)
        (↑(whiteCenters F) : Set (GridVertex n n))).ConnectedComponent =
    2 * (n * n) + boundaryDeficiencySum n n F at hchecker
  change F.card + U.card = n * n at hcard
  unfold CheckerboardBoundaryBound checkerboardComponentCount
  change boundaryDeficiencySum n n F + U.card + 4 ≤
      3 * n +
        (Fintype.card (forcedEdgeGraph (gridGraph n n)
          (↑(blackCenters F) : Set (GridVertex n n))).ConnectedComponent +
        Fintype.card (forcedEdgeGraph (gridGraph n n)
          (↑(whiteCenters F) : Set (GridVertex n n))).ConnectedComponent) ↔
      3 * F.card + 4 ≤ n * n + 3 * n
  omega

/-- The checkerboard boundary bound is exactly the missing linear four-side
rank inequality. -/
theorem checkerboardBoundaryBound_iff_fourSideComponentRank
    {n : Nat} (hn : 2 ≤ n) (U : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n)
      (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
        Set (GridVertex n n))).IsAcyclic) :
    CheckerboardBoundaryBound n U ↔ n + 4 ≤ fourSideComponentRank n U := by
  have hcount := checkerboardComponentCount_eq_component_charge_add_support U hacyc
  have hrank := fourSideComponentRank_eq_component_charge hn U
  have hboundary := boundaryDeficiencySum_add_compl n n U
  have htotal := total_boundaryDeficiencySum hn hn
  unfold CheckerboardBoundaryBound
  change boundaryDeficiencySum n n
      ((Finset.univ : Finset (GridVertex n n)) \ U) + U.card + 4 ≤
      3 * n + checkerboardComponentCount n U ↔ _
  change fourSideComponentRank n U = _ at hrank
  omega

/-- For a square-grid spanning tree, the universal waste theorem is equivalent
to the checkerboard boundary bound. -/
theorem square_grid_tree_universalWaste_iff_checkerboardBoundaryBound
    {n : Nat} (hn : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) ↔
      CheckerboardBoundaryBound n
        (supportFinset (gridGraph n n \ T)) := by
  let U := supportFinset (gridGraph n n \ T)
  have hacyc : (forcedEdgeGraph (gridGraph n n)
      (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
        Set (GridVertex n n))).IsAcyclic := by
    simpa only [U] using grid_tree_complement_forcedEdgeGraph_isAcyclic hT
  rw [square_grid_tree_universalWaste_iff_fourSideComponentRank hn hT]
  exact (checkerboardBoundaryBound_iff_fourSideComponentRank
    (by omega) U hacyc).symm

end GridGraphs
