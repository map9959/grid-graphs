import GridGraphs.Core.Defs
import GridGraphs.Core.Bounds
import GridGraphs.Constructions.ResidueOne.ResidueOne
import GridGraphs.Geometry.GridDual
import GridGraphs.Accounting.CotreeWaste
import GridGraphs.Forests.MarkedCycleFirstStop
import GridGraphs.Accounting.BoundaryFiveBudget
import GridGraphs.Accounting.BoundaryFiveEquality
import GridGraphs.Constructions.BoundaryFive.BoundaryFiveConstruction
import GridGraphs.Constructions.ResidueTwo.ResidueTwoStaircaseForest
import GridGraphs.Accounting.CarrierLengthBound
import GridGraphs.Accounting.BoundaryStratifiedCarrierBound
import GridGraphs.Accounting.ResidueTwoCounterexampleProfile
import GridGraphs.Geometry.CarrierPacking
import GridGraphs.Results.SmallDiagonalExact.Seven
import GridGraphs.Results.SmallDiagonalExact.Ten

/-!
# Decidable sanity tests linking Lean definitions to Rust DP ground truth

This file is a small regression suite consisting of `example`s that the
kernel checks via `decide` (or `rfl`/`Finset.card` evaluation). It pins the
Lean definitions of `D`, `basicUB`, `refinedUB`, `lowerB`, the vertex-class
counts, and the residue-1 cardinality to specific small-grid values that
match the Rust DP empirical data in `lean/results-empirical.csv`.

A regression in any of the bound expressions or vertex counts will break
these `example`s and therefore break `lake build`.
-/

namespace GridGraphs

/-! ## Unconditional carrier-length upper bounds -/

example (k : Nat) (hk : 3 ≤ k) :
    3 * k ^ 2 + 6 * k + 2 + k / 2 ≤ maxPreserved (3 * k + 2) (3 * k + 2) ∧
      maxPreserved (3 * k + 2) (3 * k + 2) ≤
        3 * k ^ 2 + 7 * k + (2 * k + 3) / 3 := by
  exact ⟨ResidueTwoStaircase.residueTwo_le_maxPreserved hk,
    maxPreserved_residueTwo_le_boundary_stratified (by omega)⟩

example : maxPreserved 7 7 = 22 := maxPreserved_seven_seven

example : maxPreserved 10 10 = 42 := maxPreserved_ten_ten

example : 194 ≤ maxPreserved 23 23 ∧ maxPreserved 23 23 ≤ 201 := by
  constructor
  · simpa using ResidueTwoStaircase.residueTwo_le_maxPreserved (k := 7) (by omega)
  · simpa using maxPreserved_le_boundary_stratified_carrier_bound (n := 23) (by omega)

example : 246 ≤ maxPreserved 26 26 ∧ maxPreserved 26 26 ≤ 254 := by
  constructor
  · simpa using ResidueTwoStaircase.residueTwo_le_maxPreserved (k := 8) (by omega)
  · simpa using maxPreserved_le_boundary_stratified_carrier_bound (n := 26) (by omega)

example : maxPreserved 14 14 ≤ 79 := by
  simpa using maxPreserved_le_boundary_stratified_carrier_bound (n := 14) (by omega)

example (F : Finset (GridVertex 23 23))
    (hacyc : (forcedEdgeGraph (gridGraph 23 23) (↑F : Set _)).IsAcyclic)
    (hcard : 197 ≤ F.card) :
    boundaryDeficiencySum 23 23 (Finset.univ \ F) +
      Fintype.card (forcedEdgeGraph (gridGraph 23 23) (↑F : Set _)).ConnectedComponent ≤ 21 := by
  exact residueTwo_stable_counterexample_budget (k := 7) (by omega)
    F hacyc (by simpa using hcard)

example (F : Set (GridVertex 3 2))
    (hacyc : (forcedEdgeGraph (gridGraph 3 2) F).IsAcyclic)
    (h00 : (0, 0) ∈ F) (h01 : (0, 1) ∈ F)
    (h20 : (2, 0) ∈ F) (h21 : (2, 1) ∈ F) : False := by
  apply forced_rectangle_two_rows_false (m := 3) (n := 2) (0 : Fin 1) (0 : Fin 1) hacyc
  · simpa using h00
  · simpa using h01
  · simpa using h20
  · simpa using h21

example : 254 < refinedUB 26 26 := by norm_num [refinedUB]

/-! ## Improved arbitrary-width residue-two construction -/

example : 246 ≤ maxPreserved 26 26 := by
  simpa using ResidueTwoStaircase.residueTwo_le_maxPreserved (k := 8) (by omega)

example (k : ℕ) (hk : 8 ≤ k) :
    3 * k ^ 2 + 6 * k + 5 < 3 * k ^ 2 + 6 * k + 2 + k / 2 := by
  omega

/-! ## Concrete boundary-five frame (symbolic checks, no search) -/

example : (BoundaryFiveFrame.Houter 7).IsAcyclic :=
  BoundaryFiveFrame.Houter_isAcyclic (by omega)

example : ((BoundaryFiveFrame.Houter 7).induce
    (BoundaryFiveFrame.Houter 7).support).IsTree :=
  BoundaryFiveFrame.support_isTree (by omega)

example : (BoundaryFiveConstruction.Ffull
    (∅ : Finset (GridVertex 7 7))).card = 19 := by
  have h := BoundaryFiveConstruction.Ffull_card (n := 7) (by omega)
    (A := ∅) (by simp)
  simpa using h

/-! ## Residue-two target component obstructions (no grid enumeration) -/

example (F : Finset (GridVertex 8 8))
    (hacyc : (forcedEdgeGraph (gridGraph 8 8) (↑F : Set _)).IsAcyclic)
    (hbudget : boundaryDeficiencySum 8 8 (Finset.univ \ F) = 5) :
    ∃ e : Sym2 (GridVertex 8 8),
      (∃ u v, e = Sym2.mk u v ∧ IsPerimeterEdge 8 u v ∧ u ∉ F ∧ v ∉ F) ∧
      ∀ x y, IsPerimeterEdge 8 x y → x ∉ F → y ∉ F → Sym2.mk x y = e := by
  exact boundaryDeficiencySum_compl_eq_five_unique_perimeter_edge (by omega) F hacyc hbudget

example (F : Finset (GridVertex 7 7))
    (hacyc : (forcedEdgeGraph (gridGraph 7 7) (↑F : Set _)).IsAcyclic)
    (hbudget : boundaryDeficiencySum 7 7 (Finset.univ \ F) = 5)
    (j : Fin 7) (hjlo : 1 ≤ j.val) (hjhi : j.val ≤ 5) :
    ((1 : Fin 7), j) ∉ F := by
  exact boundaryDeficiencySum_compl_eq_five_next_ring_notMem (by omega) F hacyc
    hbudget ((1 : Fin 7), j) (by norm_num) (by norm_num) hjlo hjhi (Or.inl rfl)

example (F : Finset (GridVertex 23 23)) (hcard : F.card = 196)
    (hr : 28 ≤ Fintype.card ((gridGraph 23 23).induce
      (↑F : Set _)).ConnectedComponent) :
    ¬(forcedEdgeGraph (gridGraph 23 23) (↑F : Set _)).IsAcyclic := by
  exact not_feasible_target_of_four_mul_le_components (k := 7) (by omega)
    F (by simpa using hcard) (by simpa using hr)

example (F : Finset (GridVertex 20 20)) (hcard : F.card = 150)
    (hr : 25 ≤ Fintype.card ((gridGraph 20 20).induce
      (↑F : Set _)).ConnectedComponent) :
    ¬(forcedEdgeGraph (gridGraph 20 20) (↑F : Set _)).IsAcyclic := by
  exact not_feasible_target_of_four_mul_add_one_le_components (k := 6) (by omega)
    F (by simpa using hcard) (by simpa using hr)

/-! ## Marked-cycle merger accounting with a shared suffix -/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

private noncomputable def sharedSuffixFirstStop :
    MarkedCycleFirstStop (Fin 4) where
  f := finRotate 4
  stop := {3}
  starts := {0, 1}
  stop_nonempty := by simp
  eventually_stop := by
    intro x
    fin_cases x
    · exact ⟨3, by decide⟩
    · exact ⟨2, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩

private noncomputable def markedDirectStartFirstStop :
    MarkedCycleFirstStop (Fin 4) where
  f := finRotate 4
  stop := {3}
  starts := {0, 3}
  stop_nonempty := by simp
  eventually_stop := by
    intro x
    fin_cases x
    · exact ⟨3, by decide⟩
    · exact ⟨2, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩

private noncomputable def sharedSuffixMerger : sharedSuffixFirstStop.MergerState := by
  let x := sharedSuffixFirstStop.stateOfStart ⟨1, by decide⟩
  refine ⟨x, ⟨by decide, ?_⟩⟩
  refine ⟨sharedSuffixFirstStop.stateOfStart ⟨0, by decide⟩, ?_⟩
  simp only [MarkedCycleFirstStop.statePredecessors, Finset.mem_filter,
    Finset.mem_univ, true_and]
  unfold MarkedCycleFirstStop.stateParent
  rw [dif_neg]
  · congr 2
  · decide

private noncomputable def markedDirectStartPredecessor :
    markedDirectStartFirstStop.State := by
  refine ⟨2, 0, by decide, 2, ?_, by decide⟩
  have hpos : 0 < markedDirectStartFirstStop.distance 0 :=
    Nat.pos_of_ne_zero fun h => by
      have := (markedDirectStartFirstStop.distance_eq_zero_iff 0).mp h
      change (0 : Fin 4) ∈ ({3} : Finset (Fin 4)) at this
      exact (by decide : (0 : Fin 4) ∉ ({3} : Finset (Fin 4))) this
  have hneOne : markedDirectStartFirstStop.distance 0 ≠ 1 := by
    intro h
    have hstop := markedDirectStartFirstStop.distance_spec 0
    rw [h] at hstop
    change (1 : Fin 4) ∈ ({3} : Finset (Fin 4)) at hstop
    exact (by decide : (1 : Fin 4) ∉ ({3} : Finset (Fin 4))) hstop
  omega

private noncomputable def markedDirectStartMerger :
    markedDirectStartFirstStop.MergerState := by
  let x := markedDirectStartFirstStop.stateOfStart ⟨3, by decide⟩
  refine ⟨x, ⟨by decide, ?_⟩⟩
  refine ⟨markedDirectStartPredecessor, ?_⟩
  simp only [MarkedCycleFirstStop.statePredecessors, Finset.mem_filter,
    Finset.mem_univ, true_and]
  unfold MarkedCycleFirstStop.stateParent
  rw [dif_neg]
  · congr 2
  · decide

-- The two starts overlap from state 1 onward rather than tracing disjoint paths.
example :
    ((sharedSuffixFirstStop.f : Fin 4 → Fin 4)^[1]) 0 = 1 ∧
      ((sharedSuffixFirstStop.f : Fin 4 → Fin 4)^[2]) 0 =
        ((sharedSuffixFirstStop.f : Fin 4 → Fin 4)^[1]) 1 := by
  decide

example : sharedSuffixFirstStop.forest.leaves = sharedSuffixFirstStop.demands :=
  sharedSuffixFirstStop.leaves_eq_demands

-- Entering the second start adds it to the provenance carried from the first.
example :
    sharedSuffixFirstStop.origins
        (sharedSuffixFirstStop.stateOfStart ⟨1, by decide⟩) =
      insert (⟨1, by decide⟩ : ↥sharedSuffixFirstStop.starts)
        (sharedSuffixFirstStop.origins
          (sharedSuffixFirstStop.stateOfStart ⟨0, by decide⟩)) := by
  apply sharedSuffixFirstStop.origins_stateParent_eq_insert
  · unfold MarkedCycleFirstStop.stateParent
    rw [dif_neg]
    · congr 2
    · decide

example :
    Fintype.card sharedSuffixFirstStop.forest.MergerSlot =
      sharedSuffixFirstStop.starts.card - sharedSuffixFirstStop.exits.card :=
  sharedSuffixFirstStop.card_mergerSlot_eq_card_starts_sub_card_exits

example :
    Fintype.card sharedSuffixFirstStop.forest.MergerSlot ≤
      (sharedSuffixFirstStop.starts \ sharedSuffixFirstStop.stop).card :=
  sharedSuffixFirstStop.card_mergerSlot_le_card_starts_sdiff_stop

noncomputable example :
    sharedSuffixFirstStop.forest.MergerSlot ↪
      ↥(sharedSuffixFirstStop.starts \ sharedSuffixFirstStop.stop) :=
  sharedSuffixFirstStop.mergerSlotUnmarkedStartEmbedding

-- Without a marked direct start, the unmarked merger owns its own start.
example : (sharedSuffixFirstStop.mergerOwner sharedSuffixMerger).1 = 1 :=
  sharedSuffixFirstStop.mergerOwner_eq_self_of_not_mem_stop
    sharedSuffixMerger (by decide)

-- With a marked direct start, the endpoint merger owns the earliest start in
-- the predecessor interval rather than the marked start itself.
example : (markedDirectStartFirstStop.mergerOwner markedDirectStartMerger).1 = 0 := by
  rw [markedDirectStartFirstStop.mergerOwner_eq_earliest_of_mem_stop
    markedDirectStartMerger (by decide)]
  let e := markedDirectStartFirstStop.earliestOriginStart
    (markedDirectStartFirstStop.mergerPredecessor markedDirectStartMerger)
  have heStart : e.1 ∈ markedDirectStartFirstStop.starts := e.2
  have heNot : e.1 ∉ markedDirectStartFirstStop.stop :=
    markedDirectStartFirstStop.earliestOriginStart_not_mem_stop_of_parent_marked
      (markedDirectStartFirstStop.stateParent_mergerPredecessor markedDirectStartMerger)
      (by decide)
  change e.1 = 0
  rcases e with ⟨ev, hev⟩
  fin_cases ev <;> simp_all [markedDirectStartFirstStop]

noncomputable example :
    sharedSuffixFirstStop.forest.MergerSlot ↪
      ↥(sharedSuffixFirstStop.starts \ sharedSuffixFirstStop.stop) :=
  sharedSuffixFirstStop.canonicalMergerSlotUnmarkedStartEmbedding

noncomputable example :
    markedDirectStartFirstStop.forest.MergerSlot ↪
      ↥(markedDirectStartFirstStop.starts \ markedDirectStartFirstStop.stop) :=
  markedDirectStartFirstStop.canonicalMergerSlotUnmarkedStartEmbedding

end

/-! ## Planar-dual coordinate spot checks -/

example : horizontalDualEndpoints (m := 3) (n := 3) ⟨0, 0⟩ =
    (GridFace.out, GridFace.cell 0 0) := by
  decide

example : verticalDualEndpoints (m := 3) (n := 3) ⟨1, 2⟩ =
    (GridFace.cell 1 1, GridFace.out) := by
  decide

example : (uuDualGraph ({(0, 0), (0, 1)} : Finset (GridVertex 2 2))).Adj
    GridFace.out (GridFace.cell 0 0) := by
  decide

/-! ## Incidence-waste accounting spot checks -/

example : incidenceWaste (⊥ : SimpleGraph (Fin 3)) = 0 := by
  decide

example : (supportFinset (⊥ : SimpleGraph (Fin 3))).card = 0 := by
  decide

/-! ## Vertex-class partition spot checks (matching `verts_partition`) -/

example : numCorners 5 5 + numBorderNonCorner 5 5 + numInterior 5 5 = 5 * 5 := by
  decide

example : numCorners 1 1 + numBorderNonCorner 1 1 + numInterior 1 1 = 1 := by
  decide

example : numCorners 3 4 + numBorderNonCorner 3 4 + numInterior 3 4 = 12 := by
  decide

example : numCorners 7 1 + numBorderNonCorner 7 1 + numInterior 7 1 = 7 := by
  decide

/-! ## Total deficiency `D m n = 2 (m-1)(n-1)` -/

example : D 1 1 = 0 := by decide
example : D 4 5 = 24 := by decide
example : D 10 10 = 162 := by decide
example : D 3 3 = 8 := by decide

/-! ## Basic upper bound -/

example : basicUB 1 10 = 10 := by decide
example : basicUB 4 1 = 4 := by decide
example : basicUB 3 3 = 6 := by decide
example : basicUB 4 5 = 12 := by decide
example : basicUB 4 10 = 22 := by decide
example : basicUB 5 5 = 14 := by decide
example : basicUB 10 10 = 46 := by decide

/-! ## Refined upper bound -/

example : refinedUB 1 10 = 10 := by decide
example : refinedUB 4 1 = 4 := by decide
example : refinedUB 3 3 = 5 := by decide
example : refinedUB 4 5 = 11 := by decide
example : refinedUB 4 10 = 21 := by decide
example : refinedUB 5 5 = 13 := by decide
example : refinedUB 10 10 = 46 := by decide

/-! ## Conservative operational lower bound `m + n − 2` -/

example : lowerB 5 5 = 8 := by decide
example : lowerB 4 10 = 12 := by decide
example : lowerB 10 10 = 18 := by decide
example : lowerB 2 2 = 2 := by decide

/-! ## Residue-1 diagonal `U` cardinalities -/

-- For k = 1 (n = 4): |uResidueOne 1| = 6 + 1 + 1 = 8.
example : (uResidueOne 1).card = 8 := by
  rw [uResidueOne_card 1 (by decide)]; decide

-- For k = 2 (n = 7): |uResidueOne 2| = 24 + 2 + 1 = 27.
example : (uResidueOne 2).card = 27 := by
  rw [uResidueOne_card 2 (by decide)]; decide

-- For k = 3 (n = 10): |uResidueOne 3| = 54 + 3 + 1 = 58.
example : (uResidueOne 3).card = 58 := by
  rw [uResidueOne_card 3 (by decide)]; decide

-- The conjectured `q (3k+1)` matches the empirical residue-1 sequence
-- 8, 27, 58, 101, ... = `q 4, q 7, q 10, q 13, ...`.
example : q 4 = 8 := by decide
example : q 7 = 27 := by decide
example : q 10 = 58 := by decide
example : q 13 = 101 := by decide
example : q 14 = 119 := by decide
example : q 17 = 179 := by decide

end GridGraphs
