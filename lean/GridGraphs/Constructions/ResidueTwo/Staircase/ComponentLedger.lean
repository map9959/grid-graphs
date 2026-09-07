import GridGraphs.Constructions.ResidueTwo.ResidueTwoStaircaseForest
import GridGraphs.Accounting.ComponentReduction

/-! # Concrete staircase component ledgers

The seed checks below count edges of fixed witnesses, never connected components
or configurations. Component counts follow from the proved forest property.
No recurrence or pumping invariant is asserted.
-/

namespace GridGraphs.ResidueTwoStaircase

open Finset SimpleGraph BoundaryFiveConstruction BoundaryFiveFrame

/-- A decidable coordinate presentation of the same witness. -/
def ledgerVertices (s : ℕ) : Finset (Vertex s) :=
  univ.filter fun v =>
    ((v.1.val = 0 ∨ v.1.val + 1 = 3 * s + 5 ∨
      v.2.val = 0 ∨ v.2.val + 1 = 3 * s + 5) ∧
      ¬ ((v.1.val = 0 ∧ (v.2.val = 1 ∨ v.2.val = 2)) ∨
        (v.1.val = 1 ∧ v.2.val = 3 * s + 4) ∨
        (v.1.val = 3 * s + 4 ∧ v.2.val = 3 * s + 3) ∨
        (v.1.val = 3 * s + 3 ∧ v.2.val = 0))) ∨
    (v.1.val = 2 ∧ v.2.val = 2) ∨
    (∃ j : Fin s, v.1.val = 3 * j.val + 3 ∧
      j.val + 4 ≤ v.2.val ∧ v.2.val ≤ 3 * s + 2) ∨
    (∃ j : Fin (s - 1), v.1.val = 3 * j.val + 5 ∧
      2 ≤ v.2.val ∧ v.2.val ≤ j.val + 3) ∨
    (∃ t : Fin ((s + 3) / 4), v.1.val = 3 * s + 2 ∧
      s + 2 - 4 * t.val ≤ v.2.val ∧ v.2.val ≤ s + 2 - 4 * t.val) ∨
    (∃ t : Fin ((s + 1) / 4), v.1.val = 3 * s + 1 ∧
      s - 4 * t.val ≤ v.2.val ∧ v.2.val ≤ s - 4 * t.val)

theorem Ffull_eq_ledgerVertices (s : ℕ) : Ffull (A s) = ledgerVertices s := by
  classical
  ext v
  unfold Ffull
  rw [mem_union, Set.mem_toFinset]
  simp only [Fouter, Set.mem_ofPred_eq,
    IsGridBoundary, BoundaryHole, mem_A, R, L, B, P, mem_interval,
    Prod.ext_iff, Fin.ext_iff, z, ledgerVertices, mem_filter, mem_univ, true_and]
  have h1 : 3 * s + 5 - 1 = 3 * s + 4 := by omega
  have h2 : 3 * s + 5 - 2 = 3 * s + 3 := by omega
  rw [h1, h2]

theorem index_card {s : ℕ} (hs : 2 ≤ s) :
    Fintype.card (Index s) = 2 * s + (s + 1) / 2 := by
  simp only [Index, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

/-- Only the five noncorner frame holes contribute complementary deficiency. -/
theorem Ffull_compl_boundaryDeficiency {s : ℕ} (hs : 2 ≤ s) :
    boundaryDeficiencySum (3 * s + 5) (3 * s + 5) (univ \ Ffull (A s)) = 5 := by
  classical
  let holes := ({v | BoundaryHole v} : Set (Vertex s)).toFinset
  have hsub : holes ⊆ univ \ Ffull (A s) := by
    intro v hv
    have hh : BoundaryHole v := by
      simpa only [holes, Set.mem_toFinset, Set.mem_ofPred_eq] using hv
    have ha : v ∉ A s := by
      intro ha
      have hd := A_subset_Deep hs ha
      simp only [Deep, Set.mem_ofPred_eq] at hd
      unfold BoundaryHole at hh
      omega
    simp only [mem_sdiff, mem_univ, true_and, Ffull, mem_union]
    rw [Set.mem_toFinset]
    exact not_or.mpr ⟨fun hf => hf.2 hh, ha⟩
  have hweight (v : Vertex s) (hv : v ∈ holes) :
      gridBoundaryDeficiency (3 * s + 5) (3 * s + 5) v = 1 := by
    have hh : BoundaryHole v := by
      simpa only [holes, Set.mem_toFinset, Set.mem_ofPred_eq] using hv
    rw [gridBoundaryDeficiency_eq_four_side_indicators (by omega) (by omega)]
    unfold BoundaryHole at hh
    split_ifs <;> omega
  have hzero (v : Vertex s) (hv : v ∈ univ \ Ffull (A s)) (hh : v ∉ holes) :
      gridBoundaryDeficiency (3 * s + 5) (3 * s + 5) v = 0 := by
    have hh' : ¬ BoundaryHole v := fun h => hh (Set.mem_toFinset.mpr h)
    have hn : ¬ IsGridBoundary v := by
      intro hb
      apply (mem_sdiff.mp hv).2
      unfold Ffull
      exact mem_union_left _ (Set.mem_toFinset.mpr ⟨hb, hh'⟩)
    rw [gridBoundaryDeficiency_eq_four_side_indicators (by omega) (by omega)]
    unfold IsGridBoundary at hn
    split_ifs <;> omega
  unfold boundaryDeficiencySum
  rw [← sum_subset hsub hzero, sum_congr rfl hweight]
  simpa only [sum_const, smul_eq_mul, mul_one] using holes_card (n := 3 * s + 5) (by omega)

/-- Uniform total component ledger; this does not separate the two counts. -/
theorem Ffull_component_sum {s : ℕ} (hs : 2 ≤ s) :
    Fintype.card ((gridGraph (3 * s + 5) (3 * s + 5)).induce
      (↑(Ffull (A s)) : Set (Vertex s))).ConnectedComponent +
    Fintype.card (forcedEdgeGraph (gridGraph (3 * s + 5) (3 * s + 5))
      (↑(Ffull (A s)) : Set (Vertex s))).ConnectedComponent +
    3 * ((s + 1) / 2) = 6 * s + 7 := by
  have hc := grid_component_reduction (Ffull (A s)) (Ffull_isAcyclic hs)
  have hf := Ffull_card hs
  have hb := Ffull_compl_boundaryDeficiency hs
  have hp := boundaryDeficiencySum_add_compl (3 * s + 5) (3 * s + 5) (Ffull (A s))
  have ht := total_boundaryDeficiencySum (m := 3 * s + 5) (n := 3 * s + 5)
    (by omega) (by omega)
  nlinarith

theorem seed_two_induced_edges :
    ((gridGraph 11 11).induce
      (↑(Ffull (A 2)) : Set (Vertex 2))).edgeFinset.card = 39 := by
  rw [Ffull_eq_ledgerVertices]
  decide +kernel

theorem seed_three_induced_edges :
    ((gridGraph 14 14).induce
      (↑(Ffull (A 3)) : Set (Vertex 3))).edgeFinset.card = 64 := by
  rw [Ffull_eq_ledgerVertices]
  decide +kernel

/-- Actual induced and ambient forced component counts, including ambient isolates. -/
theorem seed_two_profile :
    (Ffull (A 2)).card = 48 ∧
    Fintype.card ((gridGraph 11 11).induce
      (↑(Ffull (A 2)) : Set (Vertex 2))).ConnectedComponent = 9 ∧
    Fintype.card (forcedEdgeGraph (gridGraph 11 11)
      (↑(Ffull (A 2)) : Set (Vertex 2))).ConnectedComponent = 7 ∧
    boundaryDeficiencySum 11 11 (univ \ Ffull (A 2)) = 5 := by
  have hf := Ffull_card (s := 2) (by omega)
  have hr := induce_finset_forest_ledger (gridGraph 11 11) (Ffull (A 2))
    (Ffull_isAcyclic (s := 2) (by omega))
  have hc := grid_component_reduction (m := 11) (n := 11)
    (Ffull (A 2)) (Ffull_isAcyclic (s := 2) (by omega))
  have hb := Ffull_compl_boundaryDeficiency (s := 2) (by omega)
  change boundaryDeficiencySum 11 11 (univ \ Ffull (A 2)) = 5 at hb
  have ht := total_boundaryDeficiencySum (m := 11) (n := 11) (by omega) (by omega)
  have hp := boundaryDeficiencySum_add_compl 11 11 (Ffull (A 2))
  rw [seed_two_induced_edges] at hr
  norm_num at hf hc ht
  exact ⟨hf, by omega, by omega, hb⟩

theorem seed_three_profile :
    (Ffull (A 3)).card = 76 ∧
    Fintype.card ((gridGraph 14 14).induce
      (↑(Ffull (A 3)) : Set (Vertex 3))).ConnectedComponent = 12 ∧
    Fintype.card (forcedEdgeGraph (gridGraph 14 14)
      (↑(Ffull (A 3)) : Set (Vertex 3))).ConnectedComponent = 7 ∧
    boundaryDeficiencySum 14 14 (univ \ Ffull (A 3)) = 5 := by
  have hf := Ffull_card (s := 3) (by omega)
  have hr := induce_finset_forest_ledger (gridGraph 14 14) (Ffull (A 3))
    (Ffull_isAcyclic (s := 3) (by omega))
  have hc := grid_component_reduction (m := 14) (n := 14)
    (Ffull (A 3)) (Ffull_isAcyclic (s := 3) (by omega))
  have hb := Ffull_compl_boundaryDeficiency (s := 3) (by omega)
  change boundaryDeficiencySum 14 14 (univ \ Ffull (A 3)) = 5 at hb
  have ht := total_boundaryDeficiencySum (m := 14) (n := 14) (by omega) (by omega)
  have hp := boundaryDeficiencySum_add_compl 14 14 (Ffull (A 3))
  rw [seed_three_induced_edges] at hr
  norm_num at hf hc ht
  exact ⟨hf, by omega, by omega, hb⟩

/-- Combined induced and ambient forced component cost of the actual family. -/
noncomputable def componentCost (s : ℕ) : ℕ :=
  Fintype.card ((gridGraph (3 * s + 5) (3 * s + 5)).induce
    (↑(Ffull (A s)) : Set (Vertex s))).ConnectedComponent +
  Fintype.card (forcedEdgeGraph (gridGraph (3 * s + 5) (3 * s + 5))
    (↑(Ffull (A s)) : Set (Vertex s))).ConnectedComponent

/-- The current six-width growth spends nine component units, rather than the
six required by the stable target. This is accounting, not a new pump. -/
theorem componentCost_step_two {s : ℕ} (hs : 2 ≤ s) :
    componentCost (s + 2) = componentCost s + 9 := by
  have h := Ffull_component_sum hs
  have hnext := Ffull_component_sum (s := s + 2) (by omega)
  change componentCost s + 3 * ((s + 1) / 2) = 6 * s + 7 at h
  change componentCost (s + 2) + 3 * ((s + 2 + 1) / 2) = 6 * (s + 2) + 7 at hnext
  omega

/-- Exact score gain of the existing family when the side grows by six. -/
theorem Ffull_card_step_two {s : ℕ} (hs : 2 ≤ s) :
    (Ffull (A (s + 2))).card = (Ffull (A s)).card + 12 * s + 37 := by
  rw [Ffull_card (by omega), Ffull_card hs]
  have hdiv : (s + 2 + 1) / 2 = (s + 1) / 2 + 1 := by omega
  rw [hdiv]
  ring

end GridGraphs.ResidueTwoStaircase
