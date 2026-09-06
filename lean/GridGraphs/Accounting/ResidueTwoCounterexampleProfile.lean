import GridGraphs.Accounting.BoundaryStratifiedCarrierBound

/-!
# Necessary budgets for residue-two counterexamples

These statements restrict hypothetical counterexamples. They do not assert
that the low-budget profiles are impossible.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- Exceeding the stable target forces many carriers and a small remaining budget. -/
theorem residueTwo_counterexample_profile {k excess : Nat}
    (hk : 1 ≤ k) (hexcess : 1 ≤ excess)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hcard : 3 * k ^ 2 + 7 * k + excess ≤ F.card) :
    k + 2 ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent ∧
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) +
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent + 3 * excess ≤ 2 * k + 10 := by
  classical
  have hlength := forced_card_le_side_mul_components F hacyc
  have hcarriers : k + 2 ≤ Fintype.card
      ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).ConnectedComponent := by
    by_contra h
    have hsmall : Fintype.card
        ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).ConnectedComponent ≤
          k + 1 := by omega
    have hscaled := Nat.mul_le_mul_left (3 * k + 2) hsmall
    nlinarith
  refine ⟨hcarriers, ?_⟩
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  nlinarith

/-- A counterexample to the stable target has boundary-plus-forced-component cost at most `2k+7`. -/
theorem residueTwo_stable_counterexample_budget {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hcard : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) +
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent ≤ 2 * k + 7 := by
  have h := (residueTwo_counterexample_profile (by omega) (by omega : 1 ≤ 1)
    F hacyc hcard).2
  omega

/-- A counterexample to the early target has cost at most `2k+4`. -/
theorem residueTwo_early_counterexample_budget {k : Nat} (hk : 1 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hcard : 3 * k ^ 2 + 7 * k + 2 ≤ F.card) :
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) +
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent ≤ 2 * k + 4 := by
  have h := (residueTwo_counterexample_profile hk (by omega : 1 ≤ 2)
    F hacyc hcard).2
  omega

/-- The high-cost branch already satisfies the stable upper bound. -/
theorem residueTwo_card_le_of_large_boundary_component_budget {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hbudget : 2 * k + 8 ≤
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) +
        Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
          (↑F : Set _)).ConnectedComponent) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  by_contra h
  have hsmall := residueTwo_stable_counterexample_budget hk F hacyc (by omega)
  omega

/-- Boundary deficiency five forces an additional carrier in a stable counterexample. -/
theorem residueTwo_boundary_five_counterexample_profile {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hcard : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5) :
    k + 3 ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent ∧
    Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent ≤ 2 * k + 1 := by
  classical
  have hlength := forced_card_le_boundary_stratified_components (by omega) F hacyc hb
  have hcarriers : k + 3 ≤ Fintype.card
      ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).ConnectedComponent := by
    by_contra h
    have hsmall : Fintype.card
        ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).ConnectedComponent ≤
          k + 2 := by omega
    have hscaled := Nat.mul_le_mul_left (3 * k + 2 - 4) hsmall
    have hsub : 3 * k + 2 - 4 + 2 = 3 * k := by omega
    nlinarith
  refine ⟨hcarriers, ?_⟩
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  nlinarith

end GridGraphs
