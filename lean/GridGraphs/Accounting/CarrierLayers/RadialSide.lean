import GridGraphs.Accounting.CarrierLayers.RadialSideCounting
import GridGraphs.Accounting.ResidueTwoCounterexampleProfile

/-!
# The global at-most-three-pure-carriers branch

A missing pure-carrier side has at least `2k` holes. Two additional corner
witnesses lie outside that open side, giving boundary cost at least `2k + 2`.
This proves the near-sharp upper bound only in the `p ≤ 3` branch.
-/

namespace GridGraphs

open Finset SimpleGraph CarrierLayers

/-- At most three pure boundary carriers force `2k + 2` boundary-deficiency
units, with no maximality or optimizer assumptions. -/
theorem two_mul_add_two_le_boundaryDeficiencySum_of_pure_carriers_le_three
    {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3) :
    2 * k + 2 ≤ boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) := by
  classical
  obtain ⟨s, hs⟩ := exists_side_without_pure_carrier (by omega) F hacyc hp
  have hpacking := missing_side_preserved_card_le (by omega) F hacyc s hs
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := BoundarySix.corner_witnesses (by omega) F hacyc
  have hnear := near_openSide_card_le_two (by omega) Q hQnear s
  let S := univ.filter (OnOpenSide (n := 3 * k + 2) s)
  have hScard : S.card = 3 * k := by
    simpa only [Nat.add_sub_cancel] using openSide_card (by omega : 2 ≤ 3 * k + 2) s
  have hSF : S ∩ F = F.filter (OnOpenSide s) := by
    ext v
    simp only [S, mem_inter, mem_filter, mem_univ, true_and]
    exact and_comm
  have hQS : Q ∩ S = Q.filter (OnOpenSide s) := by
    ext v
    simp [S]
  have hA : 2 * k ≤ (S \ F).card := by
    have h := card_sdiff_add_card_inter S F
    rw [hSF] at h
    omega
  have hB : 2 ≤ (Q \ S).card := by
    have h := card_sdiff_add_card_inter Q S
    rw [hQS] at h
    omega
  have hdisjoint : Disjoint (S \ F) (Q \ S) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_sdiff.mp hv).1
  have hsub : (S \ F) ∪ (Q \ S) ⊆ univ \ F := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hv).2⟩
    · exact hQU (mem_sdiff.mp hv).1
  have hboundary : ∀ v ∈ (S \ F) ∪ (Q \ S), IsGridBoundary v := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact openSide_boundary (mem_filter.mp (mem_sdiff.mp hv).1).2
    · have h := hQnear v (mem_sdiff.mp hv).1
      unfold BoundarySix.Near IsGridBoundary at *
      omega
  have hsum : ((S \ F) ∪ (Q \ S)).card ≤
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) := by
    calc
      _ = ∑ _v ∈ (S \ F) ∪ (Q \ S), 1 := by simp
      _ ≤ ∑ v ∈ (S \ F) ∪ (Q \ S),
          gridBoundaryDeficiency (3 * k + 2) (3 * k + 2) v :=
        sum_le_sum (fun v hv => one_le_gridBoundaryDeficiency_of_boundary
          (by omega) (by omega) v (hboundary v hv))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (by simp)
  rw [card_union_of_disjoint hdisjoint] at hsum
  omega

/-- The global `p ≤ 3` branch satisfies `|F| ≤ T(k) + 2`. -/
theorem residueTwo_card_le_target_add_two_of_pure_carriers_le_three
    {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3) :
    F.card ≤ 3 * k ^ 2 + 7 * k + 2 := by
  classical
  have hb := two_mul_add_two_le_boundaryDeficiencySum_of_pure_carriers_le_three
    hk F hacyc hp
  have hc : 1 ≤ Fintype.card (forcedEdgeGraph
      (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).connectedComponentMk (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  by_contra h
  have hprofile := (residueTwo_counterexample_profile (by omega) (by omega : 1 ≤ 3)
    F hacyc (by omega)).2
  omega

/-- A hypothetical excess in the `p ≤ 3` branch has at most five forced
components and between `k + 2` and `k + 6` preserved carriers. -/
theorem residueTwo_counterexample_profile_of_pure_carriers_le_three
    {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hcard : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent ≤ 5 ∧
    k + 2 ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent ∧
    Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent ≤ k + 6 := by
  classical
  have hb := two_mul_add_two_le_boundaryDeficiencySum_of_pure_carriers_le_three
    hk F hacyc hp
  obtain ⟨hr, hbudget⟩ := residueTwo_counterexample_profile (by omega)
    (by omega : 1 ≤ 1) F hacyc hcard
  refine ⟨by omega, hr, ?_⟩
  have hc : 1 ≤ Fintype.card (forcedEdgeGraph
      (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).connectedComponentMk (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  nlinarith

end GridGraphs
