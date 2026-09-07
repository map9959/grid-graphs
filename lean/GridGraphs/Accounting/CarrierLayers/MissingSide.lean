import GridGraphs.Accounting.CarrierLayers.RadialTightExclusion

/-!
# Missing-side bounds independent of pure carrier count

The counts below are the existing boundary deficiency and the connected-component
counts of the preserved and forced graphs. No maximality is assumed. The unique
two-excess profile is necessary, not an assertion of existence or impossibility.
-/

namespace GridGraphs

open Finset SimpleGraph CarrierLayers

/-- A missing open side supplies `2k` holes and at least two off-side witnesses,
regardless of the number of pure boundary carriers. -/
theorem two_mul_add_two_le_boundaryDeficiencySum_of_missing_side
    {k : Nat} (hk : 3 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hmissing : ∃ s : Fin 4, ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    2 * k + 2 ≤ boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) := by
  classical
  obtain ⟨s, hs⟩ := hmissing
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

/-- Tight-endpoint exclusion strengthens the bound for every missing-side
configuration, including those with four or more pure carriers. -/
theorem two_mul_add_three_le_boundaryDeficiencySum_of_missing_side
    {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hmissing : ∃ s : Fin 4, ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    2 * k + 3 ≤ boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) := by
  have hlower := two_mul_add_two_le_boundaryDeficiencySum_of_missing_side
    (by omega) F hacyc hmissing
  obtain ⟨s, hs⟩ := hmissing
  have hne := tight_missing_side_false hk F hacyc
  by_contra h
  exact hne (by omega) s hs

/-- The near-sharp upper bound needs a missing side, not `p ≤ 3`. -/
theorem residueTwo_card_le_target_add_two_of_missing_side
    {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hmissing : ∃ s : Fin 4, ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    F.card ≤ 3 * k ^ 2 + 7 * k + 2 := by
  have hb := two_mul_add_three_le_boundaryDeficiencySum_of_missing_side hk F hacyc hmissing
  by_contra h
  have hbudget := (residueTwo_counterexample_profile (by omega) (by omega : 1 ≤ 3)
    F hacyc (by omega)).2
  omega

/-- Every missing-side two-excess configuration has the same physical profile
`(r,c,b) = (k+2,1,2k+3)`, with no restriction on pure carrier count. -/
theorem residueTwo_two_excess_missing_side_profile_unique
    {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hmissing : ∃ s : Fin 4, ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val)
    (hcard : 3 * k ^ 2 + 7 * k + 2 ≤ F.card) :
    F.card = 3 * k ^ 2 + 7 * k + 2 ∧
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent = k + 2 ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent = 1 ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 3 := by
  classical
  have hcardEq := Nat.le_antisymm
    (residueTwo_card_le_target_add_two_of_missing_side hk F hacyc hmissing) hcard
  have hb := two_mul_add_three_le_boundaryDeficiencySum_of_missing_side hk F hacyc hmissing
  obtain ⟨hr, hbudget⟩ := residueTwo_counterexample_profile (by omega)
    (by omega : 1 ≤ 2) F hacyc hcard
  have hc : 1 ≤ Fintype.card (forcedEdgeGraph
      (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).connectedComponentMk (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  refine ⟨hcardEq, ?_, by omega, by omega⟩
  nlinarith

/-- Covering all open sides requires four distinct physical pure carriers,
not just a numerical lower bound on their total count. -/
theorem distinct_pure_carriers_of_all_open_sides_covered
    {n : Nat} (hn : 3 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hcovered : ∀ s : Fin 4, ∃ C ∈ pureBoundaryCarriers F, ∃ v ∈ C.supp,
      OnOpenSide s v.val) :
    ∃ f : Fin 4 → pureBoundaryCarriers F, Function.Injective f ∧
      (∀ s, ∃ v ∈ (f s).val.supp, OnOpenSide s v.val) ∧
      4 ≤ (pureBoundaryCarriers F).card := by
  classical
  choose C hC v hv hs using hcovered
  let f : Fin 4 → pureBoundaryCarriers F := fun s => ⟨C s, hC s⟩
  have hinj : Function.Injective f := by
    intro s t he
    have heC : C s = C t := congrArg Subtype.val he
    obtain ⟨a, ha⟩ := pure_carrier_on_side hn F hacyc (C t) (hC t)
    have hsa := openSide_unique (hs s) (ha (v s) (heC ▸ hv s))
    have hta := openSide_unique (hs t) (ha (v t) (hv t))
    exact hsa.trans hta.symm
  refine ⟨f, hinj, fun s => ⟨v s, hv s, hs s⟩, ?_⟩
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- Low boundary cost, three excess vertices, or a two-excess configuration
outside the unique missing-side profile forces every open side to be covered. -/
theorem all_open_sides_covered_of_missing_side_obstruction
    {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hobstruction :
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) ≤ 2 * k + 2 ∨
      3 * k ^ 2 + 7 * k + 3 ≤ F.card ∨
      (3 * k ^ 2 + 7 * k + 2 ≤ F.card ∧
        (Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
          (↑F : Set _)).ConnectedComponent ≠ k + 2 ∨
         Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
          (↑F : Set _)).ConnectedComponent ≠ 1 ∨
         boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) ≠ 2 * k + 3))) :
    ∀ s : Fin 4, ∃ C ∈ pureBoundaryCarriers F, ∃ v ∈ C.supp,
      OnOpenSide s v.val := by
  classical
  intro s
  by_contra h
  have hmissing : ∃ s : Fin 4, ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val := by
    refine ⟨s, ?_⟩
    intro C hC v hv hs
    exact h ⟨C, hC, v, hv, hs⟩
  rcases hobstruction with hb | hf | ⟨hf, hprofile⟩
  · have hlower := two_mul_add_three_le_boundaryDeficiencySum_of_missing_side hk F hacyc hmissing
    omega
  · have hupper := residueTwo_card_le_target_add_two_of_missing_side hk F hacyc hmissing
    omega
  · have hunique := residueTwo_two_excess_missing_side_profile_unique hk F hacyc hmissing hf
    rcases hprofile with hr | hc | hb
    · exact hr hunique.2.1
    · exact hc hunique.2.2.1
    · exact hb hunique.2.2.2

end GridGraphs
