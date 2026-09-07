import GridGraphs.Accounting.BoundarySix.Connected.PacketSingleton

/-! # Singleton loss plus ordinary nonfull deep-carrier loss -/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

/-- At deficiency six and with four pure carriers, at most three actual full
rods fit the physical annulus bridge budget. -/
theorem boundary_six_full_rods_le_three {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (hp : 4 ≤ (pureBoundaryCarriers F).card) : (fullCarriers F).card ≤ 3 := by
  have hB := boundaryDeficiencySum_compl_eq_six_boundary_card_lower hn F hacyc hb
  have hbudget := component_budget hn F hacyc
  have hpA := pure_add_shallow_le_annulus_components (by omega) F
  have hbridge := fullCarriers_card_add_one_le_components (by omega) F hacyc
  omega

/-- The singleton loses `N-1`, and every other nonfull deep carrier loses
one more. With at most three full rods this gives `D >= N+d-5`. -/
theorem singleton_deep_mass_bound {n : Nat} (hn : 10 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (hp : 4 ≤ (pureBoundaryCarriers F).card)
    (hzero : (nextRingCarriers F).card = 0)
    (Z : Carrier F) (hZ : Z ∉ pureBoundaryCarriers F) (hsize : Z.supp.toFinset.card = 1) :
    (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card +
      (deepCarriers F).card + (n - 4) ≤ (n - 4) * (deepCarriers F).card + 5 := by
  let R := deepCarriers F
  let W := F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)
  have hZR : Z ∈ R := by simp [R, deepCarriers, card_eq_zero.mp hzero, hZ]
  have hcover : R.biUnion (deepVertices F) = W := by
    ext v
    constructor
    · intro hv
      obtain ⟨C, _, hvC⟩ := mem_biUnion.mp hv
      obtain ⟨hvF, _, ha⟩ := (mem_deepVertices (by omega) F C v).mp hvC
      rw [mem_iff_layers (by omega)] at ha
      exact mem_filter.mpr ⟨hvF, not_or.mp ha⟩
    · intro hv
      obtain ⟨hvF, hvb, hvr⟩ := mem_filter.mp hv
      let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk ⟨v, hvF⟩
      have hvC : v ∈ deepVertices F C := (mem_deepVertices (by omega) F C v).mpr
        ⟨hvF, by simp [C, ConnectedComponent.mem_supp_iff],
          fun ha => ((mem_iff_layers (by omega) v).mp ha).elim hvb hvr⟩
      exact mem_biUnion.mpr ⟨C, deepCarrier_of_mem_deepVertices (by omega) F C hvC, hvC⟩
  have hW : W.card ≤ ∑ C ∈ R, (deepVertices F C).card := by rw [← hcover]; exact card_biUnion_le
  have hcap (C : Carrier F) : (deepVertices F C).card ≤ n - 4 := by
    rw [deepVertices_card]
    exact deep_carrier_part_card_le (by omega) F hacyc C
  have hZsmall : (deepVertices F Z).card ≤ 1 := by
    rw [deepVertices_card, ← hsize]
    exact card_filter_le _ _
  have hlocal (C : Carrier F) : (deepVertices F C).card + 1 + (if C = Z then n - 6 else 0) ≤
      (n - 4) + (if C ∈ fullCarriers F then 1 else 0) := by
    by_cases he : C = Z
    · subst C
      simp only [ite_true]
      omega
    · rw [if_neg he, Nat.add_zero]
      have hc := hcap C
      by_cases hf : C ∈ fullCarriers F
      · rw [if_pos hf]
        omega
      · rw [if_neg hf]
        have hne : (deepVertices F C).card ≠ n - 4 := by
          simpa only [fullCarriers, mem_filter, mem_univ, true_and] using hf
        omega
  have hsum := sum_le_sum (s := R) (fun C _ => hlocal C)
  have hfilter : R.filter (fun C => C ∈ fullCarriers F) = fullCarriers F := by
    ext C
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨fullCarriers_subset_deepCarriers (by omega) F h, h⟩⟩
  simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one, sum_boole,
    Nat.cast_id, sum_ite_eq', if_pos hZR, hfilter] at hsum
  rw [Nat.mul_comm R.card (n - 4)] at hsum
  have hM := boundary_six_full_rods_le_three (by omega) F hacyc hb hp
  change W.card + R.card + (n - 4) ≤ (n - 4) * R.card + 5
  omega

private theorem empty_ring_card_partition {n : Nat} (F : Finset (GridVertex n n))
    (hEmpty : F.filter IsNextRing = ∅) :
    F.card = (F.filter IsGridBoundary).card +
      (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card := by
  have hpart := card_filter_add_card_filter_not (s := F) IsGridBoundary
  have he : F.filter (fun v => ¬ IsGridBoundary v) =
      F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v) := by
    ext v
    simp only [mem_filter]
    constructor
    · intro hv
      refine ⟨hv.1, hv.2, ?_⟩
      intro hr
      have hm := mem_filter.mpr ⟨hv.1, hr⟩
      rw [hEmpty] at hm
      exact notMem_empty _ hm
    · exact fun h => ⟨h.1, h.2.1⟩
  rw [he] at hpart
  exact hpart.symm

/-- At the current endpoint, the actual singleton and all nonfull losses
already contradict the preserved-cardinality requirement. -/
theorem current_endpoint_singleton_false {k : Nat} (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6)
    (Z : Carrier F) (hZ : Z ∉ pureBoundaryCarriers F) (hsize : Z.supp.toFinset.card = 1) : False := by
  obtain ⟨hEmpty, hcorners⟩ := current_endpoint_empty_ring_and_preserved_corners hk hmod F hacyc hf hb
  obtain ⟨_, _, hprofiles⟩ := current_upper_endpoint_profiles hk hmod F hacyc hf
  have hr : Fintype.card (Carrier F) = k + 4 := by
    change Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 4
    omega
  obtain ⟨hp, hzero, hd⟩ := endpoint_carrier_partition hk hmod F hacyc hf hr
  have hmass := singleton_deep_mass_bound (by omega) F hacyc hb hp.ge hzero Z hZ hsize
  rw [hd] at hmass
  have hholes := (two_perimeter_holes (by omega) F hacyc hb hp hEmpty hcorners).2
  have hper := perimeter_holes_card (by omega) F hacyc hEmpty
  have hB : (F.filter IsGridBoundary).card + 10 = 4 * (3 * k + 2) := by omega
  have hpart := empty_ring_card_partition F hEmpty
  have hN : 3 * k + 2 - 4 + 2 = 3 * k := by omega
  have he : 5 ≤ (2 * k + 1) / 3 := by omega
  nlinarith

end GridGraphs.BoundarySix.Connected
