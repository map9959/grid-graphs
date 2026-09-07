import GridGraphs.Accounting.BoundarySix.Connected.DeepRootedEndpoint

/-! # A missing outer corner also gives a connected annulus

At deficiency six a missing corner leaves exactly five actual boundary holes
and an empty next ring. The missing outer-corner correction in the cubic
annulus ledger then forces annulus connectivity when four pure carriers exist.
-/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

/-- The weighted corner correction leaves annulus mass `4n-9` and only one
forced annulus component. Neither is supplied as a certificate hypothesis. -/
theorem missing_corner_annulus_tree {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (hp : 4 ≤ (pureBoundaryCarriers F).card)
    {z : GridVertex n n} (hz : Corner z) (hzF : z ∉ F) :
    (selected F).card + 9 = 4 * n ∧
      Fintype.card (forcedEdgeGraph (graph n) (↑(selected F) : Set _)).ConnectedComponent = 1 := by
  have hweight (v : GridVertex n n) : gridBoundaryDeficiency n n v =
      (if IsGridBoundary v then 1 else 0) + (if Corner v then 1 else 0) := by
    rw [gridBoundaryDeficiency_eq_four_side_indicators (by omega) (by omega)]
    unfold IsGridBoundary Corner
    split_ifs <;> omega
  have hsum := sum_congr (s₁ := univ \ F) rfl (fun v _ => hweight v)
  have hweighted : boundaryDeficiencySum n n (univ \ F) =
      ((univ \ F).filter IsGridBoundary).card + ((univ \ F).filter Corner).card := by
    simpa only [boundaryDeficiencySum, sum_add_distrib, sum_boole, Nat.cast_id] using hsum
  have hcorner : 1 ≤ ((univ \ F).filter Corner).card :=
    card_pos.mpr ⟨z, mem_filter.mpr ⟨by simp [hzF], hz⟩⟩
  have hbalance := boundaryDeficiencySum_compl_eq_six_compl_boundary_balance hn F hacyc hb
  have hholes : ((univ \ F).filter IsGridBoundary).card = 5 := by omega
  have hring : (F.filter IsNextRing).card = 0 := by omega
  have hpartition : F.filter IsGridBoundary ∪ (univ \ F).filter IsGridBoundary =
      ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset := by
    ext v
    by_cases hv : v ∈ F <;> simp [hv]
  have hdisj : Disjoint (F.filter IsGridBoundary) ((univ \ F).filter IsGridBoundary) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp (mem_filter.mp hw).1).2 (mem_filter.mp hv).1
  have htotal := congrArg Finset.card hpartition
  rw [card_union_of_disjoint hdisj, BoundaryFiveConstruction.boundary_card (by omega)] at htotal
  have hlayers := selected_card_layers (by omega) F
  have hMass : (selected F).card + 9 = 4 * n := by omega
  have hzA : Mem z := (mem_iff_layers (by omega) z).mpr (Or.inl (by
    unfold IsGridBoundary Corner at *
    omega))
  let w : Vertex n := ⟨z, hzA⟩
  have hwC : OuterCorner w.1 := hz
  have hwS : w ∉ selected F := by simp [selected, w, hzF]
  have hwfilter : w ∉ (selected F).filter (fun v => OuterCorner v.1) := by
    intro h
    exact hwS (mem_filter.mp h).1
  have houter := outerCorner_card_le_four (insert w (selected F))
  rw [filter_insert, if_pos hwC, card_insert_of_notMem hwfilter] at houter
  have hcubic := cubic_ledger (by omega) (selected F) (selected_isAcyclic F hacyc)
  have hsize := card_vertex (by omega : 5 ≤ n)
  have hpA := pure_add_shallow_le_annulus_components (by omega) F
  have hbridge := fullCarriers_card_add_one_le_components (by omega) F hacyc
  exact ⟨hMass, by omega⟩

/-- The current boundary-six endpoint cannot have a missing outer corner. -/
theorem current_endpoint_missing_corner_false {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6)
    {z : GridVertex (3 * k + 2) (3 * k + 2)} (hz : Corner z) (hzF : z ∉ F) : False := by
  have he : 2 ≤ (2 * k + 1) / 3 := by omega
  obtain ⟨_, _, _, hp⟩ := residueTwo_four_distinct_pure_carriers_of_two_excess
    hk F hacyc (by omega)
  obtain ⟨hMass, hcA⟩ := missing_corner_annulus_tree (by omega) F hacyc hb hp hz hzF
  exact connected_annulus_current_endpoint_false hk hmod F hacyc hf hb hcA hMass

/-- The only remaining current boundary-six endpoint geometry has an empty
next ring and all four outer corners preserved. -/
theorem current_endpoint_empty_ring_and_preserved_corners {k : Nat}
    (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6) :
    F.filter IsNextRing = ∅ ∧ ∀ z, Corner z → z ∈ F := by
  refine ⟨current_endpoint_nextRing_empty hk hmod F hacyc hf hb, ?_⟩
  intro z hz
  by_contra hzF
  exact current_endpoint_missing_corner_false hk hmod F hacyc hf hb hz hzF

end GridGraphs.BoundarySix.Connected
