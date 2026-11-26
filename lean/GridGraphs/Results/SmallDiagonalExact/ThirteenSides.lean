import GridGraphs.Accounting.CarrierLayers.RadialSide

/-! On an open side with no pure carrier, radial spacing permits at most
four of its eleven sites. Two additional corner witnesses are off that side. -/
namespace GridGraphs.Thirteen
open Finset SimpleGraph CarrierLayers
attribute [local instance] Classical.propDecidable

private theorem missing_side
    (F : Finset (GridVertex 13 13))
    (hacyc : (forcedEdgeGraph (gridGraph 13 13)
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) : (F.filter (OnOpenSide s)).card ≤ 4 := by
  classical
  let S := F.filter (OnOpenSide s)
  have hneighbor (u : S) : ∃ w : GridVertex 13 13,
      w ∈ F ∧ IsNextRing w ∧ (gridGraph 13 13).Adj u.val w := by
    let v : (↑F : Set _) := ⟨u.val, (mem_filter.mp u.property).1⟩
    let C := ((gridGraph 13 13).induce
      (↑F : Set _)).connectedComponentMk v
    have hv : v ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
    have hC : C ∉ pureBoundaryCarriers F := fun h =>
      hmissing C h v hv (mem_filter.mp u.property).2
    obtain ⟨w, _, hwr, hadj⟩ := boundary_nonpure_carrier_nextRing_neighbor
      (by omega) F hacyc C hC hv (openSide_boundary (mem_filter.mp u.property).2)
    exact ⟨w.val, w.property, hwr, hadj⟩
  have hspace (u v : S) (hlt : sidePosition s u.val < sidePosition s v.val) :
      sidePosition s u.val + 3 ≤ sidePosition s v.val := by
    obtain ⟨w, hw, hwr, huw⟩ := hneighbor u
    obtain ⟨z, hz, hzr, hvz⟩ := hneighbor v
    exact radial_pair_spacing (by omega) F hacyc s
      (mem_filter.mp u.property).1 (mem_filter.mp v.property).1 hw hz
      (mem_filter.mp u.property).2 (mem_filter.mp v.property).2 hwr hzr huw hvz hlt
  let f : S → Fin 4 := fun u => ⟨(sidePosition s u.val - 1) / 3, by
    have h := sidePosition_bounds (mem_filter.mp u.property).2
    omega⟩
  have hinj : Function.Injective f := by
    intro u v he
    have he' := congrArg Fin.val he
    dsimp [f] at he'
    have hu := sidePosition_bounds (mem_filter.mp u.property).2
    have hv := sidePosition_bounds (mem_filter.mp v.property).2
    apply Subtype.ext
    apply sidePosition_injective (mem_filter.mp u.property).2 (mem_filter.mp v.property).2
    rcases lt_trichotomy (sidePosition s u.val) (sidePosition s v.val) with h | h | h
    · have h' := hspace u v h
      omega
    · exact h
    · have h' := hspace v u h
      omega
  simpa only [Fintype.card_coe, Fintype.card_fin, S] using
    Fintype.card_le_of_injective f hinj

theorem nine_le_cost_of_missing_carrier
    (F : Finset (GridVertex 13 13))
    (hacyc : (forcedEdgeGraph (gridGraph 13 13)
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3) :
    9 ≤ boundaryDeficiencySum 13 13 (univ \ F) := by
  classical
  obtain ⟨s, hs⟩ := exists_side_without_pure_carrier (by omega) F hacyc hp
  have hpacking := missing_side F hacyc s hs
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := BoundarySix.corner_witnesses (by omega) F hacyc
  have hnear := near_openSide_card_le_two (by omega) Q hQnear s
  let S := univ.filter (OnOpenSide (n := 13) s)
  have hScard : S.card = 11 := by
    exact openSide_card (by decide : 2 ≤ 13) s
  have hSF : S ∩ F = F.filter (OnOpenSide s) := by
    ext v
    simp only [S, mem_inter, mem_filter, mem_univ, true_and]
    exact and_comm
  have hQS : Q ∩ S = Q.filter (OnOpenSide s) := by
    ext v
    simp [S]
  have hA : 7 ≤ (S \ F).card := by
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
      boundaryDeficiencySum 13 13 (univ \ F) := by
    calc
      _ = ∑ _v ∈ (S \ F) ∪ (Q \ S), 1 := by simp
      _ ≤ ∑ v ∈ (S \ F) ∪ (Q \ S),
          gridBoundaryDeficiency 13 13 v :=
        sum_le_sum (fun v hv => one_le_gridBoundaryDeficiency_of_boundary
          (by omega) (by omega) v (hboundary v hv))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (by simp)
  rw [card_union_of_disjoint hdisjoint] at hsum
  omega

end GridGraphs.Thirteen
