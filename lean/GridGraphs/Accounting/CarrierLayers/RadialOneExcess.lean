import GridGraphs.Accounting.CarrierLayers.RadialNearTightExclusion

/-!
# One-excess slack and empty-block isolate charging

These are necessary conditions, not a sharp-target exclusion. In particular,
distinct empty blocks are not assumed to have distinct inward carriers.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- A one-excess configuration has exactly three units of slack above
`(r,c,b) = (k+2,1,2k+3)`. The slack variables are natural numbers. -/
theorem one_excess_exact_slack {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hcard : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    F.card = 3 * k ^ 2 + 7 * k + 1 ∧
    ∃ a d e : Nat, a + d + e = 3 ∧
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent = k + 2 + a ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent = 1 + d ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 3 + e := by
  have hf := Nat.le_antisymm
    (residueTwo_card_le_target_add_one_of_pure_carriers_le_three hk F hacyc hp) hcard
  have hr := (residueTwo_counterexample_profile (by omega) (by omega : 1 ≤ 1)
    F hacyc hcard).1
  have hb := two_mul_add_three_le_boundaryDeficiencySum_of_pure_carriers_le_three hk F hacyc hp
  have hc : 1 ≤ Fintype.card (forcedEdgeGraph
      (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).connectedComponentMk (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  have hsum : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent +
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 3 * k + 9 := by
    nlinarith
  refine ⟨hf,
    Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent - (k + 2),
    Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent - 1,
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) - (2 * k + 3), ?_⟩
  omega

/-- At least `k-q` disjoint triple blocks are empty. Their distinct middle
vertices are holes with no preserved boundary neighbors. No forest assumption
is needed for this pigeonhole statement. -/
theorem empty_block_middle_set {k : Nat} (hk : 1 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2))) (s : Fin 4) :
    ∃ S : Finset (GridVertex (3 * k + 2) (3 * k + 2)),
      k - (F.filter (OnOpenSide s)).card ≤ S.card ∧
      ∀ v ∈ S, OnOpenSide s v ∧ v ∉ F ∧
        ∀ z, (gridGraph (3 * k + 2) (3 * k + 2)).Adj v z →
          IsGridBoundary z → z ∉ F := by
  classical
  let A := F.filter (OnOpenSide s)
  let I := A.image (fun v => (sidePosition s v - 1) / 3)
  let E := range k \ I
  have hE : k - A.card ≤ E.card := by
    have hpart := card_sdiff_add_card_inter (range k) I
    have hle := card_le_card (inter_subset_right (s₁ := range k) (s₂ := I))
    have himage : I.card ≤ A.card := card_image_le
    rw [card_range] at hpart
    change E.card + (range k ∩ I).card = k at hpart
    omega
  let a : Fin (3 * k + 2) := ⟨if s.val = 0 ∨ s.val = 2 then 0 else 3 * k + 1, by
    split <;> omega⟩
  let middle : E → GridVertex (3 * k + 2) (3 * k + 2) := fun i =>
    let t : Fin (3 * k + 2) := ⟨3 * i.val + 2, by
      have hi := mem_range.mp (mem_sdiff.mp i.property).1
      omega⟩
    if s.val < 2 then (a, t) else (t, a)
  have hpos (i : E) : sidePosition s (middle i) = 3 * i.val + 2 := by
    dsimp [sidePosition, middle]
    split_ifs <;> rfl
  have hinj : Function.Injective middle := by
    intro i j he
    have h := congrArg (sidePosition s) he
    rw [hpos, hpos] at h
    exact Subtype.ext (by omega)
  let S := univ.image middle
  have hScard : S.card = E.card := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_coe]
  refine ⟨S, by change k - A.card ≤ S.card; omega, ?_⟩
  intro v hv
  obtain ⟨i, _, rfl⟩ := mem_image.mp hv
  have hi := mem_range.mp (mem_sdiff.mp i.property).1
  have hiI := (mem_sdiff.mp i.property).2
  have hhole (z : GridVertex (3 * k + 2) (3 * k + 2))
      (hz : OnOpenSide s z) (hblock : (sidePosition s z - 1) / 3 = i.val) : z ∉ F := by
    intro hzF
    exact hiI (mem_image.mpr ⟨z, mem_filter.mpr ⟨hzF, hz⟩, hblock⟩)
  have hs : OnOpenSide s (middle i) := by
    dsimp [middle, a, OnOpenSide, OnSide]
    split_ifs <;> simp <;> omega
  refine ⟨hs, hhole _ hs (by rw [hpos]; omega), ?_⟩
  intro z hadj hzb
  have hzgeom : OnOpenSide s z ∧ (sidePosition s z - 1) / 3 = i.val := by
    unfold IsGridBoundary at hzb
    fin_cases s <;>
      dsimp [middle, a, gridGraph, adjacent, OnOpenSide, OnSide, sidePosition] at hadj ⊢ <;>
      simp only [Fin.ext_iff, Fin.val_zero] at hadj <;> omega
  exact hhole z hzgeom.1 hzgeom.2

/-- If roots and pure carriers exhaust the induced component count, a side
hole with no preserved boundary neighbor is an ambient isolate. -/
theorem hole_middle_isolated_of_root_saturation {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hsat : Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent =
      (F.filter (OnOpenSide s)).card + (pureBoundaryCarriers F).card)
    (v : GridVertex n n) (hvs : OnOpenSide s v) (hv : v ∉ F)
    (hneighbors : ∀ z, (gridGraph n n).Adj v z → IsGridBoundary z → z ∉ F) :
    ∀ z, ¬ (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj v z := by
  intro w hadj
  have hw : w ∈ F := hadj.2.resolve_left hv
  have hwb : ¬ IsGridBoundary w := fun h => hneighbors w hadj.1 h hw
  let wF : (↑F : Set (GridVertex n n)) := ⟨w, hw⟩
  let D := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk wF
  have hwD : wF ∈ D.supp := by simp [D, ConnectedComponent.mem_supp_iff]
  have hD : D ∉ pureBoundaryCarriers F := fun h => hwb ((mem_filter.mp h).2 wF hwD)
  have havoid := inward_hole_carrier_avoids_roots F hacyc s v hvs hv wF hwb hadj.1
  have hbound := missing_side_roots_add_pure_add_one_le_components F hacyc s hmissing D hD havoid
  omega

/-- Distinct isolated holes give distinct ambient components, and a preserved
vertex supplies one further component that none of those holes can reuse. -/
theorem isolated_holes_card_add_one_le_components {n : Nat}
    (F S : Finset (GridVertex n n)) (hF : F.Nonempty)
    (hU : ∀ v ∈ S, v ∉ F)
    (hiso : ∀ v ∈ S, ∀ z, ¬ (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj v z) :
    S.card + 1 ≤ Fintype.card
      (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent := by
  classical
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  obtain ⟨u, hu⟩ := hF
  have huS : u ∉ S := fun h => hU u h hu
  have heq {x y : GridVertex n n} (hx : x ∈ S) (hr : H.Reachable x y) : x = y := by
    by_contra hne
    have hm : x ∈ H.support := mem_support_of_reachable hne hr
    obtain ⟨z, hz⟩ := (mem_support H).mp hm
    exact hiso x hx z hz
  let f : ↥(insert u S) → H.ConnectedComponent := fun v => H.connectedComponentMk v.val
  have hinj : Function.Injective f := by
    intro x y he
    have hr : H.Reachable x.val y.val := ConnectedComponent.exact he
    apply Subtype.ext
    rcases mem_insert.mp x.property with hx | hx
    · rcases mem_insert.mp y.property with hy | hy
      · exact hx.trans hy.symm
      · exact (heq hy hr.symm).symm
    · exact heq hx hr
  have hle := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, card_insert_of_notMem huS] using hle

/-- Safe multi-block charging: under root saturation, at least `k-q` distinct
empty-block middles are isolates, hence `c ≥ k-q+1`. -/
theorem empty_blocks_charge_ambient_components {k : Nat} (hk : 1 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2))) (hF : F.Nonempty)
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hsat : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent =
      (F.filter (OnOpenSide s)).card + (pureBoundaryCarriers F).card) :
    k - (F.filter (OnOpenSide s)).card + 1 ≤
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent := by
  obtain ⟨S, hS, hgeom⟩ := empty_block_middle_set hk F s
  have hbound := isolated_holes_card_add_one_le_components F S hF
    (fun v hv => (hgeom v hv).2.1)
    (fun v hv => hole_middle_isolated_of_root_saturation F hacyc s hmissing hsat v
      (hgeom v hv).1 (hgeom v hv).2.1 (hgeom v hv).2.2)
  omega

/-- The missing-side holes and two distinct off-side near-corner witnesses
give a root-sensitive boundary lower bound, without a tightness assumption. -/
theorem missing_side_root_boundary_budget {k : Nat} (hk : 3 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) (s : Fin 4) :
    3 * k + 2 ≤ (F.filter (OnOpenSide s)).card +
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) := by
  classical
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
  have hApart := card_sdiff_add_card_inter S F
  rw [hSF, hScard] at hApart
  have hBpart := card_sdiff_add_card_inter Q S
  rw [hQS, hQcard] at hBpart
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

/-- A compact slack profile retaining root deficit `m = k-q`. Boundary holes
give `m ≤ e+1`; carrier nonreuse gives `p ≤ a+m+2`; at saturation the
distinct empty-block isolates additionally give `m ≤ d`. -/
theorem one_excess_missing_side_slack {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hcard : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val) :
    ∃ a d e m : Nat, a + d + e = 3 ∧
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent = k + 2 + a ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent = 1 + d ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 3 + e ∧
      (F.filter (OnOpenSide s)).card + m = k ∧ m ≤ e + 1 ∧
      (pureBoundaryCarriers F).card ≤ a + m + 2 ∧
      ((pureBoundaryCarriers F).card = a + m + 2 → m ≤ d) := by
  obtain ⟨_, a, d, e, hslack, hr, hc, hb⟩ := one_excess_exact_slack hk F hacyc hp hcard
  have hq := missing_side_preserved_card_le (by omega) F hacyc s hmissing
  have hqb := missing_side_root_boundary_budget (by omega) F hacyc s
  have hqr := missing_side_roots_add_pure_le_components F hacyc s hmissing
  let m := k - (F.filter (OnOpenSide s)).card
  have hm : (F.filter (OnOpenSide s)).card + m = k := by dsimp [m]; omega
  refine ⟨a, d, e, m, hslack, hr, hc, hb, hm, by omega, by omega, ?_⟩
  intro hsaturate
  have hsat : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent =
      (F.filter (OnOpenSide s)).card + (pureBoundaryCarriers F).card := by omega
  have hF : F.Nonempty := card_pos.mp (by omega)
  have hcharge := empty_blocks_charge_ambient_components (by omega) F hF hacyc s hmissing hsat
  dsimp [m] at *
  omega

/-- At the maximal ambient count `c=4`, the one-excess slack is completely
used by ambient components. Every missing side has `k-1` roots, two off-side
near-corner holes, and an actual ambient isolate. -/
theorem one_excess_four_components_geometry {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hcard : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hc4 : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 4)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val) :
    (pureBoundaryCarriers F).card = 3 ∧
    (F.filter (OnOpenSide s)).card = k - 1 ∧
    ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card = 2 ∧
    (∀ v, BoundarySix.Corner v → v ∈ F) ∧
    (∀ v, IsGridBoundary v → ¬ OnOpenSide s v → v ∉ F → BoundarySix.Near v) ∧
    ∃ v, OnOpenSide s v ∧ v ∉ F ∧
      ∀ z, ¬ (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).Adj v z := by
  obtain ⟨_, a, d, e, hslack, hr, hc, hb⟩ := one_excess_exact_slack hk F hacyc hp hcard
  have hb0 : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 3 := by omega
  have hr0 : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 2 := by omega
  have hperim := perimeter_le_pureBoundaryCarriers_add_twice_boundaryDeficiency (by omega) F hacyc
  have hp3 : (pureBoundaryCarriers F).card = 3 := by
    by_contra hne
    have hsmall : (pureBoundaryCarriers F).card ≤ 2 := by omega
    have hmul := Nat.mul_le_mul_left (3 * k + 2) hsmall
    omega
  have hqr := missing_side_roots_add_pure_le_components F hacyc s hmissing
  have hcases := near_tight_missing_side_hole_count hk F hacyc hb0 s hmissing
  have hq : (F.filter (OnOpenSide s)).card = k - 1 := by omega
  have hsat : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent =
      (F.filter (OnOpenSide s)).card + (pureBoundaryCarriers F).card := by omega
  obtain ⟨v, hvs, hv, hn⟩ := missing_side_empty_triple_middle (by omega) F s (by omega)
  exact ⟨hp3, hq, by omega,
    (near_tight_missing_side_budget hk F hacyc hb0 s hmissing).2,
    (near_tight_offside_nonNear_holes hk F hacyc hb0 s hmissing).2 hq,
    v, hvs, hv, hole_middle_isolated_of_root_saturation F hacyc s hmissing hsat v hvs hv hn⟩

end GridGraphs.CarrierLayers
