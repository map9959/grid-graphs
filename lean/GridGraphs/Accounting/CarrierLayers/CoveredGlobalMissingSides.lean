import GridGraphs.Accounting.CarrierLayers.GapGlobalMinimal

/-!
# Global coverage in stable counterexamples

Distinct missing open sides supply disjoint physical holes. Their combined
deficiency exceeds the stable counterexample budget. Covered sides require
distinct actual pure carriers, including at the stable endpoint k = 5.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Two missing open sides contribute disjoint sets of at least `2k` holes
each. Corners are excluded, so adjacent sides do not reuse any vertex. -/
theorem four_mul_le_boundaryDeficiency_of_two_missing_sides {k : Nat} (hk : 1 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s t : Fin 4) (hst : s ≠ t)
    (hs : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (ht : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide t v.val) :
    4 * k ≤ boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) := by
  classical
  let U (a : Fin 4) := (univ \ F).filter (OnOpenSide a)
  have holes (a : Fin 4)
      (ha : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide a v.val) :
      2 * k ≤ (U a).card := by
    have hq := missing_side_preserved_card_le hk F hacyc a ha
    let S := univ.filter (OnOpenSide (n := 3 * k + 2) a)
    have hScard : S.card = 3 * k := by
      simpa only [Nat.add_sub_cancel] using
        openSide_card (by omega : 2 ≤ 3 * k + 2) a
    have hSF : S ∩ F = F.filter (OnOpenSide a) := by
      ext v
      simp [S, and_comm]
    have hSU : S \ F = U a := by
      ext v
      simp only [S, U, mem_sdiff, mem_filter, mem_univ, true_and]
      exact and_comm
    have hpart := card_sdiff_add_card_inter S F
    rw [hScard, hSF, hSU] at hpart
    omega
  have hd : Disjoint (U s) (U t) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact hst (openSide_unique (mem_filter.mp hv).2 (mem_filter.mp hw).2.1)
  have hsub : U s ∪ U t ⊆ univ \ F := by
    intro v hv
    rcases mem_union.mp hv with hv | hv <;> exact (mem_filter.mp hv).1
  have hboundary : ∀ v ∈ U s ∪ U t, IsGridBoundary v := by
    intro v hv
    rcases mem_union.mp hv with hv | hv <;>
      exact openSide_boundary (mem_filter.mp hv).2
  have hsum : (U s ∪ U t).card ≤
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) := by
    calc
      _ = ∑ _v ∈ U s ∪ U t, 1 := by simp
      _ ≤ ∑ v ∈ U s ∪ U t,
          gridBoundaryDeficiency (3 * k + 2) (3 * k + 2) v :=
        sum_le_sum fun v hv => one_le_gridBoundaryDeficiency_of_boundary
          (by omega) (by omega) v (hboundary v hv)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (by simp)
  rw [card_union_of_disjoint hd] at hsum
  have hsH := holes s hs
  have htH := holes t ht
  omega

/-- Every stable counterexample has at most one missing open side, uniformly
for `k >= 5`, with no pure-carrier-count or deficiency hypothesis. -/
theorem stable_counterexample_missing_sides_subsingleton {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (s t : Fin 4)
    (hs : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (ht : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide t v.val) :
    s = t := by
  by_contra hst
  have hlower := four_mul_le_boundaryDeficiency_of_two_missing_sides
    (by omega) F hacyc s t hst hs ht
  have hbudget := residueTwo_stable_counterexample_budget hk F hacyc hf
  let : Nonempty (GridVertex (3 * k + 2) (3 * k + 2)) :=
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hc := one_le_card_connectedComponent
    (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _))
  omega

/-- Actual witnesses on distinct covered open sides belong to distinct pure
carriers. This counts physical components, not a freely assigned side label. -/
theorem covered_sides_card_le_pure_carriers {n : Nat} (hn : 3 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (S : Finset (Fin 4))
    (hcovered : ∀ s ∈ S, ∃ C ∈ pureBoundaryCarriers F, ∃ v ∈ C.supp,
      OnOpenSide s v.val) :
    S.card ≤ (pureBoundaryCarriers F).card := by
  classical
  have hex (s : S) := hcovered s.val s.property
  choose C hC v hv hs using hex
  let f : S → pureBoundaryCarriers F := fun s => ⟨C s, hC s⟩
  have hinj : Function.Injective f := by
    intro s t he
    have heC : C s = C t := congrArg Subtype.val he
    obtain ⟨a, ha⟩ := pure_carrier_on_side hn F hacyc (C t) (hC t)
    have hsa := openSide_unique (hs s) (ha (v s) (heC ▸ hv s))
    have hta := openSide_unique (hs t) (ha (v t) (hv t))
    exact Subtype.ext (hsa.trans hta.symm)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- At least three open sides have physical pure-carrier witnesses in every
stable counterexample, including `k = 5` and `k = 6`. -/
theorem stable_counterexample_three_le_covered_sides {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    3 ≤ (univ.filter (fun s : Fin 4 =>
      ∃ C ∈ pureBoundaryCarriers F, ∃ v ∈ C.supp, OnOpenSide s v.val)).card := by
  classical
  let P := fun s : Fin 4 =>
    ∃ C ∈ pureBoundaryCarriers F, ∃ v ∈ C.supp, OnOpenSide s v.val
  have hmissing : (univ.filter (fun s => ¬ P s)).card ≤ 1 := by
    apply card_le_one.mpr
    intro s hs t ht
    apply stable_counterexample_missing_sides_subsingleton hk F hacyc hf s t
    · intro C hC v hv hvs
      exact (mem_filter.mp hs).2 ⟨C, hC, v, hv, hvs⟩
    · intro C hC v hv hvt
      exact (mem_filter.mp ht).2 ⟨C, hC, v, hv, hvt⟩
  have hpart := card_filter_add_card_filter_not (s := (univ : Finset (Fin 4))) (p := P)
  simp only [card_univ, Fintype.card_fin] at hpart
  change 3 ≤ (univ.filter P).card
  omega

/-- The global lower bound of three pure boundary carriers holds at the full
stable range `k >= 5`, improving the earlier `k >= 7` threshold. -/
theorem stable_counterexample_three_le_pure_carriers {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    3 ≤ (pureBoundaryCarriers F).card := by
  have hthree := stable_counterexample_three_le_covered_sides hk F hacyc hf
  exact hthree.trans (covered_sides_card_le_pure_carriers (by omega) F hacyc _
    (fun _ hs => (mem_filter.mp hs).2))

/-- Minimal induced count is globally impossible above the stable target:
three pure carriers use the missing-side loss, and four use deep capacity. -/
theorem stable_counterexample_induced_components_ge {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    k + 3 ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent := by
  have hp := stable_counterexample_three_le_pure_carriers hk F hacyc hf
  have hr := (residueTwo_counterexample_profile (by omega) (by omega : 1 ≤ 1)
    F hacyc hf).1
  by_contra h
  have hre : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 2 := by omega
  by_cases hp3 : (pureBoundaryCarriers F).card = 3
  · have htarget := card_le_target_of_three_pure_minimal_induced hk F hacyc hp3 hre
    omega
  · have hcap := card_le_perimeter_add_remaining_deep_capacity (by omega) F hacyc
    rw [hre] at hcap
    have hsub : k + 2 - (pureBoundaryCarriers F).card - (nextRingCarriers F).card ≤
        k - 2 := by omega
    have hmul := Nat.mul_le_mul_left (3 * k + 2 - 4) hsub
    have hk2 : k - 2 + 2 = k := by omega
    have hn2 : 3 * k + 2 - 4 + 2 = 3 * k := by omega
    have hper : 4 * (3 * k + 2) - 4 = 12 * k + 4 := by omega
    rw [hper] at hcap
    nlinarith

end GridGraphs.CarrierLayers
