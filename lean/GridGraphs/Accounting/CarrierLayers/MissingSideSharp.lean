import GridGraphs.Accounting.CarrierLayers.MissingSide
import GridGraphs.Accounting.CarrierLayers.RadialNearTightExclusion

/-!
# Excluding two excess vertices on any missing side

The physical root and component counts reduce a hypothetical missing-side
two-excess configuration to the excluded at-most-three-pure-carriers branch.
Consequently every two-excess configuration covers all four open sides with
distinct pure boundary carriers. No pure carrier count is assumed.
-/

namespace GridGraphs

open Finset SimpleGraph CarrierLayers

/-- Any missing open side gives `|F| ≤ T(k)+1`, independently of pure carrier
count and without maximality or connectivity assumptions. -/
theorem residueTwo_card_le_target_add_one_of_missing_side
    {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hmissing : ∃ s : Fin 4, ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    F.card ≤ 3 * k ^ 2 + 7 * k + 1 := by
  classical
  by_contra h
  have hcard : 3 * k ^ 2 + 7 * k + 2 ≤ F.card := by omega
  obtain ⟨_, hr, _, hb⟩ :=
    residueTwo_two_excess_missing_side_profile_unique hk F hacyc hmissing hcard
  obtain ⟨s, hs⟩ := hmissing
  have hbudget := (near_tight_missing_side_budget hk F hacyc hb s hs).1
  have hnonreuse := missing_side_roots_add_pure_le_components F hacyc s hs
  have hp : (pureBoundaryCarriers F).card ≤ 3 := by omega
  have hupper := residueTwo_card_le_target_add_one_of_pure_carriers_le_three hk F hacyc hp
  omega

/-- Two excess vertices force a pure-carrier witness on every open side,
including configurations with the formerly surviving numerical profile. -/
theorem residueTwo_all_open_sides_covered_of_two_excess
    {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hcard : 3 * k ^ 2 + 7 * k + 2 ≤ F.card) :
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
  have hupper := residueTwo_card_le_target_add_one_of_missing_side hk F hacyc hmissing
  omega

/-- Two excess vertices require four distinct physical pure carriers, one
meeting each open side, and hence at least four pure carriers in total. -/
theorem residueTwo_four_distinct_pure_carriers_of_two_excess
    {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hcard : 3 * k ^ 2 + 7 * k + 2 ≤ F.card) :
    ∃ f : Fin 4 → pureBoundaryCarriers F, Function.Injective f ∧
      (∀ s, ∃ v ∈ (f s).val.supp, OnOpenSide s v.val) ∧
      4 ≤ (pureBoundaryCarriers F).card := by
  exact distinct_pure_carriers_of_all_open_sides_covered (by omega) F hacyc
    (residueTwo_all_open_sides_covered_of_two_excess hk F hacyc hcard)

end GridGraphs
