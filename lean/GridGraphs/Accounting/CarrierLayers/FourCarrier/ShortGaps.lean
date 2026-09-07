import GridGraphs.Accounting.CarrierLayers.FourCarrier.GapArithmetic

/-! # Short gaps at three off-side units

All inclusive root-free intervals have length at most four, including end gaps.
A four-position interval forces a root at one of the two second positions.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Actual root positions at root deficit one: three-spaced, away from the
endpoints, and not simultaneously occupying both second positions. -/
theorem root_deficit_position_data {k : Nat} (hk : 3 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hq : (F.filter (OnOpenSide s)).card = k - 1)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 3) :
    let A := (F.filter (OnOpenSide s)).image (sidePosition s)
    A.card = k - 1 ∧ (∀ x ∈ A, 2 ≤ x ∧ x < 3 * k) ∧
      (∀ x ∈ A, ∀ y ∈ A, x < y → x + 3 ≤ y) ∧ ¬ (2 ∈ A ∧ 3 * k - 1 ∈ A) := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [card_image_iff.mpr, hq]
    intro u hu v hv he
    exact sidePosition_injective (mem_filter.mp hu).2 (mem_filter.mp hv).2 he
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    have h := root_positions_of_offside_deficiency_le_four (by omega) F hacyc s hmissing
      (by omega) v (mem_filter.mp hv).1 (mem_filter.mp hv).2
    simpa only [Nat.add_sub_cancel] using h
  · intro x hx y hy hlt
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
    obtain ⟨w, hw, hwr, huw⟩ := missing_side_root_inward (by omega) F hacyc s hmissing
      u (mem_filter.mp hu).1 (mem_filter.mp hu).2
    obtain ⟨z, hz, hzr, hvz⟩ := missing_side_root_inward (by omega) F hacyc s hmissing
      v (mem_filter.mp hv).1 (mem_filter.mp hv).2
    exact radial_pair_spacing (by omega) F hacyc s
      (mem_filter.mp hu).1 (mem_filter.mp hv).1 hw hz
      (mem_filter.mp hu).2 (mem_filter.mp hv).2 hwr hzr huw hvz hlt
  · rintro ⟨hfirst, hlast⟩
    have hroot (t : Fin (3 * k + 2)) (ht : 0 < t.val ∧ t.val + 1 < 3 * k + 2)
        (hm : t.val ∈ (F.filter (OnOpenSide s)).image (sidePosition s)) :
        sideChart s (t, ⟨0, by omega⟩) ∈ F := by
      obtain ⟨u, hu, he⟩ := mem_image.mp hm
      have hs := (sideChart_openSide s (t, ⟨0, by omega⟩)).mpr ⟨rfl, ht⟩
      have heq := sidePosition_injective (mem_filter.mp hu).2 hs
        (by rw [sideChart_position]; exact he)
      exact heq ▸ (mem_filter.mp hu).1
    apply not_both_second_roots_of_offside_le_three (by omega) F hacyc s hmissing hW
    · exact hroot (⟨2, by omega⟩ : Fin (3 * k + 2)) (by dsimp; omega) hfirst
    · apply hroot (⟨3 * k + 2 - 3, by omega⟩ : Fin (3 * k + 2)) (by dsimp; omega)
      have he : 3 * k + 2 - 3 = 3 * k - 1 := by omega
      simpa only [he] using hlast

/-- At `q=k-1` and `W<=3`, every inclusive root-free interval has length at
most four. This includes intervals beginning at one or ending at `3k`. -/
theorem root_deficit_gap_le_four {k : Nat} (hk : 3 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hq : (F.filter (OnOpenSide s)).card = k - 1)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 3)
    (a b : Nat) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3 * k)
    (hgap : ∀ v ∈ F, OnOpenSide s v → a ≤ sidePosition s v → sidePosition s v ≤ b → False) :
    b - a + 1 ≤ 4 := by
  classical
  let A := (F.filter (OnOpenSide s)).image (sidePosition s)
  obtain ⟨hcard, hbound, hspace, hends⟩ := root_deficit_position_data hk F hacyc s hmissing hq hW
  change A.card = _ at hcard
  change ¬ (2 ∈ A ∧ 3 * k - 1 ∈ A) at hends
  have hg : ∀ x ∈ A, ¬ (a ≤ x ∧ x ≤ b) := by
    intro x hx h
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    exact hgap v (mem_filter.mp hv).1 (mem_filter.mp hv).2 h.1 h.2
  by_cases hfirst : 2 ∈ A
  · apply spaced_root_deficit_gap_bound (lo := 2) (hi := 3 * k - 2)
      (by omega) A hcard ?_ hspace (by omega) (by omega) (by omega) a b ha hab hb hg
    intro x hx
    have hx' := hbound x hx
    have hxne : x ≠ 3 * k - 1 := fun he => hends ⟨hfirst, he ▸ hx⟩
    omega
  · apply spaced_root_deficit_gap_bound (lo := 3) (hi := 3 * k - 1)
      (by omega) A hcard ?_ hspace (by omega) (by omega) (by omega) a b ha hab hb hg
    intro x hx
    have hx' := hbound x hx
    have hxne : x ≠ 2 := fun he => hfirst (he ▸ hx)
    omega

/-- A four-position gap forces a second-position root at one end of the side.
The gap itself may be an end gap. -/
theorem four_gap_forces_second_root {k : Nat} (hk : 3 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hq : (F.filter (OnOpenSide s)).card = k - 1)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 3)
    (a : Nat) (ha : 1 ≤ a) (hb : a + 3 ≤ 3 * k)
    (hgap : ∀ v ∈ F, OnOpenSide s v → a ≤ sidePosition s v → sidePosition s v ≤ a + 3 → False) :
    ∃ v ∈ F, OnOpenSide s v ∧ (sidePosition s v = 2 ∨ sidePosition s v = 3 * k - 1) := by
  classical
  let A := (F.filter (OnOpenSide s)).image (sidePosition s)
  obtain ⟨hcard, hbound, hspace, _⟩ := root_deficit_position_data hk F hacyc s hmissing hq hW
  by_contra h
  have havoid : ∀ x ∈ A, x ≠ 2 ∧ x ≠ 3 * k - 1 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    constructor <;> intro he
    · exact h ⟨v, (mem_filter.mp hv).1, (mem_filter.mp hv).2, Or.inl he⟩
    · exact h ⟨v, (mem_filter.mp hv).1, (mem_filter.mp hv).2, Or.inr he⟩
  have hshort := spaced_root_deficit_gap_bound (g := 3) (lo := 3) (hi := 3 * k - 2)
    (by omega) A hcard (by
      intro x hx
      have := hbound x hx
      have := havoid x hx
      omega) hspace (by omega) (by omega) (by omega) a (a + 3) ha (by omega) hb (by
      intro x hx h
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      exact hgap v (mem_filter.mp hv).1 (mem_filter.mp hv).2 h.1 h.2)
  omega

/-- The proved gap geometry specialized to an actual four-pure missing-side
counterexample. A length-four interval requires a second-position root; all
intervals, including both end gaps, are bounded by four. -/
theorem four_pure_missing_side_gap_geometry {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 4) :
    (∀ v, BoundarySix.Corner v → v ∈ F) ∧
      (∀ v ∈ F, OnOpenSide s v → 2 ≤ sidePosition s v ∧ sidePosition s v < 3 * k) ∧
      ∀ a b : Nat, 1 ≤ a → a ≤ b → b ≤ 3 * k →
        (∀ v ∈ F, OnOpenSide s v → a ≤ sidePosition s v → sidePosition s v ≤ b → False) →
        b - a + 1 ≤ 4 ∧ (b - a + 1 = 4 →
          ∃ v ∈ F, OnOpenSide s v ∧ (sidePosition s v = 2 ∨ sidePosition s v = 3 * k - 1)) := by
  have hW := four_pure_offside_deficiency_eq_three hk F hacyc s hmissing hf hp
  have hq := (four_pure_missing_side_profile hk F hacyc s hmissing hf hp).2.1
  refine ⟨corners_preserved_of_offside_le_three (by omega) F hacyc s (by omega), ?_, ?_⟩
  · intro v hv hs
    have h := root_positions_of_offside_deficiency_le_four (by omega) F hacyc s hmissing
      (by omega) v hv hs
    simpa only [Nat.add_sub_cancel] using h
  · intro a b ha hab hb hgap
    refine ⟨root_deficit_gap_le_four (by omega) F hacyc s hmissing hq (by omega)
      a b ha hab hb hgap, ?_⟩
    intro he
    have hbe : b = a + 3 := by omega
    subst b
    exact four_gap_forces_second_root (by omega) F hacyc s hmissing hq (by omega) a ha hb hgap

end GridGraphs.CarrierLayers.FourCarrier
