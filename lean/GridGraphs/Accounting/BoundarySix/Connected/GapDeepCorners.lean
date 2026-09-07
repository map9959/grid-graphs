import GridGraphs.Accounting.BoundarySix.Connected.GapCorners

/-! # The two gaps force two distinct preserved deep corners

Coordinates are ambient. The deep corners have coordinates two or n-3.
Their preservation follows from actual domination of missing outer spokes,
not from a normalized boundary construction.
-/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

def IsDeepCorner {n : Nat} (v : GridVertex n n) : Prop :=
  (v.1.val = 2 ∨ v.1.val + 3 = n) ∧ (v.2.val = 2 ∨ v.2.val + 3 = n)

/-- A second-position boundary hole at the endpoint forces the deep corner
with the same geometric corner label. -/
theorem current_endpoint_second_hole_forces_deep_corner {k : Nat}
    (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6)
    {u : GridVertex (3 * k + 2) (3 * k + 2)} (huS : Second u) (huF : u ∉ F) :
    ∃ w ∈ F, IsDeepCorner w ∧ cornerLabel w = cornerLabel u := by
  have hEmpty := current_endpoint_nextRing_empty hk hmod F hacyc hf hb
  have force (s : Fin 4) (t : Fin (3 * k + 2))
      (ht : t.val = 2 ∨ t.val + 3 = 3 * k + 2)
      (he : u = sideChart s (t, ⟨0, by omega⟩)) :
      ∃ w ∈ F, IsDeepCorner w ∧ cornerLabel w = cornerLabel u := by
    have hw := endpoint_empty_ring_forces_deep hk hmod F hacyc hf hb
      (card_eq_zero.mpr hEmpty) s t.val (by omega) (by omega) (he ▸ huF)
    refine ⟨sideChart s (t, ⟨2, by omega⟩), hw, ?_, ?_⟩
    · fin_cases s <;> simp [sideChart, IsDeepCorner] <;> omega
    · rw [he]
      fin_cases s <;> apply Prod.ext <;> simp [cornerLabel, sideChart] <;> omega
  rcases huS with ⟨hr, hc⟩ | ⟨hc, hr⟩
  · rcases hr with hr | hr
    · apply force 0 u.2 hc
      apply Prod.ext <;> apply Fin.ext <;> simp [sideChart]
      exact Fin.ext hr
    · apply force 1 u.2 hc
      apply Prod.ext <;> apply Fin.ext <;> simp [sideChart]
      omega
  · rcases hc with hc | hc
    · apply force 2 u.1 hr
      apply Prod.ext <;> apply Fin.ext <;> simp [sideChart]
      exact Fin.ext hc
    · apply force 3 u.1 hr
      apply Prod.ext <;> apply Fin.ext <;> simp [sideChart]
      omega

/-- Two distinct actual preserved deep corners are forced in every remaining
boundary-six endpoint. Their labels match the two distinct gap corners. -/
theorem current_endpoint_two_preserved_deep_corners {k : Nat}
    (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6) :
    ∃ z ∈ F, ∃ w ∈ F, IsDeepCorner z ∧ IsDeepCorner w ∧
      cornerLabel z ≠ cornerLabel w ∧ z ≠ w := by
  obtain ⟨Q, u, v, _, _, _, _, _, _, huS, hvS, huv, _, _, hB, _⟩ :=
    current_endpoint_two_distinct_corner_gaps hk hmod F hacyc hf hb
  have huF : u.1 ∉ F := by
    have hm : u.1 ∈ (univ \ F).filter IsGridBoundary := by rw [hB]; simp
    exact (mem_sdiff.mp (mem_filter.mp hm).1).2
  have hvF : v.1 ∉ F := by
    have hm : v.1 ∈ (univ \ F).filter IsGridBoundary := by rw [hB]; simp
    exact (mem_sdiff.mp (mem_filter.mp hm).1).2
  obtain ⟨z, hzF, hzD, hzL⟩ := current_endpoint_second_hole_forces_deep_corner
    hk hmod F hacyc hf hb huS huF
  obtain ⟨w, hwF, hwD, hwL⟩ := current_endpoint_second_hole_forces_deep_corner
    hk hmod F hacyc hf hb hvS hvF
  have hlabels : cornerLabel z ≠ cornerLabel w := by rwa [hzL, hwL]
  exact ⟨z, hzF, w, hwF, hzD, hwD, hlabels, fun he => hlabels (congrArg cornerLabel he)⟩

end GridGraphs.BoundarySix.Connected
