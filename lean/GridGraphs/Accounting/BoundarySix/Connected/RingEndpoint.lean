import GridGraphs.Accounting.BoundarySix.Connected.RingCycle

/-! # The surviving nonempty-ring endpoint geometry

The second-position cycle is a genuine exclusion. The remaining ring position
is three from an end, and its actual carrier contains the boundary root, the
ring vertex, and the twice-inward vertex. No exclusion of this case is claimed.
-/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus

/-- At the current boundary-six endpoint, every charted ring vertex is at the
third position and has both its outward and inward neighbors preserved. All
carrier-count premises of the cycle argument follow from the endpoint. -/
theorem endpoint_ring_position_three {k : Nat} (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6)
    (s : Fin 4) (t : Fin (3 * k + 2))
    (ht : 0 < t.val ∧ t.val + 1 < 3 * k + 2)
    (hw : sideChart s (t, ⟨1, by omega⟩) ∈ F) :
    (t.val = 3 ∨ t.val + 4 = 3 * k + 2) ∧
      sideChart s (t, ⟨0, by omega⟩) ∈ F ∧
      sideChart s (t, ⟨2, by omega⟩) ∈ F := by
  obtain ⟨_, _, hprofiles⟩ := current_upper_endpoint_profiles hk hmod F hacyc hf
  have hr : Fintype.card (Carrier F) = k + 4 := by
    change Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 4
    omega
  obtain ⟨hp, hzero, _⟩ := endpoint_carrier_partition hk hmod F hacyc hf hr
  have hpos := inward_position_three (by omega) F hacyc hb hp.ge hzero s t ht hw
  exact ⟨hpos, third_position_outer_preserved (by omega) F hacyc hb s t hpos hw,
    inward_depth_two_of_no_shallow (by omega) F hacyc hzero s t ht hw⟩

/-- Without choosing a side chart or normalizing any holes, every preserved
next-ring vertex at the endpoint is one of the eight third-position vertices. -/
theorem endpoint_nextRing_eight_positions {k : Nat} (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6)
    {w : GridVertex (3 * k + 2) (3 * k + 2)} (hw : w ∈ F) (hwR : IsNextRing w) :
    ((w.1.val = 1 ∨ w.1.val + 2 = 3 * k + 2) ∧
      (w.2.val = 3 ∨ w.2.val + 4 = 3 * k + 2)) ∨
    ((w.2.val = 1 ∨ w.2.val + 2 = 3 * k + 2) ∧
      (w.1.val = 3 ∨ w.1.val + 4 = 3 * k + 2)) := by
  have chart (s : Fin 4) (t : Fin (3 * k + 2))
      (ht : 0 < t.val ∧ t.val + 1 < 3 * k + 2)
      (he : sideChart s (t, ⟨1, by omega⟩) = w) :
      t.val = 3 ∨ t.val + 4 = 3 * k + 2 := by
    exact (endpoint_ring_position_three hk hmod F hacyc hf hb s t ht (he ▸ hw)).1
  obtain ⟨hrlo, hrhi, hclo, hchi, hside⟩ := hwR
  rcases hside with htop | hbottom | hleft | hright
  · have he : sideChart 0 (w.2, ⟨1, by omega⟩) = w := by
      apply Prod.ext <;> apply Fin.ext <;> simp [sideChart]
      omega
    exact Or.inl ⟨Or.inl htop, chart 0 w.2 (by omega) he⟩
  · have he : sideChart 1 (w.2, ⟨1, by omega⟩) = w := by
      apply Prod.ext <;> apply Fin.ext <;> simp [sideChart]
      omega
    exact Or.inl ⟨Or.inr (by omega), chart 1 w.2 (by omega) he⟩
  · have he : sideChart 2 (w.1, ⟨1, by omega⟩) = w := by
      apply Prod.ext <;> apply Fin.ext <;> simp [sideChart]
      omega
    exact Or.inr ⟨Or.inl hleft, chart 2 w.1 (by omega) he⟩
  · have he : sideChart 3 (w.1, ⟨1, by omega⟩) = w := by
      apply Prod.ext <;> apply Fin.ext <;> simp [sideChart]
      omega
    exact Or.inr ⟨Or.inr (by omega), chart 3 w.1 (by omega) he⟩

end GridGraphs.BoundarySix.Connected
