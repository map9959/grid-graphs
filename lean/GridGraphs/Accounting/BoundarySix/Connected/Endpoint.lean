import GridGraphs.Accounting.BoundarySix.Connected.Inward
import GridGraphs.Accounting.CarrierLayers.Annulus.Upper

/-! # The connected boundary-six endpoint

The endpoint has four pure carriers and no shallow carriers. Consequently the
physical inward constraints apply without any additional carrier hypothesis.
This file does not exclude the endpoint or assert a short deep carrier.
-/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

/-- The requested component profile leaves exactly four pure and `k` deep
carriers, with no shallow carriers. No coverage normalization is assumed. -/
theorem endpoint_carrier_partition {k : Nat} (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hr : Fintype.card (Carrier F) = k + 4) :
    (pureBoundaryCarriers F).card = 4 ∧ (nextRingCarriers F).card = 0 ∧
      (deepCarriers F).card = k := by
  have he : 2 ≤ (2 * k + 1) / 3 := by omega
  obtain ⟨_, _, _, hp⟩ := residueTwo_four_distinct_pure_carriers_of_two_excess
    hk F hacyc (by omega)
  have hd := Annulus.counterexample_deep_carriers_ge hk F hacyc (by omega)
  have hpart := carrier_partition F
  rw [deepCarriers_card] at hpart ⊢
  omega

/-- At the endpoint, each preserved depth-one vertex lies away from the
next-ring corners and extends to an actual deep vertex in its own carrier. -/
theorem endpoint_inward_extension {k : Nat} (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hr : Fintype.card (Carrier F) = k + 4)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6)
    (s : Fin 4) (t : Fin (3 * k + 2)) (ht : 0 < t.val ∧ t.val + 1 < 3 * k + 2)
    (hw : sideChart s (t, ⟨1, by omega⟩) ∈ F) :
    2 ≤ t.val ∧ t.val + 3 ≤ 3 * k + 2 ∧
      sideChart s (t, ⟨2, by omega⟩) ∈ F := by
  have hzero := (endpoint_carrier_partition hk hmod F hacyc hf hr).2.1
  have hbounds := inward_position_bounds (by omega) F hacyc hb hzero s t ht hw
  exact ⟨hbounds.1, hbounds.2,
    inward_depth_two_of_no_shallow (by omega) F hacyc hzero s t ht hw⟩

/-- In the boundary-six endpoint branch, an outer hole without its depth-two
vertex locates the sole preserved next-ring vertex. Connectivity and the
absence of shallow carriers are derived, not additional assumptions. -/
theorem endpoint_missing_deep_locates_unique_ring {k : Nat}
    (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6)
    (s : Fin 4) (t : Nat) (ht : 2 ≤ t) (htn : t + 3 ≤ 3 * k + 2)
    (hhole : sideChart s (⟨t, by omega⟩, ⟨0, by omega⟩) ∉ F)
    (hdeep : sideChart s (⟨t, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    ∃ q : Fin (3 * k + 2), (q.val + 1 = t ∨ t + 1 = q.val) ∧
      2 ≤ q.val ∧ q.val + 3 ≤ 3 * k + 2 ∧
      sideChart s (q, ⟨1, by omega⟩) ∈ F ∧
      ∀ v ∈ F, IsNextRing v → v = sideChart s (q, ⟨1, by omega⟩) := by
  obtain ⟨_, _, hprofiles⟩ := current_upper_endpoint_profiles hk hmod F hacyc hf
  have hrc : Fintype.card (Carrier F) = k + 4 ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent = 1 := by
    change Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 4 ∧ _
    omega
  have hzero := (endpoint_carrier_partition hk hmod F hacyc hf hrc.1).2.1
  exact missing_deep_locates_unique_ring (by omega) F hacyc hb hrc.2 hzero
    s t ht htn hhole hdeep

/-- In the empty-next-ring case every missing outer spoke away from the
corner neighbors has its twice-inward vertex preserved, on all four sides. -/
theorem endpoint_empty_ring_forces_deep {k : Nat}
    (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6)
    (hEmpty : (F.filter IsNextRing).card = 0)
    (s : Fin 4) (t : Nat) (ht : 2 ≤ t) (htn : t + 3 ≤ 3 * k + 2)
    (hhole : sideChart s (⟨t, by omega⟩, ⟨0, by omega⟩) ∉ F) :
    sideChart s (⟨t, by omega⟩, ⟨2, by omega⟩) ∈ F := by
  classical
  by_contra hdeep
  obtain ⟨q, _, hqlo, hqhi, hqF, _⟩ := endpoint_missing_deep_locates_unique_ring
    hk hmod F hacyc hf hb s t ht htn hhole hdeep
  have hqR : IsNextRing (sideChart s (q, ⟨1, by omega⟩)) := by
    fin_cases s <;> simp [sideChart, IsNextRing] <;> omega
  have hm := mem_filter.mpr ⟨hqF, hqR⟩
  rw [card_eq_zero.mp hEmpty] at hm
  exact notMem_empty _ hm

end GridGraphs.BoundarySix.Connected
