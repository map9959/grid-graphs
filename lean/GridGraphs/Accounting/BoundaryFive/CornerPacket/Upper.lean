import GridGraphs.Accounting.BoundaryFive.CornerPacket.Capacity
import GridGraphs.Accounting.BoundaryFive.CornerPacket.Transport

/-! # Exclusion of the connected boundary-five first endpoint profile

Only the gap is positioned. The original component profile is transported,
so the other two current endpoint profiles cannot replace it after normalization.
-/

namespace GridGraphs.BoundaryFive.CornerPacket

open Finset SimpleGraph CarrierLayers.Annulus

/-- Global sharp target bound on the `b=5,c=1,r<=k+5` branch, without an
orientation, endpoint-score, or residue premise. -/
theorem card_le_target_of_boundary_five_connected {k : Nat} (hk : 7 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 1)
    (hr : Fintype.card (Carrier F) ≤ k + 5) : F.card ≤ 3 * k ^ 2 + 7 * k := by
  obtain ⟨F', hcard, hac, hr', hc', hb', ha, hh⟩ :=
    exists_top_gap_pullback_profile (by omega) F hacyc hb
  have hbound := top_gap_card_le_target hk F' hac hb' (hc'.trans hc)
    (hr'.le.trans hr) ha hh
  rwa [hcard] at hbound

/-- Every connected boundary-five set has at least `k+6` actual induced
carriers, for `k>=7`. In particular `(k+5,1,5)` is impossible even without a
score or residue premise. -/
theorem connected_boundary_five_components_ge {k : Nat} (hk : 7 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 1) : k + 6 ≤ Fintype.card (Carrier F) := by
  by_contra h
  have hr : Fintype.card (Carrier F) ≤ k + 5 := by omega
  have hbound := card_le_target_of_boundary_five_connected hk F hacyc hb hc hr
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  rw [hc] at hledger
  rw [hb, htotal] at hpartition
  change Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
    (↑F : Set _)).ConnectedComponent ≤ k + 5 at hr
  nlinarith

/-- Oriented exclusion of the first current `k=1 mod 3` endpoint profile. -/
theorem top_gap_current_first_profile_false {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hr : Fintype.card (Carrier F) = k + 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 1)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) : False := by
  have hbound := top_gap_card_le_target (by omega) F hacyc hb hc hr.le ha hh
  omega

/-- The first current endpoint profile is impossible globally, with no gap
orientation or short-carrier certificate among the hypotheses. -/
theorem current_upper_endpoint_first_profile_false {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hr : Fintype.card (Carrier F) = k + 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 1)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5) : False := by
  have hbound := card_le_target_of_boundary_five_connected (by omega) F hacyc hb hc hr.le
  omega

/-- Only the other two actual profiles remain at the current endpoint.
Neither is asserted to exist or excluded by this theorem. -/
theorem current_upper_endpoint_two_profiles {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card) :
    let r := Fintype.card (Carrier F)
    let c := Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent
    let b := boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F)
    F.card = 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ∧
      ((r = k + 4 ∧ c = 2 ∧ b = 5) ∨ (r = k + 4 ∧ c = 1 ∧ b = 6)) := by
  obtain ⟨hcard, _, hcases⟩ := current_upper_endpoint_profiles hk hmod F hacyc hf
  refine ⟨hcard, ?_⟩
  rcases hcases with ⟨hr, hc, hb⟩ | h | h
  · exact (current_upper_endpoint_first_profile_false hk hmod F hacyc hf hr hc hb).elim
  · exact Or.inl h
  · exact Or.inr h

/-- The connected boundary-five branch saves one at the current endpoint.
This is conditional on `b=5,c=1`, not a new unconditional maximum bound. -/
theorem card_le_refined_bound_of_boundary_five_connected {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 1) :
    F.card ≤ 3 * k ^ 2 + 7 * k + (2 * k) / 3 := by
  by_contra h
  have hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card := by omega
  have hprofiles := (current_upper_endpoint_two_profiles hk hmod F hacyc hf).2
  omega

end GridGraphs.BoundaryFive.CornerPacket
