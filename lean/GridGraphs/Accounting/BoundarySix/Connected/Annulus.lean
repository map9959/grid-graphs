import GridGraphs.Accounting.BoundarySix.Connected.Endpoint

/-! # A nonempty next ring forbids full rods at the endpoint

A preserved next-ring vertex contributes an induced annulus component distinct
from every pure boundary carrier. At deficiency six and with four pure carriers,
the annulus forest budget then leaves no physical bridge for a full deep rod.
This forces a deficit on every deep carrier, but does not exclude the endpoint.
-/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

/-- The component of a preserved next-ring vertex is distinct from the annulus
components supplied by whole pure carriers. Distinctness is certified by the
map back to the actual induced grid graph. -/
theorem pure_add_one_le_annulus_components {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n)) (hRing : (F.filter IsNextRing).Nonempty) :
    (pureBoundaryCarriers F).card + 1 ≤
      Fintype.card ((graph n).induce (↑(selected F) : Set _)).ConnectedComponent := by
  obtain ⟨w, hw⟩ := hRing
  obtain ⟨hwF, hwR⟩ := mem_filter.mp hw
  let G := (gridGraph n n).induce (↑F : Set _)
  let L := (graph n).induce (↑(selected F) : Set _)
  let C := G.connectedComponentMk ⟨w, hwF⟩
  have hwC : (⟨w, hwF⟩ : (↑F : Set _)) ∈ C.supp := by
    simp [C, ConnectedComponent.mem_supp_iff]
  have hC : C ∉ pureBoundaryCarriers F := by
    intro hp
    have hwb := (mem_filter.mp hp).2 _ hwC
    change IsGridBoundary w at hwb
    unfold IsGridBoundary at hwb
    unfold IsNextRing at hwR
    omega
  let Q := insert C (pureBoundaryCarriers F)
  have hex (D : Q) : ∃ v ∈ D.1.supp, Mem v.1 := by
    rcases mem_insert.mp D.2 with he | hp
    · exact ⟨⟨w, hwF⟩, he ▸ hwC, (mem_iff_layers hn w).mpr (Or.inr hwR)⟩
    · obtain ⟨v, hv⟩ := D.1.nonempty_supp
      exact ⟨v, hv, (mem_iff_layers hn v.1).mpr (Or.inl ((mem_filter.mp hp).2 v hv))⟩
  choose u hu hA using hex
  let v (D : Q) : (↑(selected F) : Set (Vertex n)) :=
    ⟨⟨(u D).1, hA D⟩, mem_filter.mpr ⟨mem_univ _, (u D).2⟩⟩
  let f (D : Q) : L.ConnectedComponent := L.connectedComponentMk (v D)
  let inc : L →g G :=
    { toFun := fun x => ⟨x.1.1, (mem_filter.mp x.2).2⟩
      map_rel' := by intro x y h; exact h }
  have hmap (D : Q) : (f D).map inc = D.1 := hu D
  have hi : Function.Injective f := by
    intro D E he
    apply Subtype.ext
    exact (hmap D).symm.trans ((congrArg (fun c => c.map inc) he).trans (hmap E))
  have hc := Fintype.card_le_of_injective f hi
  rw [Fintype.card_coe, show Q.card = (pureBoundaryCarriers F).card + 1 from
    card_insert_of_notMem hC] at hc
  exact hc

/-- With four pure carriers and a nonempty next ring, the boundary-six annulus
is a single forced component and admits no full deep rod. The bridge loss is
physical, not a postulated contact-graph forest inequality. -/
theorem nonempty_ring_no_full_rods {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (hp : 4 ≤ (pureBoundaryCarriers F).card)
    (hRing : (F.filter IsNextRing).Nonempty) :
    Fintype.card ((graph n).induce (↑(selected F) : Set _)).ConnectedComponent = 5 ∧
      Fintype.card (forcedEdgeGraph (graph n) (↑(selected F) : Set _)).ConnectedComponent = 1 ∧
      (fullCarriers F).card = 0 := by
  have hr := pure_add_one_le_annulus_components (by omega) F hRing
  have hbudget := component_budget hn F hacyc
  have hboundary := boundaryDeficiencySum_compl_eq_six_boundary_card_lower hn F hacyc hb
  have hpositive := card_pos.mpr hRing
  have hbridge := fullCarriers_card_add_one_le_components (by omega) F hacyc
  omega

/-- At the current boundary-six endpoint, a nonempty next ring forces all `k`
deep carriers to be nonfull. No pure-count or connectivity premise is added. -/
theorem endpoint_nonempty_ring_no_full_rods {k : Nat}
    (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6)
    (hRing : (F.filter IsNextRing).Nonempty) :
    (fullCarriers F).card = 0 := by
  have he : 2 ≤ (2 * k + 1) / 3 := by omega
  obtain ⟨_, _, _, hp⟩ := residueTwo_four_distinct_pure_carriers_of_two_excess
    hk F hacyc (by omega)
  exact (nonempty_ring_no_full_rods (by omega) F hacyc hb hp hRing).2.2

end GridGraphs.BoundarySix.Connected
