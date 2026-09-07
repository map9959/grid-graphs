import GridGraphs.Accounting.BoundarySix.Connected.DeepRooted
import GridGraphs.Accounting.BoundaryFive.Rootless.CornerRoots

/-! # Excluding the connected-annulus endpoint by actual deep roots

The boundary-root/component bijection cancels the deep boundary deficiency in
the forest ledger. This recovers the induced deep count from the exact score,
without assuming a carrier-trimming bijection or counting only nonisolates.
-/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus
open BoundaryFive.Rootless

attribute [local instance] Classical.propDecidable

/-- Actual unique boundary roots identify all forced components with preserved
boundary vertices. With four unpreserved corners their ledger contributions cancel. -/
theorem rooted_deep_score {m : Nat} (hm : 2 ≤ m) (F : Finset (GridVertex m m))
    (hacyc : (forcedEdgeGraph (gridGraph m m) (↑F : Set _)).IsAcyclic)
    (hex : BoundaryRooted (m := m) (↑F : Set _))
    (hroot : UniqueBoundaryRoots (m := m) (↑F : Set _))
    (hcorners : ∀ v, Corner v → v ∉ F) :
    3 * F.card + Fintype.card ((gridGraph m m).induce (↑F : Set _)).ConnectedComponent = m * m := by
  let H := forcedEdgeGraph (gridGraph m m) (↑F : Set _)
  let R := F.filter IsGridBoundary
  let f (v : R) : H.ConnectedComponent := H.connectedComponentMk v.1
  have hi : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    exact hroot u.1 (mem_filter.mp u.2).1 v.1 (mem_filter.mp v.2).1
      (mem_filter.mp u.2).2 (mem_filter.mp v.2).2 (ConnectedComponent.exact he)
  have hs : Function.Surjective f := by
    intro C
    obtain ⟨v, hv⟩ := C.nonempty_supp
    obtain ⟨u, hu, hub, hreach⟩ := hex v
    refine ⟨⟨u, mem_filter.mpr ⟨hu, hub⟩⟩, ?_⟩
    exact (ConnectedComponent.sound hreach).symm.trans hv
  have hcard := Fintype.card_of_bijective (f := f) ⟨hi, hs⟩
  rw [Fintype.card_coe] at hcard
  have hweight (v : GridVertex m m) (hv : v ∈ F) :
      gridBoundaryDeficiency m m v = if IsGridBoundary v then 1 else 0 := by
    have hnc : ¬ Corner v := fun h => hcorners v h hv
    rw [gridBoundaryDeficiency_eq_four_side_indicators hm hm]
    unfold IsGridBoundary Corner at *
    split_ifs <;> omega
  have hb : boundaryDeficiencySum m m F = R.card := by
    unfold boundaryDeficiencySum
    rw [sum_congr rfl hweight]
    simp [R]
  have hledger := grid_component_reduction F hacyc
  change R.card = Fintype.card H.ConnectedComponent at hcard
  change 3 * F.card + _ + Fintype.card H.ConnectedComponent = _ at hledger
  omega

/-- The actual selected vertices partition into the annulus and the offset
deep crop; no particular boundary-hole pattern is used. -/
theorem deepSelected_card_partition {m n : Nat} (hm : m + 4 = n)
    (F : Finset (GridVertex n n)) :
    (deepSelected hm F).card + (selected F).card = F.card := by
  have he : (deepSelected hm F).map (deepEmbedding hm) = F.filter (fun v => ¬ Mem v) := by
    ext v
    simp only [mem_map, mem_filter]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(mem_deepSelected hm F w).mp hw, deepEmbedding_not_mem hm w⟩
    · rintro ⟨hv, ha⟩
      obtain ⟨w, rfl⟩ := deepEmbedding_range hm ha
      exact ⟨w, (mem_deepSelected hm F w).mpr hv, rfl⟩
  have hcard := congrArg Finset.card he
  rw [card_map] at hcard
  rw [hcard, selected_card, Nat.add_comm]
  exact card_filter_add_card_filter_not _

/-- A connected forced annulus of mass `4n-9` cannot occur at the current
boundary-six endpoint. All actual deep-root hypotheses are proved here. -/
theorem connected_annulus_current_endpoint_false {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6)
    (hcA : Fintype.card (forcedEdgeGraph (graph (3 * k + 2))
      (↑(selected F) : Set _)).ConnectedComponent = 1)
    (hMass : (selected F).card + 9 = 4 * (3 * k + 2)) : False := by
  obtain ⟨hfeq, _, hprofiles⟩ := current_upper_endpoint_profiles hk hmod F hacyc hf
  have hrc : Fintype.card (Carrier F) = k + 4 ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent = 1 := by
    change Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 4 ∧ _
    omega
  have hzero := (endpoint_carrier_partition hk hmod F hacyc hf hrc.1).2.1
  have hm : (3 * k - 2) + 4 = 3 * k + 2 := by omega
  let D := deepSelected hm F
  have hac := deepSelected_acyclic hm F hacyc
  have hex := deep_boundary_rooted hm (by omega) F hacyc hrc.2 hzero
  have hroot := deep_unique_boundary_roots hm F hacyc hcA
  have hcorners := deep_corners_unpreserved hm (by omega) F hacyc hcA
  have hpart := deepSelected_card_partition hm F
  have hquot : 3 * ((2 * k + 1) / 3) = 2 * k + 1 := by omega
  have hm2 : 3 * k - 2 + 2 = 3 * k := by omega
  have hscore : 3 * D.card + k = (3 * k - 2) * (3 * k - 2) := by
    dsimp [D]
    nlinarith
  have hledger := rooted_deep_score (by omega) D hac hex hroot hcorners
  have hq : Fintype.card ((gridGraph (3 * k - 2) (3 * k - 2)).induce
      (↑D : Set _)).ConnectedComponent = k := by omega
  exact rooted_deep_endpoint_false (by omega) hm2 D hac hex hroot hcorners hq hscore

/-- The entire nonempty-next-ring boundary-six endpoint branch is impossible.
The proof does not classify the position of the preserved next-ring vertex. -/
theorem current_endpoint_nonempty_ring_false {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6)
    (hRing : (F.filter IsNextRing).Nonempty) : False := by
  have he : 2 ≤ (2 * k + 1) / 3 := by omega
  obtain ⟨_, _, _, hp⟩ := residueTwo_four_distinct_pure_carriers_of_two_excess
    hk F hacyc (by omega)
  have hcA := (nonempty_ring_no_full_rods (by omega) F hacyc hb hp hRing).2.1
  have hB := boundaryDeficiencySum_compl_eq_six_boundary_card_lower (by omega) F hacyc hb
  have hE := card_pos.mpr hRing
  have hcap := selected_card_add_nine_le (by omega) F hacyc
  have hparts := selected_card_layers (by omega) F
  apply connected_annulus_current_endpoint_false hk hmod F hacyc hf hb hcA
  omega

/-- Only the empty-next-ring case remains in the current boundary-six profile. -/
theorem current_endpoint_nextRing_empty {k : Nat} (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6) :
    F.filter IsNextRing = ∅ := by
  exact not_nonempty_iff_eq_empty.mp (current_endpoint_nonempty_ring_false hk hmod F hacyc hf hb)

end GridGraphs.BoundarySix.Connected
