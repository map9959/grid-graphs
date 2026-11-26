import GridGraphs.Results.SmallDiagonalExact.ThirteenSides
import GridGraphs.Accounting.BoundaryFive.CornerPacket.Upper
import GridGraphs.Accounting.BoundarySix.Connected.MissingCorner
import GridGraphs.Accounting.BoundarySix.Connected.TwoGaps

/-! The only surviving side-thirteen ledger profile has an empty next ring,
three deep carriers, and a second-position perimeter hole. -/
namespace GridGraphs.Thirteen
open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus
open BoundaryFive.CornerPacket BoundarySix BoundarySix.Connected
attribute [local instance] Classical.propDecidable

theorem gap_profile (F : Finset (GridVertex 13 13))
    (acy : (forcedEdgeGraph (gridGraph 13 13) (↑F : Set _)).IsAcyclic)
    (hf : 69 ≤ F.card) :
    Fintype.card (forcedEdgeGraph (gridGraph 13 13) (↑F : Set _)).ConnectedComponent = 1 ∧
    F.filter IsNextRing = ∅ ∧ (deepCarriers F).card = 3 ∧
    ∃ u : GridVertex 13 13, Second u ∧ u ∉ F := by
  let r := Fintype.card (Carrier F)
  let c := Fintype.card (forcedEdgeGraph (gridGraph 13 13) (↑F : Set _)).ConnectedComponent
  let b := boundaryDeficiencySum 13 13 (univ \ F)
  let p := (pureBoundaryCarriers F).card
  let d := (deepCarriers F).card
  let a := (selected F).card
  let z := (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card
  let m := (fullCarriers F).card
  have ledger : 3 * F.card + r + c + b = 221 := by
    have h := grid_component_reduction F acy
    have ht := boundaryDeficiencySum_add_compl 13 13 F
    rw [total_boundaryDeficiencySum (by decide : 2 ≤ 13) (by decide : 2 ≤ 13)] at ht
    dsimp [r,c,b,Carrier]
    omega
  have hc : 1 ≤ c := Fintype.card_pos_iff.mpr
    ⟨(forcedEdgeGraph (gridGraph 13 13) (↑F : Set _)).connectedComponentMk (0,0)⟩
  have hb : 5 ≤ b := five_le_boundaryDeficiencySum_compl (by decide) F acy
  have len : F.card ≤ 13*r := forced_card_le_side_mul_components F acy
  have hp : 4 ≤ p := by
    by_contra h
    have h' : 9 ≤ b := nine_le_cost_of_missing_carrier F acy (by omega)
    omega
  have hpartition : d + p + (nextRingCarriers F).card = r := carrier_partition F
  have ha : a + 9 ≤ 52 := selected_card_add_nine_le (by decide) F acy
  have hphys := physical_deficit_identity (by decide) F acy
  dsimp only at hphys
  rw [← deepCarriers_card, ← selected_card_layers (by decide) F] at hphys
  change a ≤ 48 ∧ z ≤ 9*d ∧ F.card + (48-a) + (9*d-z) = 48+9*d at hphys
  have hm : d ≤ m + (9*d-z) := deep_count_le_full_add_deficit (by decide) F acy
  -- There are at least three deep carriers: the annulus holds at most 43
  -- sites and each deep carrier holds at most nine. Together with the four
  -- pure carriers this leaves at most six units of boundary deficiency.
  have low : b = 5 ∨ b = 6 := by omega
  rcases low with hb5 | hb6
  -- At cost five, the single-full-carrier cap forces connectedness. Rotate
  -- the two adjacent holes to the top and apply their joint capacity bound.
  · have hone : m ≤ 1 := boundary_five_fullCarriers_le_one (by decide) F acy hb5
    have hc1 : c = 1 := by omega
    obtain ⟨F',hF',ac',hr',hc',hb',q,t⟩ := exists_top_gap_pullback_profile
      (by decide) F acy hb5
    have cap := top_gap_card_capacity (by decide) F' ac' hb' (hc'.trans hc1) q t
    obtain ⟨hB,hE,_⟩ := boundary_five_annulus_occupancy (by decide) F' ac' hb'
    have hP := forced_boundary_card_le_pureBoundaryCarriers_add_nextRing (by decide) F' ac'
    have hpart := carrier_partition F'
    change Fintype.card (Carrier F') = r at hr'
    omega
  · have facts : c = 1 ∧ p = 4 ∧ d = 3 ∧ 2 ≤ m := by omega
    obtain ⟨hc1,hp4,hd3,hm2⟩ := facts
    have bridge := fullCarriers_card_add_one_le_components (by decide) F acy
    change m + 1 ≤ _ at bridge
    -- At least two full rods rule out a connected annulus, hence both a
    -- next-ring site and an omitted outer corner are impossible.
    have emptyRing : F.filter IsNextRing = ∅ := by
      apply not_nonempty_iff_eq_empty.mp
      intro hR
      have h0 : m = 0 := (nonempty_ring_no_full_rods (by decide) F acy hb6 hp hR).2.2
      omega
    have corners : ∀ w, Corner w → w ∈ F := by
      intro w hw
      by_contra h
      have hA := (missing_corner_annulus_tree (by decide) F acy hb6 hp hw h).2
      omega
    obtain ⟨Q,u,v,q,t,_,_,_,_,_,_,_,_,hu,_,_,_,hholes,_⟩ :=
      two_gap_classification (by decide) F acy hb6 hp4 hc1 emptyRing corners
    refine ⟨hc1,emptyRing,hd3,u.1,hu,?_⟩
    have hh : u.1 ∈ (univ \ F).filter IsGridBoundary := by rw [hholes]; simp
    exact (mem_sdiff.mp (mem_filter.mp hh).1).2

end GridGraphs.Thirteen
