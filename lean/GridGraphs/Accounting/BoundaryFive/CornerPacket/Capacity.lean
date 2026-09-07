import GridGraphs.Accounting.BoundaryFive.CornerPacket.Mirror
import GridGraphs.Accounting.BoundaryFive.CornerPacket.Annulus
import GridGraphs.Accounting.CarrierLayers.AllCoveredCounterexamples

/-! # Summing the corner packet over actual deep carriers -/

namespace GridGraphs.BoundaryFive.CornerPacket

open Finset SimpleGraph CarrierLayers CarrierLayers.Annulus CarrierLayers.FourCarrier

attribute [local instance] Classical.propDecidable

/-- With no next-ring occupancy, a shallow nonpure carrier cannot exist. -/
theorem boundary_five_no_shallow {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5) : nextRingCarriers F = ∅ := by
  have hE := (boundary_five_annulus_occupancy hn F hacyc hb).2.1
  have hno (v : (↑F : Set (GridVertex n n))) : ¬ IsNextRing v.1 := by
    intro hv
    have hm : v.1 ∈ F.filter IsNextRing := mem_filter.mpr ⟨v.2, hv⟩
    rw [card_eq_zero.mp hE] at hm
    exact Finset.notMem_empty _ hm
  apply eq_empty_iff_forall_notMem.mpr
  intro C hC
  obtain ⟨hnp, hsh⟩ := (mem_filter.mp hC).2
  apply hnp
  apply mem_filter.mpr
  exact ⟨mem_univ _, fun v hv => (hsh v hv).resolve_right (hno v)⟩

/-- The two exceptional losses and all ordinary nonfull losses are counted
once each on the actual deep-carrier partition. -/
theorem two_short_deep_mass_bound {n : Nat} (hn : 10 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (Z S : Carrier F) (hZS : Z ≠ S)
    (hZ : Z ∉ pureBoundaryCarriers F) (hS : S ∉ pureBoundaryCarriers F)
    (hZsize : Z.supp.toFinset.card = 1) (hSsize : S.supp.toFinset.card ≤ 3) :
    (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card +
      (deepCarriers F).card + 2 * (n - 4) ≤ (n - 4) * (deepCarriers F).card + 7 := by
  let R := deepCarriers F
  let W := F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)
  have hsh := boundary_five_no_shallow (by omega) F hacyc hb
  have hZR : Z ∈ R := by simp [R, deepCarriers, hsh, hZ]
  have hSR : S ∈ R := by simp [R, deepCarriers, hsh, hS]
  have hcover : R.biUnion (deepVertices F) = W := by
    ext v
    constructor
    · intro hv
      obtain ⟨C, _, hvC⟩ := mem_biUnion.mp hv
      obtain ⟨hvF, _, ha⟩ := (mem_deepVertices (by omega) F C v).mp hvC
      rw [mem_iff_layers (by omega)] at ha
      exact mem_filter.mpr ⟨hvF, not_or.mp ha⟩
    · intro hv
      obtain ⟨hvF, hvb, hvr⟩ := mem_filter.mp hv
      let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk ⟨v, hvF⟩
      have hvC : v ∈ deepVertices F C := (mem_deepVertices (by omega) F C v).mpr
        ⟨hvF, by simp [C, ConnectedComponent.mem_supp_iff],
          fun ha => ((mem_iff_layers (by omega) v).mp ha).elim hvb hvr⟩
      exact mem_biUnion.mpr ⟨C, deepCarrier_of_mem_deepVertices (by omega) F C hvC, hvC⟩
  have hW : W.card ≤ ∑ C ∈ R, (deepVertices F C).card := by
    rw [← hcover]
    exact card_biUnion_le
  have hcap (C : Carrier F) : (deepVertices F C).card ≤ n - 4 := by
    rw [deepVertices_card]
    exact deep_carrier_part_card_le (by omega) F hacyc C
  have hsmall (C : Carrier F) : (deepVertices F C).card ≤ C.supp.toFinset.card := by
    rw [deepVertices_card]
    exact card_filter_le _ _
  have hlocal (C : Carrier F) : (deepVertices F C).card + 1 +
      (if C = Z then n - 6 else 0) + (if C = S then n - 8 else 0) ≤
      (n - 4) + (if C ∈ fullCarriers F then 1 else 0) := by
    by_cases heZ : C = Z
    · subst C
      have hz := hsmall Z
      simp only [ite_true, if_neg hZS]
      omega
    · by_cases heS : C = S
      · subst C
        have hs := hsmall S
        simp only [if_neg heZ, ite_true]
        omega
      · simp only [if_neg heZ, if_neg heS, Nat.add_zero]
        have hc := hcap C
        by_cases hf : C ∈ fullCarriers F
        · rw [if_pos hf]
          omega
        · rw [if_neg hf]
          have hne : (deepVertices F C).card ≠ n - 4 := by
            simpa only [fullCarriers, mem_filter, mem_univ, true_and] using hf
          omega
  have hsum := sum_le_sum (s := R) (fun C _ => hlocal C)
  have hfilter : R.filter (fun C => C ∈ fullCarriers F) = fullCarriers F := by
    ext C
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨fullCarriers_subset_deepCarriers (by omega) F h, h⟩⟩
  simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one, sum_boole,
    Nat.cast_id, sum_ite_eq', if_pos hZR, if_pos hSR, hfilter] at hsum
  have hM := boundary_five_fullCarriers_le_one hn F hacyc hb
  change W.card + R.card + 2 * (n - 4) ≤ (n - 4) * R.card + 7
  rw [Nat.mul_comm R.card (n - 4)] at hsum
  omega

/-- A subtraction-free physical capacity bound derived from the oriented packet. -/
theorem top_gap_card_capacity {n : Nat} (hn : 10 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent = 1)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    F.card + (deepCarriers F).card + 2 * (n - 4) ≤
      4 * n - 2 + (n - 4) * (deepCarriers F).card := by
  obtain ⟨Z, S, hZS, hZ, hS, hZsize, hSsize⟩ :=
    top_gap_two_short_carriers (by omega) F hacyc hb hc ha hh
  have hmass := two_short_deep_mass_bound hn F hacyc hb Z S hZS hZ hS hZsize hSsize
  have hphysical := physical_deficit_identity (by omega) F hacyc
  obtain ⟨hB, hE, _⟩ := boundary_five_annulus_occupancy (by omega) F hacyc hb
  dsimp only at hphysical
  rw [← deepCarriers_card, hB, hE] at hphysical
  omega

/-- Even one excess is impossible in the oriented `b=5,c=1,r<=k+5` branch,
for every `k>=7`. No endpoint or residue assumption is needed. -/
theorem top_gap_card_le_target {k : Nat} (hk : 7 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 1)
    (hr : Fintype.card (Carrier F) ≤ k + 5)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  by_contra hf
  have hpos : 3 * k ^ 2 + 7 * k + 1 ≤ F.card := by omega
  have hp := (stable_counterexample_pure_and_induced (by omega) F hacyc hpos).1
  have hd : (deepCarriers F).card ≤ k + 1 := by
    rw [deepCarriers_card]
    omega
  have hcap := top_gap_card_capacity (by omega) F hacyc hb hc ha hh
  have hmul := Nat.mul_le_mul_left (3 * k - 3) hd
  have hn : 3 * k + 2 - 4 = 3 * k - 2 := by omega
  have hN : 3 * k - 2 = (3 * k - 3) + 1 := by omega
  rw [hn, hN] at hcap
  have hsub : 3 * k - 3 + 3 = 3 * k := by omega
  have hper : 4 * (3 * k + 2) - 2 = 12 * k + 6 := by omega
  rw [hper] at hcap
  nlinarith

end GridGraphs.BoundaryFive.CornerPacket
