import GridGraphs.Accounting.BoundarySix.Connected.PacketGeometry

/-! # At least one forced deep corner is an actual singleton carrier -/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

theorem isolated_deep_corner_singleton {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n)) {z : GridVertex n n}
    (hzF : z ∈ F) (hzD : IsDeepCorner z)
    (hno : ∀ w ∈ F, ¬ (gridGraph n n).Adj z w) :
    ∃ Z : Carrier F, Z ∉ pureBoundaryCarriers F ∧ Z.supp.toFinset.card = 1 := by
  let G := (gridGraph n n).induce (↑F : Set _)
  let v : (↑F : Set (GridVertex n n)) := ⟨z, hzF⟩
  let Z := G.connectedComponentMk v
  have hvZ : v ∈ Z.supp := rfl
  have hnoG (w : (↑F : Set (GridVertex n n))) : ¬ G.Adj v w := fun h => hno w.1 w.2 h
  have heq (w : (↑F : Set (GridVertex n n))) (hw : w ∈ Z.supp) : w = v := by
    obtain ⟨p⟩ := Z.reachable_of_mem_supp hvZ hw
    cases p with
    | nil => rfl
    | cons h _ => exact (hnoG _ h).elim
  refine ⟨Z, ?_, ?_⟩
  · intro hp
    have hzb := (mem_filter.mp hp).2 v hvZ
    change IsGridBoundary z at hzb
    dsimp only [IsGridBoundary, IsDeepCorner] at hzb hzD
    omega
  · have hs : Z.supp.toFinset = {v} := by
      ext w
      simp only [Set.mem_toFinset, mem_singleton]
      exact ⟨heq w, fun he => he ▸ hvZ⟩
    rw [hs, card_singleton]

/-- If neither corner were a singleton, two literal corner packets would
close a cycle over the actual two-gap perimeter. No assumption that the two
corners lie in distinct induced carriers is made. -/
theorem current_endpoint_deep_singleton {k : Nat} (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6) :
    ∃ Z : Carrier F, Z ∉ pureBoundaryCarriers F ∧ Z.supp.toFinset.card = 1 := by
  by_contra hnone
  have neighbors (z : GridVertex (3 * k + 2) (3 * k + 2)) (hzF : z ∈ F) (hzD : IsDeepCorner z) :
      ∃ w ∈ F, (gridGraph (3 * k + 2) (3 * k + 2)).Adj z w := by
    by_contra h
    push Not at h
    exact hnone (isolated_deep_corner_singleton (by omega) F hzF hzD h)
  obtain ⟨hEmpty, hcorners⟩ := current_endpoint_empty_ring_and_preserved_corners hk hmod F hacyc hf hb
  obtain ⟨_, _, hprofiles⟩ := current_upper_endpoint_profiles hk hmod F hacyc hf
  have hr : Fintype.card (Carrier F) = k + 4 := by
    change Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 4
    omega
  have hp := (endpoint_carrier_partition hk hmod F hacyc hf hr).1
  have hholes := (two_perimeter_holes (by omega) F hacyc hb hp hEmpty hcorners).2
  have hbase := perimeter_base_two (by omega) F hholes
  obtain ⟨Q, u, v, _, _, _, hQN, _, _, huS, hvS, huv, _, _, hB, _⟩ :=
    current_endpoint_two_distinct_corner_gaps hk hmod F hacyc hf hb
  have hcover (x : GridVertex (3 * k + 2) (3 * k + 2)) (hxF : x ∉ F) (hxb : IsGridBoundary x) :
      Near x ∨ x = u.1 ∨ x = v.1 := by
    have hm : x ∈ (univ \ F).filter IsGridBoundary := mem_filter.mpr ⟨by simp [hxF], hxb⟩
    rw [hB] at hm
    rcases mem_insert.mp hm with he | hm
    · exact Or.inr (Or.inl he)
    · rcases mem_insert.mp hm with he | hm
      · exact Or.inr (Or.inr he)
      · exact Or.inl (hQN x hm)
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
  have hzEq := deepCorner_reflect (by omega) hzD
  have hwEq := deepCorner_reflect (by omega) hwD
  rw [hzL] at hzEq
  rw [hwL] at hwEq
  have hzN := neighbors z hzF hzD
  have hwN := neighbors w hwF hwD
  rw [hzEq] at hzF hzN
  rw [hwEq] at hwF hwN
  obtain ⟨P⟩ := corner_packet_of_neighbor (by omega) F hEmpty u.1 v.1 huS hvS huv hcover hzF hzN
  obtain ⟨R⟩ := corner_packet_of_neighbor (by omega) F hEmpty v.1 u.1 hvS huS huv.symm
    (fun x hx hxb => (hcover x hx hxb).imp_right Or.symm) hwF hwN
  exact two_corner_packets_false (by omega) _ hacyc hbase huv P R

end GridGraphs.BoundarySix.Connected
