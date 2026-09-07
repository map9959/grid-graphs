import GridGraphs.Accounting.BoundarySix.Connected.TwoGaps

/-! # The two gaps belong to distinct corners

Each of the four actual corner cells requires a near-corner hole. Since the
two-gap classification leaves exactly four such holes, the corner labels are
bijective. In particular the two distinct matched witnesses belong to different
corners, without normalizing any of their orientations.
-/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

/-- On Near and Second positions, this labels the associated outer corner. -/
def cornerLabel {n : Nat} (v : GridVertex n n) : Bool × Bool :=
  (decide (v.1.val < 3), decide (v.2.val < 3))

theorem near_hole_at_each_corner {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (l : Bool × Bool) : ∃ v ∈ (univ \ F).filter Near, cornerLabel v = l := by
  have diagonal (r c : Fin (n - 1)) :
      (cell00 r c ∉ F ∨ cell11 r c ∉ F) ∧ (cell01 r c ∉ F ∨ cell10 r c ∉ F) := by
    rcases grid_cell_has_unforced_edge r c hacyc with h | h | h | h
    · exact ⟨Or.inl h.1, Or.inl h.2⟩
    · exact ⟨Or.inr h.2, Or.inl h.1⟩
    · exact ⟨Or.inr h.1, Or.inr h.2⟩
    · exact ⟨Or.inl h.2, Or.inr h.1⟩
  let z : Fin (n - 1) := ⟨0, by omega⟩
  let last : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hlow : ¬ n - 2 < 3 := by omega
  have hlast : ¬ n - 2 + 1 < 3 := by omega
  rcases l with ⟨a, b⟩
  cases a <;> cases b
  · rcases (diagonal last last).2 with h | h
    · refine ⟨cell01 last last, mem_filter.mpr ⟨by simp [h], ?_⟩, ?_⟩
      · simp [Near, cell01, last]; omega
      · simp [cornerLabel, cell01, last, hlow, hlast]
    · refine ⟨cell10 last last, mem_filter.mpr ⟨by simp [h], ?_⟩, ?_⟩
      · simp [Near, cell10, last]; omega
      · simp [cornerLabel, cell10, last, hlow, hlast]
  · rcases (diagonal last z).1 with h | h
    · refine ⟨cell00 last z, mem_filter.mpr ⟨by simp [h], ?_⟩, ?_⟩
      · simp [Near, cell00, last, z]; omega
      · simp [cornerLabel, cell00, last, z, hlow]
    · refine ⟨cell11 last z, mem_filter.mpr ⟨by simp [h], ?_⟩, ?_⟩
      · simp [Near, cell11, last, z]; omega
      · simp [cornerLabel, cell11, last, z, hlast]
  · rcases (diagonal z last).1 with h | h
    · refine ⟨cell00 z last, mem_filter.mpr ⟨by simp [h], ?_⟩, ?_⟩
      · simp [Near, cell00, last, z]; omega
      · simp [cornerLabel, cell00, last, z, hlow]
    · refine ⟨cell11 z last, mem_filter.mpr ⟨by simp [h], ?_⟩, ?_⟩
      · simp [Near, cell11, last, z]; omega
      · simp [cornerLabel, cell11, last, z, hlast]
  · rcases (diagonal z z).2 with h | h
    · refine ⟨cell01 z z, mem_filter.mpr ⟨by simp [h], ?_⟩, ?_⟩
      · simp [Near, cell01, z]
      · simp [cornerLabel, cell01, z]
    · refine ⟨cell10 z z, mem_filter.mpr ⟨by simp [h], ?_⟩, ?_⟩
      · simp [Near, cell10, z]
      · simp [cornerLabel, cell10, z]

/-- Every neighbor of a Near witness has the same corner label. -/
theorem neighbor_near_same_corner {n : Nat} (hn : 9 ≤ n) {u q : GridVertex n n}
    (hq : Near q) (huq : (gridGraph n n).Adj u q) :
    cornerLabel u = cornerLabel q := by
  simp only [gridGraph, adjacent, Fin.ext_iff] at huq
  dsimp only [Near] at hq
  apply Prod.ext <;> simp [cornerLabel] <;> omega

/-- Four near-corner holes give one hole per corner, not merely four unrelated
Near positions. This is certified by the four unit-cell witnesses. -/
theorem four_near_holes_distinct_labels {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hcard : ((univ \ F).filter Near).card = 4)
    {q r : GridVertex n n} (hq : q ∉ F) (hr : r ∉ F) (hqN : Near q) (hrN : Near r)
    (he : cornerLabel q = cornerLabel r) : q = r := by
  let S := (univ \ F).filter Near
  let f (v : S) := cornerLabel v.1
  have hs : Function.Surjective f := by
    intro l
    obtain ⟨v, hv, he⟩ := near_hole_at_each_corner hn F hacyc l
    exact ⟨⟨v, hv⟩, he⟩
  have hc : Fintype.card S = Fintype.card (Bool × Bool) := by
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool] using hcard
  have hi := ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hs, hc⟩).1
  have hqS : q ∈ S := mem_filter.mpr ⟨by simp [hq], hqN⟩
  have hrS : r ∈ S := mem_filter.mpr ⟨by simp [hr], hrN⟩
  exact congrArg Subtype.val (hi (a₁ := ⟨q, hqS⟩) (a₂ := ⟨r, hrS⟩) he)

/-- Exact endpoint two-gap classification, including the distinct corners.
The perimeter edge set is the actual omitted edge finset. -/
theorem current_endpoint_two_distinct_corner_gaps {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6) :
    ∃ (Q : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
      (u v q r : PerimeterVertex (3 * k + 2)),
      Q.card = 4 ∧ (∀ z ∈ Q, Near z) ∧ q.1 ∈ Q ∧ r.1 ∈ Q ∧
      Second u.1 ∧ Second v.1 ∧ cornerLabel u.1 ≠ cornerLabel v.1 ∧
      (gridGraph (3 * k + 2) (3 * k + 2)).Adj u.1 q.1 ∧
      (gridGraph (3 * k + 2) (3 * k + 2)).Adj v.1 r.1 ∧
      (univ \ F).filter IsGridBoundary = insert u.1 (insert v.1 Q) ∧
      perimeterHoles F = {s(u, q), s(v, r)} := by
  obtain ⟨hEmpty, hcorners⟩ := current_endpoint_empty_ring_and_preserved_corners hk hmod F hacyc hf hb
  obtain ⟨_, _, hprofiles⟩ := current_upper_endpoint_profiles hk hmod F hacyc hf
  have hrc : Fintype.card (Carrier F) = k + 4 ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent = 1 := by
    change Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 4 ∧ _
    omega
  have hp := (endpoint_carrier_partition hk hmod F hacyc hf hrc.1).1
  obtain ⟨Q, u, v, q, r, hQcard, hQN, _, _, _, hqQ, hrQ, hqr, huS, hvS, huq, hvr, hB, hE⟩ :=
    two_gap_classification (by omega) F hacyc hb hp hrc.2 hEmpty hcorners
  have hQeq : (univ \ F).filter Near = Q := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzU, hzN⟩ := mem_filter.mp hz
      have hzb : IsGridBoundary z := by unfold Near IsGridBoundary at *; omega
      have hzB := mem_filter.mpr ⟨hzU, hzb⟩
      rw [hB] at hzB
      rcases mem_insert.mp hzB with he | hzB
      · have h : Near u.1 := he ▸ hzN
        dsimp only [Near, Second] at h huS
        omega
      · rcases mem_insert.mp hzB with he | hzQ
        · have h : Near v.1 := he ▸ hzN
          dsimp only [Near, Second] at h hvS
          omega
        · exact hzQ
    · intro hz
      have hzB : z ∈ (univ \ F).filter IsGridBoundary := by rw [hB]; simp [hz]
      exact mem_filter.mpr ⟨(mem_filter.mp hzB).1, hQN z hz⟩
  have hqU : q.1 ∉ F := by
    have hm : q.1 ∈ (univ \ F).filter Near := by rw [hQeq]; exact hqQ
    exact (mem_sdiff.mp (mem_filter.mp hm).1).2
  have hrU : r.1 ∉ F := by
    have hm : r.1 ∈ (univ \ F).filter Near := by rw [hQeq]; exact hrQ
    exact (mem_sdiff.mp (mem_filter.mp hm).1).2
  have huLabel := neighbor_near_same_corner (by omega) (hQN q.1 hqQ) huq
  have hvLabel := neighbor_near_same_corner (by omega) (hQN r.1 hrQ) hvr
  refine ⟨Q, u, v, q, r, hQcard, hQN, hqQ, hrQ, huS, hvS, ?_, huq, hvr, hB, hE⟩
  intro he
  apply hqr
  apply Subtype.ext
  exact four_near_holes_distinct_labels (by omega) F hacyc (by rw [hQeq]; exact hQcard)
    hqU hrU (hQN q.1 hqQ) (hQN r.1 hrQ) (huLabel.symm.trans (he.trans hvLabel))

end GridGraphs.BoundarySix.Connected
