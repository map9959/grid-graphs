import GridGraphs.Accounting.CarrierLayers.FourCarrier.DeepExtension
import GridGraphs.Accounting.CarrierLayers.FourCarrier.Deficit

/-! # Connected missing sides with a root deficit require a shallow carrier

The argument uses one empty triple, including either end triple. It does not
need an a priori bound on the lengths of maximal gaps.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Fewer than `k` roots leave an actual empty charted triple block. -/
theorem exists_empty_chart_block {k : Nat} (hk : 1 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2))) (s : Fin 4)
    (hq : (F.filter (OnOpenSide s)).card < k) :
    ∃ i : Fin k, ∀ t : Fin (3 * k + 2), 3 * i.val + 1 ≤ t.val → t.val ≤ 3 * i.val + 3 →
      sideChart s (t, ⟨0, by omega⟩) ∉ F := by
  classical
  let I := (F.filter (OnOpenSide s)).image (fun v => (sidePosition s v - 1) / 3)
  have hI : I.card < k := card_image_le.trans_lt hq
  have hex : ∃ i < k, i ∉ I := by
    by_contra h
    push Not at h
    have hsub : range k ⊆ I := fun i hi => h i (mem_range.mp hi)
    have hle := card_le_card hsub
    rw [card_range] at hle
    omega
  obtain ⟨i, hi, hiI⟩ := hex
  refine ⟨⟨i, hi⟩, ?_⟩
  intro t hlo hhi hv
  dsimp only at hlo hhi
  apply hiI
  refine mem_image.mpr ⟨sideChart s (t, ⟨0, by omega⟩), mem_filter.mpr ⟨hv, ?_⟩, ?_⟩
  · apply (sideChart_openSide s _).mpr
    dsimp
    omega
  · rw [sideChart_position]
    dsimp
    omega

private theorem four_position_triple_false {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hzero : (nextRingCarriers F).card = 0)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent = 1)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (a : Nat) (ha : 1 ≤ a) (hb : a + 4 < n)
    (hm1 : sideChart s (⟨a + 1, by omega⟩, ⟨0, by omega⟩) ∉ F)
    (hm2 : sideChart s (⟨a + 2, by omega⟩, ⟨0, by omega⟩) ∉ F)
    (hend : sideChart s (⟨a, by omega⟩, ⟨0, by omega⟩) ∉ F ∨
      sideChart s (⟨a + 3, by omega⟩, ⟨0, by omega⟩) ∉ F) : False := by
  rcases hend with hleft | hright
  · have hmid := empty_chart_triple_inward hn F hc s a (by omega) hleft hm1 hm2
    by_cases hr : sideChart s (⟨a + 3, by omega⟩, ⟨0, by omega⟩) ∈ F
    · have hi := sideChart_root_inward hn F hacyc s hmissing
        (⟨a + 3, by omega⟩ : Fin n) (by dsimp; omega) hr
      exact close_inward_vertices_false_of_no_shallow hn F hacyc hzero s
        (a + 1) (a + 3) (by omega) (by omega) (by omega) (by omega) hmid hi
    · have hi := empty_chart_triple_inward hn F hc s (a + 1) (by omega)
        hm1 (by simpa only [Nat.add_assoc] using hm2) (by simpa only [Nat.add_assoc] using hr)
      exact close_inward_vertices_false_of_no_shallow hn F hacyc hzero s
        (a + 1) (a + 2) (by omega) (by omega) (by omega) (by omega) hmid hi
  · have hmid := empty_chart_triple_inward hn F hc s (a + 1) (by omega)
      hm1 (by simpa only [Nat.add_assoc] using hm2) (by simpa only [Nat.add_assoc] using hright)
    by_cases hl : sideChart s (⟨a, by omega⟩, ⟨0, by omega⟩) ∈ F
    · have hi := sideChart_root_inward hn F hacyc s hmissing
        (⟨a, by omega⟩ : Fin n) (by dsimp; omega) hl
      exact close_inward_vertices_false_of_no_shallow hn F hacyc hzero s
        a (a + 2) (by omega) (by omega) (by omega) (by omega) hi hmid
    · have hi := empty_chart_triple_inward hn F hc s a (by omega) hl hm1 hm2
      exact close_inward_vertices_false_of_no_shallow hn F hacyc hzero s
        (a + 1) (a + 2) (by omega) (by omega) (by omega) (by omega) hi hmid

/-- Any connected feasible missing-side configuration with fewer than `k`
roots has a shallow nonpure carrier. No score, corner, or off-side budget
hypothesis is needed. -/
theorem shallow_pos_of_connected_missing_side_root_deficit {k : Nat} (hk : 2 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hq : (F.filter (OnOpenSide s)).card < k)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 1) :
    1 ≤ (nextRingCarriers F).card := by
  by_contra h
  have hzero : (nextRingCarriers F).card = 0 := by omega
  obtain ⟨i, hi⟩ := exists_empty_chart_block (by omega) F s hq
  by_cases hlast : i.val + 1 = k
  · apply four_position_triple_false (by omega) F hacyc hzero hc s hmissing
      (3 * k - 3) (by omega) (by omega)
    · apply hi <;> dsimp <;> omega
    · apply hi <;> dsimp <;> omega
    · right
      apply hi <;> dsimp <;> omega
  · apply four_position_triple_false (by omega) F hacyc hzero hc s hmissing
      (3 * i.val + 1) (by omega) (by omega)
    · apply hi <;> dsimp <;> omega
    · apply hi <;> dsimp <;> omega
    · left
      apply hi <;> dsimp <;> omega

/-- The four-pure missing-side counterexample has exactly one shallow carrier
and exactly `k-1` carriers left for deep capacity. -/
theorem four_pure_missing_side_shallow_eq_one {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 4) :
    (nextRingCarriers F).card = 1 ∧
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent - (pureBoundaryCarriers F).card -
        (nextRingCarriers F).card = k - 1 := by
  obtain ⟨_, hq, hr, hc, _, hh⟩ := four_pure_missing_side_profile hk F hacyc s hmissing hf hp
  have hpos := shallow_pos_of_connected_missing_side_root_deficit (by omega) F hacyc s
    hmissing (by omega) hc
  omega

/-- The remaining four-pure missing-side branch has only five total physical
perimeter/deep deficit units. -/
theorem four_pure_missing_side_deficit_eq_five {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) (hp : (pureBoundaryCarriers F).card = 4) :
    (12 * k + 4 - ((F.filter IsGridBoundary).card + (F.filter IsNextRing).card)) +
      ((3 * k - 2) * (k - 1) -
        (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card) = 5 := by
  exact minimal_deep_one_excess_deficit hk F hacyc
    (four_pure_missing_side_profile hk F hacyc s hmissing hf hp).1
    (four_pure_missing_side_shallow_eq_one hk F hacyc s hmissing hf hp).2

end GridGraphs.CarrierLayers.FourCarrier
