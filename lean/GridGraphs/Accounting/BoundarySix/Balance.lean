import GridGraphs.Accounting.BoundarySix.NextRing
import GridGraphs.Constructions.BoundaryFive.BoundaryFiveConstruction

/-! # Numeric boundary and next-ring balance at deficiency six -/

namespace GridGraphs

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Four independent corner witnesses and a missing perimeter edge require
at least five actual complementary boundary vertices, without a budget assumption. -/
theorem five_le_compl_boundary_card {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    5 ≤ ((univ \ F).filter IsGridBoundary).card := by
  classical
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := BoundarySix.corner_witnesses hn F hacyc
  let B := (univ \ F).filter IsGridBoundary
  have hQB : Q ⊆ B := by
    intro x hx
    refine mem_filter.mpr ⟨hQU hx, ?_⟩
    have h := hQnear x hx
    unfold BoundarySix.Near IsGridBoundary at *
    omega
  obtain ⟨T, hFT, hTG, htree⟩ := SimpleGraph.isAcyclic_extends_to_isTree
    (forcedEdgeGraph_le (gridGraph n n) (↑F : Set _)) hacyc
    (gridGraph_connected (by omega) (by omega))
  let : DecidableRel T.Adj := Classical.decRel _
  obtain ⟨a, b, hab, hnot⟩ := exists_omitted_perimeter_edge (by omega : 2 ≤ n)
    (show IsSpanningSubtree (gridGraph n n) T from ⟨hTG, htree⟩)
  have haF : a ∉ F := fun ha => hnot (hFT ⟨hab.1, Or.inl ha⟩)
  have hbF : b ∉ F := fun hb => hnot (hFT ⟨hab.1, Or.inr hb⟩)
  have haB : a ∈ B := mem_filter.mpr ⟨by simp [haF], hab.2.1⟩
  have hbB : b ∈ B := mem_filter.mpr ⟨by simp [hbF], hab.2.2⟩
  have hextra : ∃ u ∈ B, u ∉ Q := by
    by_cases haQ : a ∈ Q
    · refine ⟨b, hbB, ?_⟩
      intro hbQ
      have ha := hQnear a haQ
      have hb := hQnear b hbQ
      have hadj := hab.1
      simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
      unfold BoundarySix.Near at ha hb
      omega
    · exact ⟨a, haB, haQ⟩
  obtain ⟨u, huB, huQ⟩ := hextra
  have hcard := card_le_card (insert_subset huB hQB)
  rw [card_insert_of_notMem huQ, hQcard] at hcard
  exact hcard

/-- A nonempty preserved next ring excludes complementary corners, so the six
units of deficiency are exactly six actual complementary boundary vertices. -/
theorem boundaryDeficiencySum_compl_eq_six_compl_boundary_card_of_next_ring_nonempty
    {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (hring : (F.filter IsNextRing).Nonempty) :
    ((univ \ F).filter IsGridBoundary).card = 6 := by
  classical
  obtain ⟨v, hv⟩ := hring
  obtain ⟨x, y, hx, hy, hxy⟩ := BoundarySix.preserved_gap hn F hacyc
    (mem_filter.mp hv).1 (mem_filter.mp hv).2
  have boundary {a b : GridVertex n n} (h : BoundarySix.Gap a b) : IsGridBoundary a := by
    unfold BoundarySix.Gap IsGridBoundary at *
    omega
  have hnc (z : GridVertex n n) (hz : z ∉ F) : ¬ BoundarySix.Corner z := by
    rcases BoundarySix.decomposition hn F hacyc hb with
      ⟨u, hu, cover⟩ | ⟨u, w, huc, hwc, _, cover⟩
    · have Hx := cover x hx (boundary hxy)
      have Hy := cover y hy (boundary (BoundarySix.gap_symm hxy))
      exfalso
      rcases Hx with Hx | rfl <;> rcases Hy with Hy | rfl
      · exact BoundarySix.near_not_gap hn Hx Hy hxy
      · rcases hu with hu | hu
        · exact BoundarySix.corner_not_gap_near hn hu Hx (BoundarySix.gap_symm hxy)
        · exact BoundarySix.second_not_gap_near hn hu Hx (BoundarySix.gap_symm hxy)
      · rcases hu with hu | hu
        · exact BoundarySix.corner_not_gap_near hn hu Hy hxy
        · exact BoundarySix.second_not_gap_near hn hu Hy hxy
      · unfold BoundarySix.Gap at hxy
        omega
    · intro hc
      have hzb : IsGridBoundary z := by
        unfold BoundarySix.Corner IsGridBoundary at *
        omega
      rcases cover z hz hzb with hzNear | rfl | rfl
      · unfold BoundarySix.Near BoundarySix.Corner at *
        omega
      · exact huc hc
      · exact hwc hc
  have hpoint (z : GridVertex n n) (hz : z ∈ univ \ F) :
      gridBoundaryDeficiency n n z = if IsGridBoundary z then 1 else 0 := by
    have H := hnc z (mem_sdiff.mp hz).2
    rw [gridBoundaryDeficiency_eq_four_side_indicators (by omega) (by omega)]
    unfold BoundarySix.Corner IsGridBoundary at *
    split_ifs <;> omega
  calc
    ((univ \ F).filter IsGridBoundary).card =
        ∑ z ∈ univ \ F, (if IsGridBoundary z then 1 else 0) := by simp
    _ = boundaryDeficiencySum n n (univ \ F) :=
      sum_congr rfl (fun z hz => (hpoint z hz).symm)
    _ = 6 := hb

/-- Actual complementary boundary counts absorb the preserved next-ring count. -/
theorem boundaryDeficiencySum_compl_eq_six_compl_boundary_balance
    {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6) :
    5 + (F.filter IsNextRing).card ≤ ((univ \ F).filter IsGridBoundary).card ∧
      ((univ \ F).filter IsGridBoundary).card ≤ 6 := by
  classical
  constructor
  · by_cases hr : (F.filter IsNextRing).Nonempty
    · rw [boundaryDeficiencySum_compl_eq_six_compl_boundary_card_of_next_ring_nonempty
        hn F hacyc hb hr]
      have := boundaryDeficiencySum_compl_eq_six_next_ring_card_le_one hn F hacyc hb
      omega
    · have hzero : (F.filter IsNextRing).card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hr)
      rw [hzero, Nat.add_zero]
      exact five_le_compl_boundary_card hn F hacyc
  · calc
      ((univ \ F).filter IsGridBoundary).card =
          ∑ _z ∈ (univ \ F).filter IsGridBoundary, 1 := by simp
      _ ≤ ∑ z ∈ (univ \ F).filter IsGridBoundary, gridBoundaryDeficiency n n z :=
        sum_le_sum (fun z hz => one_le_gridBoundaryDeficiency_of_boundary
          (by omega) (by omega) z (mem_filter.mp hz).2)
      _ ≤ boundaryDeficiencySum n n (univ \ F) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by simp)
      _ = 6 := hb

/-- Numeric boundary-six interface: a lower boundary count and a joint upper
bound for the preserved boundary and next ring. -/
theorem boundaryDeficiencySum_compl_eq_six_boundary_count_bounds
    {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6) :
    4 * n - 10 ≤ (F.filter IsGridBoundary).card ∧
      (F.filter IsGridBoundary).card + (F.filter IsNextRing).card ≤ 4 * n - 9 := by
  classical
  obtain ⟨hlower, hupper⟩ :=
    boundaryDeficiencySum_compl_eq_six_compl_boundary_balance hn F hacyc hb
  have hpartition : F.filter IsGridBoundary ∪ (univ \ F).filter IsGridBoundary =
      ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset := by
    ext v
    by_cases hv : v ∈ F <;> simp [hv]
  have hdisj : Disjoint (F.filter IsGridBoundary) ((univ \ F).filter IsGridBoundary) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp (mem_filter.mp hw).1).2 (mem_filter.mp hv).1
  have htotal := congrArg Finset.card hpartition
  rw [card_union_of_disjoint hdisj, BoundaryFiveConstruction.boundary_card (by omega)] at htotal
  omega

/-- At deficiency six at least `4*n-10` boundary vertices are preserved. -/
theorem boundaryDeficiencySum_compl_eq_six_boundary_card_lower
    {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6) :
    4 * n - 10 ≤ (F.filter IsGridBoundary).card :=
  (boundaryDeficiencySum_compl_eq_six_boundary_count_bounds hn F hacyc hb).1

/-- The preserved boundary and next ring together have at most `4*n-9` vertices. -/
theorem boundaryDeficiencySum_compl_eq_six_boundary_add_next_ring_card_le
    {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6) :
    (F.filter IsGridBoundary).card + (F.filter IsNextRing).card ≤ 4 * n - 9 :=
  (boundaryDeficiencySum_compl_eq_six_boundary_count_bounds hn F hacyc hb).2

end GridGraphs
