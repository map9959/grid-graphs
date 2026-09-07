import GridGraphs.Accounting.BoundarySix.Witnesses

namespace GridGraphs.BoundarySix

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- Weighted boundary accounting, including the possible complementary corner.
The single-extra case permits a corner; two distinct extras must be noncorners. -/
theorem decomposition {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6) :
    (∃ u : GridVertex n n, (Corner u ∨ Second u) ∧
      ∀ x, x ∉ F → IsGridBoundary x → Near x ∨ x = u) ∨
    (∃ u v : GridVertex n n, ¬ Corner u ∧ ¬ Corner v ∧
      (Second u ∨ Second v ∨ (gridGraph n n).Adj u v) ∧
      ∀ x, x ∉ F → IsGridBoundary x → Near x ∨ x = u ∨ x = v) := by
  classical
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := corner_witnesses hn F hacyc
  let B := (univ \ F).filter (fun v => IsGridBoundary v)
  have hQB : Q ⊆ B := by
    intro x hx
    refine mem_filter.mpr ⟨hQU hx, ?_⟩
    have h := hQnear x hx
    unfold Near IsGridBoundary at *
    omega
  have hBcard : B.card ≤ 6 := by
    calc
      B.card = ∑ _x ∈ B, 1 := by simp
      _ ≤ ∑ x ∈ B, gridBoundaryDeficiency n n x := sum_le_sum (fun x hx =>
        one_le_gridBoundaryDeficiency_of_boundary (by omega) (by omega) x
          (mem_filter.mp hx).2)
      _ ≤ boundaryDeficiencySum n n (univ \ F) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by simp)
      _ = 6 := hb
  have hQsum : 4 ≤ ∑ x ∈ Q, gridBoundaryDeficiency n n x := by
    calc
      4 = ∑ _x ∈ Q, 1 := by simp [hQcard]
      _ ≤ _ := sum_le_sum (fun x hx =>
        one_le_gridBoundaryDeficiency_of_boundary (by omega) (by omega) x
          (mem_filter.mp (hQB hx)).2)
  have hEcard : (B \ Q).card ≤ 2 := by
    rw [card_sdiff_of_subset hQB]
    omega
  have independent {a b : GridVertex n n} (ha : Near a) (hb : Near b) :
      ¬ (gridGraph n n).Adj a b := by
    simp only [gridGraph, adjacent, Fin.ext_iff]
    unfold Near at *
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
  have hE : (B \ Q).Nonempty := by
    by_cases haQ : a ∈ Q
    · refine ⟨b, mem_sdiff.mpr ⟨hbB, ?_⟩⟩
      exact fun hbQ => independent (hQnear a haQ) (hQnear b hbQ) hab.1
    · exact ⟨a, mem_sdiff.mpr ⟨haB, haQ⟩⟩
  obtain ⟨u, hu⟩ := hE
  have huB := (mem_sdiff.mp hu).1
  have huQ := (mem_sdiff.mp hu).2
  have huBoundary := (mem_filter.mp huB).2
  by_cases hsingle : ∀ v ∈ B \ Q, v = u
  · have cover (x : GridVertex n n) (hx : x ∈ B) : Near x ∨ x = u := by
      by_cases hxQ : x ∈ Q
      · exact Or.inl (hQnear x hxQ)
      · exact Or.inr (hsingle x (mem_sdiff.mpr ⟨hx, hxQ⟩))
    have htype : Corner u ∨ Second u := by
      rcases cover a haB with ha | rfl <;> rcases cover b hbB with hb | rfl
      · exact False.elim (independent ha hb hab.1)
      · exact neighbor_near hn huBoundary ha hab.1.symm
      · exact neighbor_near hn huBoundary hb hab.1
      · exact False.elim (hab.1.ne rfl)
    exact Or.inl ⟨u, htype, fun x hx hxb => cover x (mem_filter.mpr ⟨by simp [hx], hxb⟩)⟩
  · push Not at hsingle
    obtain ⟨v, hv, hvu⟩ := hsingle
    have hvB := (mem_sdiff.mp hv).1
    have hvQ := (mem_sdiff.mp hv).2
    have hvBoundary := (mem_filter.mp hvB).2
    have hrest : B \ Q = {u, v} := by
      symm
      apply eq_of_subset_of_card_le
      · exact insert_subset hu (singleton_subset_iff.mpr hv)
      · simpa [hvu.symm] using hEcard
    have cover (x : GridVertex n n) (hx : x ∈ B) : Near x ∨ x = u ∨ x = v := by
      by_cases hxQ : x ∈ Q
      · exact Or.inl (hQnear x hxQ)
      · have H : x ∈ B \ Q := mem_sdiff.mpr ⟨hx, hxQ⟩
        rw [hrest] at H
        exact Or.inr (by simpa using H)
    have hsub : insert v (insert u Q) ⊆ univ \ F :=
      insert_subset (mem_filter.mp hvB).1 (insert_subset (mem_filter.mp huB).1 hQU)
    have hsum := sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => Nat.zero_le _) (f := fun x => gridBoundaryDeficiency n n x)
    rw [sum_insert (by simp [hvu, hvQ]), sum_insert huQ] at hsum
    change gridBoundaryDeficiency n n v + (gridBoundaryDeficiency n n u +
      ∑ x ∈ Q, gridBoundaryDeficiency n n x) ≤
      boundaryDeficiencySum n n (univ \ F) at hsum
    have hupos := one_le_gridBoundaryDeficiency_of_boundary (by omega) (by omega) u huBoundary
    have hvpos := one_le_gridBoundaryDeficiency_of_boundary (by omega) (by omega) v hvBoundary
    have corner_weight (x : GridVertex n n) (hx : Corner x) :
        gridBoundaryDeficiency n n x = 2 := by
      unfold gridBoundaryDeficiency
      rw [gridGraph_degree_corner (by omega) (by omega) x hx.1 hx.2]
    have huc : ¬ Corner u := by intro H; have := corner_weight u H; omega
    have hvc : ¬ Corner v := by intro H; have := corner_weight v H; omega
    have htype : Second u ∨ Second v ∨ (gridGraph n n).Adj u v := by
      rcases cover a haB with ha | rfl | rfl <;>
        rcases cover b hbB with hb | rfl | rfl
      · exact False.elim (independent ha hb hab.1)
      · exact Or.inl ((neighbor_near hn huBoundary ha hab.1.symm).resolve_left huc)
      · exact Or.inr (Or.inl ((neighbor_near hn hvBoundary ha hab.1.symm).resolve_left hvc))
      · exact Or.inl ((neighbor_near hn huBoundary hb hab.1).resolve_left huc)
      · exact False.elim (hab.1.ne rfl)
      · exact Or.inr (Or.inr hab.1)
      · exact Or.inr (Or.inl ((neighbor_near hn hvBoundary hb hab.1).resolve_left hvc))
      · exact Or.inr (Or.inr hab.1.symm)
      · exact False.elim (hab.1.ne rfl)
    exact Or.inr ⟨u, v, huc, hvc, htype, fun x hx hxb =>
      cover x (mem_filter.mpr ⟨by simp [hx], hxb⟩)⟩

end GridGraphs.BoundarySix
