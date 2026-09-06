import GridGraphs.BoundaryFiveBudget

/-! # The first equality gate for boundary deficiency five -/

namespace GridGraphs

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000

private def IsCornerNeighbor {n : Nat} (v : GridVertex n n) : Prop :=
  ((v.1.val = 0 ∨ v.1.val + 1 = n) ∧ (v.2.val = 1 ∨ v.2.val + 2 = n)) ∨
  ((v.2.val = 0 ∨ v.2.val + 1 = n) ∧ (v.1.val = 1 ∨ v.1.val + 2 = n))

private theorem four_corner_cell_witnesses {n : Nat} (hn : 6 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    ∃ Q : Finset (GridVertex n n), Q.card = 4 ∧ Q ⊆ Finset.univ \ F ∧
      (∀ v ∈ Q, IsGridBoundary v) ∧
      (∀ v ∈ Q, ¬ ((v.1.val = 0 ∨ v.1.val + 1 = n) ∧
        (v.2.val = 0 ∨ v.2.val + 1 = n))) ∧
      (∀ x ∈ Q, ∀ y ∈ Q, ¬ (gridGraph n n).Adj x y) ∧
      (∀ v : GridVertex n n, IsGridBoundary v →
        ¬ ((v.1.val = 0 ∨ v.1.val + 1 = n) ∧
          (v.2.val = 0 ∨ v.2.val + 1 = n)) →
        ∀ x ∈ Q, ∀ y ∈ Q,
          (gridGraph n n).Adj v x → (gridGraph n n).Adj v y → x = y) ∧
      (∀ v ∈ Q, IsCornerNeighbor v) := by
  classical
  let a : GridVertex n n := (⟨0, by omega⟩, ⟨1, by omega⟩)
  let b : GridVertex n n := (⟨1, by omega⟩, ⟨0, by omega⟩)
  let c : GridVertex n n := (⟨0, by omega⟩, ⟨n - 2, by omega⟩)
  let d : GridVertex n n := (⟨1, by omega⟩, ⟨n - 1, by omega⟩)
  let e : GridVertex n n := (⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩)
  let f : GridVertex n n := (⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩)
  let g : GridVertex n n := (⟨n - 1, by omega⟩, ⟨1, by omega⟩)
  let h : GridVertex n n := (⟨n - 2, by omega⟩, ⟨0, by omega⟩)
  have hlast : n - 2 + 1 = n - 1 := by omega
  have h0 : a ∉ F ∨ b ∉ F := by
    have H := grid_cell_has_unforced_edge
      (⟨0, by omega⟩ : Fin (n - 1)) (⟨0, by omega⟩ : Fin (n - 1)) hacyc
    simp only [cell00, cell01, cell11, cell10, Finset.mem_coe] at H
    exact H.elim (fun H => Or.inl H.2) (fun H => H.elim
      (fun H => Or.inl H.1) (fun H => H.elim (fun H => Or.inr H.2) (fun H => Or.inr H.1)))
  have h1 : c ∉ F ∨ d ∉ F := by
    have H := grid_cell_has_unforced_edge
      (⟨0, by omega⟩ : Fin (n - 1)) (⟨n - 2, by omega⟩ : Fin (n - 1)) hacyc
    simp only [cell00, cell01, cell11, cell10, Finset.mem_coe, hlast] at H
    exact H.elim (fun H => Or.inl H.1) (fun H => H.elim
      (fun H => Or.inr H.2) (fun H => H.elim (fun H => Or.inr H.1) (fun H => Or.inl H.2)))
  have h2 : e ∉ F ∨ f ∉ F := by
    have H := grid_cell_has_unforced_edge
      (⟨n - 2, by omega⟩ : Fin (n - 1))
      (⟨n - 2, by omega⟩ : Fin (n - 1)) hacyc
    simp only [cell00, cell01, cell11, cell10, Finset.mem_coe, hlast] at H
    exact H.elim (fun H => Or.inl H.2) (fun H => H.elim
      (fun H => Or.inl H.1) (fun H => H.elim (fun H => Or.inr H.2) (fun H => Or.inr H.1)))
  have h3 : g ∉ F ∨ h ∉ F := by
    have H := grid_cell_has_unforced_edge
      (⟨n - 2, by omega⟩ : Fin (n - 1)) (⟨0, by omega⟩ : Fin (n - 1)) hacyc
    simp only [cell00, cell01, cell11, cell10, Finset.mem_coe, hlast] at H
    exact H.elim (fun H => Or.inr H.1) (fun H => H.elim
      (fun H => Or.inl H.2) (fun H => H.elim (fun H => Or.inl H.1) (fun H => Or.inr H.2)))
  have choose (x y : GridVertex n n) (hxy : x ∉ F ∨ y ∉ F) :
      ∃ q, (q = x ∨ q = y) ∧ q ∉ F := by
    rcases hxy with hx | hy
    · exact ⟨x, Or.inl rfl, hx⟩
    · exact ⟨y, Or.inr rfl, hy⟩
  obtain ⟨q0, hq0, hu0⟩ := choose a b h0
  obtain ⟨q1, hq1, hu1⟩ := choose c d h1
  obtain ⟨q2, hq2, hu2⟩ := choose e f h2
  obtain ⟨q3, hq3, hu3⟩ := choose g h h3
  let Q : Finset (GridVertex n n) := {q0, q1, q2, q3}
  have hQcard : Q.card = 4 := by
    rcases hq0 with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      rcases hq2 with rfl | rfl <;> rcases hq3 with rfl | rfl <;>
      simp only [Q, GridVertex, Finset.card_insert_eq_ite, Finset.card_singleton,
        Finset.mem_insert, Finset.mem_singleton, a, b, c, d, e, f, g, h,
        Prod.ext_iff, Fin.ext_iff] <;>
      split_ifs <;> omega
  have hQU : Q ⊆ Finset.univ \ F := by
    intro v hv
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> simp [hu0, hu1, hu2, hu3]
  have hQcoords (v : GridVertex n n) (hv : v ∈ Q) :
      v = a ∨ v = b ∨ v = c ∨ v = d ∨ v = e ∨ v = f ∨ v = g ∨ v = h := by
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hq0.elim Or.inl (fun H => Or.inr (Or.inl H))
    · exact Or.inr (Or.inr (hq1.elim Or.inl (fun H => Or.inr (Or.inl H))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (hq2.elim Or.inl (fun H => Or.inr (Or.inl H))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq3)))))
  have hQboundary (v : GridVertex n n) (hv : v ∈ Q) : IsGridBoundary v := by
    rcases hQcoords v hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [IsGridBoundary, a, b, c, d, e, f, g, h] <;> omega
  refine ⟨Q, hQcard, hQU, hQboundary, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases hQcoords v hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [a, b, c, d, e, f, g, h] <;> omega
  · intro x hx y hy
    rcases hQcoords x hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hQcoords y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gridGraph, adjacent, a, b, c, d, e, f, g, h] <;> omega
  · intro v hv hnc x hx y hy hvx hvy
    unfold IsGridBoundary at hv
    rcases hQcoords x hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hQcoords y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gridGraph, adjacent, Fin.ext_iff, a, b, c, d, e, f, g, h] at hvx hvy <;>
      simp [Prod.ext_iff, Fin.ext_iff, a, b, c, d, e, f, g, h] <;> omega
  · intro v hv
    rcases hQcoords v hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [IsCornerNeighbor, a, b, c, d, e, f, g, h] <;> omega

/-- At boundary deficiency five, every corner is forced and the complement
contains exactly five boundary vertices (all of them noncorners). -/
theorem boundaryDeficiencySum_compl_eq_five_corners_and_card {n : Nat} (hn : 6 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hbudget : boundaryDeficiencySum n n (Finset.univ \ F) = 5) :
    (∀ v : GridVertex n n,
      (v.1.val = 0 ∨ v.1.val + 1 = n) →
      (v.2.val = 0 ∨ v.2.val + 1 = n) → v ∈ F) ∧
    ((Finset.univ \ F).filter (fun v => IsGridBoundary v)).card = 5 := by
  classical
  obtain ⟨Q, hQcard, hQU, hQboundary, hQnoncorner, _, _⟩ :=
    four_corner_cell_witnesses hn F hacyc
  have hQsum : 4 ≤ ∑ x ∈ Q, gridBoundaryDeficiency n n x := by
    calc
      4 = ∑ _x ∈ Q, 1 := by simp [hQcard]
      _ ≤ _ := Finset.sum_le_sum (fun x hx =>
        one_le_gridBoundaryDeficiency_of_boundary (by omega) (by omega) x (hQboundary x hx))
  have hcorners (v : GridVertex n n)
      (hr : v.1.val = 0 ∨ v.1.val + 1 = n)
      (hc : v.2.val = 0 ∨ v.2.val + 1 = n) : v ∈ F := by
    by_contra hvF
    have hvQ : v ∉ Q := by
      intro hv
      exact hQnoncorner v hv ⟨hr, hc⟩
    have hvdef : gridBoundaryDeficiency n n v = 2 := by
      unfold gridBoundaryDeficiency
      rw [gridGraph_degree_corner (by omega) (by omega) v hr hc]
    have hsub : insert v Q ⊆ Finset.univ \ F :=
      Finset.insert_subset (by simp [hvF]) hQU
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => Nat.zero_le _) (f := fun x => gridBoundaryDeficiency n n x)
    rw [Finset.sum_insert hvQ, hvdef] at hle
    change 2 + (∑ x ∈ Q, gridBoundaryDeficiency n n x) ≤
      boundaryDeficiencySum n n (Finset.univ \ F) at hle
    omega
  refine ⟨hcorners, ?_⟩
  have hpoint (v : GridVertex n n) (hv : v ∈ Finset.univ \ F) :
      gridBoundaryDeficiency n n v = if IsGridBoundary v then 1 else 0 := by
    have hvF : v ∉ F := (Finset.mem_sdiff.mp hv).2
    have hnc : ¬ ((v.1.val = 0 ∨ v.1.val + 1 = n) ∧
        (v.2.val = 0 ∨ v.2.val + 1 = n)) :=
      fun h => hvF (hcorners v h.1 h.2)
    rw [gridBoundaryDeficiency_eq_four_side_indicators (by omega) (by omega)]
    unfold IsGridBoundary
    split_ifs <;> omega
  calc
    ((Finset.univ \ F).filter (fun v => IsGridBoundary v)).card =
        ∑ v ∈ Finset.univ \ F, (if IsGridBoundary v then 1 else 0) := by simp
    _ = boundaryDeficiencySum n n (Finset.univ \ F) :=
      Finset.sum_congr rfl (fun v hv => (hpoint v hv).symm)
    _ = 5 := hbudget

/-- The complementary boundary consists of four independent corner-cell
witnesses and one extra vertex, which has at most one neighbor among them. -/
theorem boundaryDeficiencySum_compl_eq_five_witness_decomposition
    {n : Nat} (hn : 6 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hbudget : boundaryDeficiencySum n n (Finset.univ \ F) = 5) :
    ∃ (Q : Finset (GridVertex n n)) (u : GridVertex n n),
      Q.card = 4 ∧ u ∉ Q ∧
      (Finset.univ \ F).filter (fun v => IsGridBoundary v) = insert u Q ∧
      (∀ x ∈ Q, ∀ y ∈ Q, ¬ (gridGraph n n).Adj x y) ∧
      (∀ x ∈ Q, ∀ y ∈ Q,
        (gridGraph n n).Adj u x → (gridGraph n n).Adj u y → x = y) := by
  classical
  obtain ⟨hcorners, hcard⟩ :=
    boundaryDeficiencySum_compl_eq_five_corners_and_card hn F hacyc hbudget
  obtain ⟨Q, hQcard, hQU, hQB, _, hQindependent, hQneighbor, _⟩ :=
    four_corner_cell_witnesses hn F hacyc
  let B := (Finset.univ \ F).filter (fun v => IsGridBoundary v)
  have hQBsub : Q ⊆ B := fun v hv => Finset.mem_filter.mpr ⟨hQU hv, hQB v hv⟩
  obtain ⟨u, huB, huQ⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show Q.card < B.card by change Q.card <
      ((Finset.univ \ F).filter (fun v => IsGridBoundary v)).card; omega)
  have hB : B = insert u Q := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.insert_subset huB hQBsub)
    rw [Finset.card_insert_of_notMem huQ, hQcard]
    exact hcard.le
  have huBoundary : IsGridBoundary u := (Finset.mem_filter.mp huB).2
  have huF : u ∉ F := (Finset.mem_sdiff.mp (Finset.mem_filter.mp huB).1).2
  refine ⟨Q, u, hQcard, huQ, hB, hQindependent, ?_⟩
  apply hQneighbor u huBoundary
  exact fun h => huF (hcorners u h.1 h.2)

/-- A feasible square-grid set with boundary deficiency five has exactly one
unordered perimeter edge with both endpoints in its complement. -/
theorem boundaryDeficiencySum_compl_eq_five_unique_perimeter_edge
    {n : Nat} (hn : 6 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hbudget : boundaryDeficiencySum n n (Finset.univ \ F) = 5) :
    ∃ e : Sym2 (GridVertex n n),
      (∃ u v, e = s(u, v) ∧ IsPerimeterEdge n u v ∧ u ∉ F ∧ v ∉ F) ∧
      ∀ x y, IsPerimeterEdge n x y → x ∉ F → y ∉ F → s(x, y) = e := by
  classical
  obtain ⟨Q, u, _, _, hB, hQindependent, hQneighbor⟩ :=
    boundaryDeficiencySum_compl_eq_five_witness_decomposition hn F hacyc hbudget
  -- Every complementary perimeter edge joins the extra vertex to a witness.
  have orient (x y : GridVertex n n) (hxy : IsPerimeterEdge n x y)
      (hx : x ∉ F) (hy : y ∉ F) :
      ∃ q ∈ Q, s(x, y) = s(u, q) ∧ (gridGraph n n).Adj u q := by
    have hxB : x ∈ insert u Q := by
      rw [← hB]
      exact Finset.mem_filter.mpr ⟨by simp [hx], hxy.2.1⟩
    have hyB : y ∈ insert u Q := by
      rw [← hB]
      exact Finset.mem_filter.mpr ⟨by simp [hy], hxy.2.2⟩
    rcases Finset.mem_insert.mp hxB with rfl | hxQ <;>
      rcases Finset.mem_insert.mp hyB with rfl | hyQ
    · exact False.elim (hxy.1.ne rfl)
    · exact ⟨y, hyQ, rfl, hxy.1⟩
    · exact ⟨x, hxQ, Sym2.eq_swap, hxy.1.symm⟩
    · exact False.elim (hQindependent x hxQ y hyQ hxy.1)
  obtain ⟨T, hFT, hTG, htree⟩ := SimpleGraph.isAcyclic_extends_to_isTree
    (forcedEdgeGraph_le (gridGraph n n) (↑F : Set _)) hacyc
    (gridGraph_connected (by omega) (by omega))
  let : DecidableRel T.Adj := Classical.decRel _
  obtain ⟨a, b, hab, hnot⟩ := exists_omitted_perimeter_edge (by omega : 2 ≤ n)
    (show IsSpanningSubtree (gridGraph n n) T from ⟨hTG, htree⟩)
  have ha : a ∉ F := fun ha => hnot (hFT ⟨hab.1, Or.inl ha⟩)
  have hb : b ∉ F := fun hb => hnot (hFT ⟨hab.1, Or.inr hb⟩)
  obtain ⟨q, hq, heq, huq⟩ := orient a b hab ha hb
  refine ⟨s(u, q), ⟨a, b, heq.symm, hab, ha, hb⟩, ?_⟩
  intro x y hxy hx hy
  obtain ⟨r, hr, her, hur⟩ := orient x y hxy hx hy
  have hrq : r = q := hQneighbor r hr q hq hur huq
  simpa only [hrq] using her

/-- On any outer side, two vertices separated by two grid steps cannot both
belong to the complement when the boundary deficiency is five. -/
theorem boundaryDeficiencySum_compl_eq_five_no_boundary_distance_two
    {n : Nat} (hn : 7 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hbudget : boundaryDeficiencySum n n (Finset.univ \ F) = 5)
    (x y : GridVertex n n)
    (hxy :
      (x.1.val = y.1.val ∧ (x.1.val = 0 ∨ x.1.val + 1 = n) ∧
        (x.2.val + 2 = y.2.val ∨ y.2.val + 2 = x.2.val)) ∨
      (x.2.val = y.2.val ∧ (x.2.val = 0 ∨ x.2.val + 1 = n) ∧
        (x.1.val + 2 = y.1.val ∨ y.1.val + 2 = x.1.val))) :
    x ∈ F ∨ y ∈ F := by
  classical
  by_contra hF
  have hxF : x ∉ F := fun h => hF (Or.inl h)
  have hyF : y ∉ F := fun h => hF (Or.inr h)
  obtain ⟨hcorners, hcard⟩ :=
    boundaryDeficiencySum_compl_eq_five_corners_and_card (by omega) F hacyc hbudget
  obtain ⟨Q, hQcard, hQU, hQB, _, hQindependent, _, hQnear⟩ :=
    four_corner_cell_witnesses (by omega) F hacyc
  let B := (Finset.univ \ F).filter (fun v => IsGridBoundary v)
  have hQBsub : Q ⊆ B := fun v hv => Finset.mem_filter.mpr ⟨hQU hv, hQB v hv⟩
  obtain ⟨u, huB, huQ⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show Q.card < B.card by change Q.card <
      ((Finset.univ \ F).filter (fun v => IsGridBoundary v)).card; omega)
  have hB : B = insert u Q := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.insert_subset huB hQBsub)
    rw [Finset.card_insert_of_notMem huQ, hQcard]
    exact hcard.le
  have huBoundary : IsGridBoundary u := (Finset.mem_filter.mp huB).2
  have huF : u ∉ F := (Finset.mem_sdiff.mp (Finset.mem_filter.mp huB).1).2
  have hunc : ¬ ((u.1.val = 0 ∨ u.1.val + 1 = n) ∧
      (u.2.val = 0 ∨ u.2.val + 1 = n)) :=
    fun h => huF (hcorners u h.1 h.2)
  have mem (v : GridVertex n n) (hv : v ∉ F) (hvB : IsGridBoundary v) :
      v = u ∨ v ∈ Q := by
    apply Finset.mem_insert.mp
    rw [← hB]
    exact Finset.mem_filter.mpr ⟨by simp [hv], hvB⟩
  obtain ⟨_, ⟨a, b, _, hab, ha, hb⟩, _⟩ :=
    boundaryDeficiencySum_compl_eq_five_unique_perimeter_edge (by omega) F hacyc hbudget
  have huneighbor : ∃ q ∈ Q, (gridGraph n n).Adj u q := by
    rcases mem a ha hab.2.1 with rfl | haQ <;>
      rcases mem b hb hab.2.2 with rfl | hbQ
    · exact False.elim (hab.1.ne rfl)
    · exact ⟨b, hbQ, hab.1⟩
    · exact ⟨a, haQ, hab.1.symm⟩
    · exact False.elim (hQindependent a haQ b hbQ hab.1)
  obtain ⟨q, hq, huq⟩ := huneighbor
  have hqnear := hQnear q hq
  have husecond :
      ((u.1.val = 0 ∨ u.1.val + 1 = n) ∧ (u.2.val = 2 ∨ u.2.val + 3 = n)) ∨
      ((u.2.val = 0 ∨ u.2.val + 1 = n) ∧ (u.1.val = 2 ∨ u.1.val + 3 = n)) := by
    unfold IsGridBoundary at huBoundary
    unfold IsCornerNeighbor at hqnear
    simp only [gridGraph, adjacent, Fin.ext_iff] at huq
    omega
  have hxB : IsGridBoundary x := by unfold IsGridBoundary; omega
  have hyB : IsGridBoundary y := by unfold IsGridBoundary; omega
  rcases mem x hxF hxB with rfl | hxQ <;>
    rcases mem y hyF hyB with rfl | hyQ
  · omega
  · have hynear := hQnear y hyQ
    unfold IsCornerNeighbor at hynear
    omega
  · have hxnear := hQnear x hxQ
    unfold IsCornerNeighbor at hxnear
    omega
  · have hxnear := hQnear x hxQ
    have hynear := hQnear y hyQ
    unfold IsCornerNeighbor at hxnear hynear
    omega

/-- At boundary deficiency five, the entire boundary of the once-cropped
square lies in the complement, for side length at least seven. -/
theorem boundaryDeficiencySum_compl_eq_five_next_ring_notMem
    {n : Nat} (hn : 7 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hbudget : boundaryDeficiencySum n n (Finset.univ \ F) = 5)
    (v : GridVertex n n)
    (hrlo : 1 ≤ v.1.val) (hrhi : v.1.val ≤ n - 2)
    (hclo : 1 ≤ v.2.val) (hchi : v.2.val ≤ n - 2)
    (hside : v.1.val = 1 ∨ v.1.val = n - 2 ∨
      v.2.val = 1 ∨ v.2.val = n - 2) : v ∉ F := by
  intro hvF
  have diagonal (r c : Fin (n - 1)) :
      (cell00 r c ∉ F ∨ cell11 r c ∉ F) ∧
      (cell01 r c ∉ F ∨ cell10 r c ∉ F) := by
    rcases grid_cell_has_unforced_edge r c hacyc with h | h | h | h
    · exact ⟨Or.inl h.1, Or.inl h.2⟩
    · exact ⟨Or.inr h.2, Or.inl h.1⟩
    · exact ⟨Or.inr h.1, Or.inr h.2⟩
    · exact ⟨Or.inl h.2, Or.inr h.1⟩
  have h00 (r c : Fin (n - 1)) (heq : cell11 r c = v) : cell00 r c ∉ F :=
    (diagonal r c).1.resolve_right (by simpa only [heq, not_not] using hvF)
  have h11 (r c : Fin (n - 1)) (heq : cell00 r c = v) : cell11 r c ∉ F :=
    (diagonal r c).1.resolve_left (by simpa only [heq, not_not] using hvF)
  have h01 (r c : Fin (n - 1)) (heq : cell10 r c = v) : cell01 r c ∉ F :=
    (diagonal r c).2.resolve_right (by simpa only [heq, not_not] using hvF)
  have h10 (r c : Fin (n - 1)) (heq : cell01 r c = v) : cell10 r c ∉ F :=
    (diagonal r c).2.resolve_left (by simpa only [heq, not_not] using hvF)
  let r : Fin (n - 1) := ⟨v.1.val, by omega⟩
  let c : Fin (n - 1) := ⟨v.2.val, by omega⟩
  let rm : Fin (n - 1) := ⟨v.1.val - 1, by omega⟩
  let cm : Fin (n - 1) := ⟨v.2.val - 1, by omega⟩
  let z : Fin (n - 1) := ⟨0, by omega⟩
  have separate := boundaryDeficiencySum_compl_eq_five_no_boundary_distance_two
    hn F hacyc hbudget
  rcases hside with htop | hbottom | hleft | hright
  · have hx := h00 z cm (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell11, z, cm] <;> omega)
    have hy := h01 z c (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell10, z, c]
      omega)
    apply (separate (cell00 z cm) (cell01 z c) ?_).elim hx hy
    left
    simp [cell00, cell01, z, cm, c]
    omega
  · have hx := h10 r cm (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell01, r, cm]
      omega)
    have hy := h11 r c (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell00, r, c])
    apply (separate (cell10 r cm) (cell11 r c) ?_).elim hx hy
    left
    simp [cell10, cell11, r, cm, c]
    omega
  · have hx := h00 rm z (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell11, rm, z] <;> omega)
    have hy := h10 r z (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell01, r, z]
      omega)
    apply (separate (cell00 rm z) (cell10 r z) ?_).elim hx hy
    right
    simp [cell00, cell10, rm, r, z]
    omega
  · have hx := h01 rm c (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell10, rm, c]
      omega)
    have hy := h11 r c (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell00, r, c])
    apply (separate (cell01 rm c) (cell11 r c) ?_).elim hx hy
    right
    simp [cell01, cell11, rm, r, c]
    omega

end GridGraphs
