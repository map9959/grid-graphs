import GridGraphs.Results.SmallDiagonalExact.AttachmentFive

/-!
# Four rotated attachment exclusions in the `5 x 5` grid

Each possible side attachment forces an explicit six-cycle, contradicting acyclicity.
-/

namespace GridGraphs.SmallDiagonalProof

open Finset SimpleGraph

lemma final_profile_attachment_top_impossible
    (F : Finset (GridVertex 5 5))
    (hxOutside : F \ boundary55 = {((1, 2) : GridVertex 5 5)})
    (hxF : ((1, 2) : GridVertex 5 5) ∈ F)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hcorners : corners55 ⊆ F)
    (homit00 : (0, 1) ∉ F ∨ (1, 0) ∉ F)
    (homit04 : (0, 3) ∉ F ∨ (1, 4) ∉ F)
    (homit44 : (3, 4) ∉ F ∨ (4, 3) ∉ F)
    (homit40 : (4, 1) ∉ F ∨ (3, 0) ∉ F)
    (hruns : boundaryForcedRunCount55 F = 3)
    (hdegree : ((gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))).degree
      ⟨(1, 2), hxF⟩ = 1) : False := by
  classical
  let x : GridVertex 5 5 := (1, 2)
  let b : GridVertex 5 5 := (0, 2)
  let H := (gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))
  have hbF : b ∈ F := by
    have hpos : 0 < H.degree ⟨x, hxF⟩ := by
      change 0 < ((gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))).degree
        ⟨(1, 2), hxF⟩
      rw [hdegree]
      norm_num
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    have hxy : (gridGraph 5 5).Adj x y.1 := by
      simpa [H, SimpleGraph.mem_neighborFinset] using hy
    have hyBoundary : y.1 ∈ boundary55 := by
      by_contra hyNotBoundary
      have hyOutside : y.1 ∈ F \ boundary55 :=
        Finset.mem_sdiff.mpr ⟨y.2, hyNotBoundary⟩
      have hyx : y.1 = x := by simpa [hxOutside, x] using hyOutside
      exact (gridGraph 5 5).ne_of_adj hxy hyx.symm
    have hyb : y.1 = b := by
      change adjacent 5 5 x y.1 at hxy
      simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and] at hyBoundary
      dsimp [x] at hxy
      dsimp [b]
      rcases hxy with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
        rcases hyBoundary with h | h | h | h <;>
        apply Prod.ext <;> apply Fin.ext <;> norm_num at hr hc h ⊢ <;> omega
    simpa [hyb] using y.2
  have h01not : ((0, 1) : GridVertex 5 5) ∉ F := by
    rcases homit00 with h | h
    · exact h
    · by_contra h01
      have hp := forced_two_edge_walk_parallel hacyc hxF hbF h01
        (by simp [gridGraph, adjacent, b]) (by simp [gridGraph, adjacent, b])
      rcases hp with hp | hp <;> norm_num [x, b] at hp
      omega
  have h03not : ((0, 3) : GridVertex 5 5) ∉ F := by
    rcases homit04 with h | h
    · exact h
    · by_contra h03
      have hp := forced_two_edge_walk_parallel hacyc hxF hbF h03
        (by simp [gridGraph, adjacent, b]) (by simp [gridGraph, adjacent, b])
      rcases hp with hp | hp <;> norm_num [x, b] at hp
      omega
  let q2 : Fin 16 := if (3, 4) ∈ F then 9 else 7
  let q3 : Fin 16 := if (4, 1) ∈ F then 13 else 11
  let Q : Finset (Fin 16) := {1, 3, q2, q3}
  have hq2 : q2 = 7 ∨ q2 = 9 := by
    by_cases h : (3, 4) ∈ F <;> simp [q2, h]
  have hq3 : q3 = 11 ∨ q3 = 13 := by
    by_cases h : (4, 1) ∈ F <;> simp [q3, h]
  have hq2omit : boundaryVertex55 q2 ∉ F := by
    dsimp [q2]
    split_ifs with h
    · rcases homit44 with h' | h'
      · exact (h' h).elim
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hq3omit : boundaryVertex55 q3 ∉ F := by
    dsimp [q3]
    split_ifs with h
    · rcases homit40 with h' | h'
      · exact (h' h).elim
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hQcard : Q.card = 4 := by
    rcases hq2 with hq2 | hq2 <;> rcases hq3 with hq3 | hq3 <;>
      simp [Q, hq2, hq3]
  have hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | hq | hq
    · simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h01not
    · simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h03not
    · subst q
      simpa [boundaryForcedPositions55] using hq2omit
    · subst q
      simpa [boundaryForcedPositions55] using hq3omit
  have hQodd : ∀ q ∈ Q, q.val % 2 = 1 := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | hq | hq
    · norm_num
    · norm_num
    · rw [hq]
      rcases hq2 with hq2 | hq2 <;> simp [hq2]
    · rw [hq]
      rcases hq3 with hq3 | hq3 <;> simp [hq3]
  have hcornerPositions : ∀ i : Fin 16, i.val % 4 = 0 →
      i ∈ boundaryForcedPositions55 F := by
    intro i hi
    have hiCases : i = 0 ∨ i = 4 ∨ i = 8 ∨ i = 12 := by
      have hiVal : i.val = 0 ∨ i.val = 4 ∨ i.val = 8 ∨ i.val = 12 := by omega
      rcases hiVal with h | h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
    rcases hiCases with rfl | rfl | rfl | rfl <;>
      simp only [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] <;> apply hcorners <;> simp [corners55]
  obtain ⟨e, heO, heQ, heMid, hePrev, heNext⟩ :=
    fifth_boundary_omission_is_side_midpoint_of_three_runs F Q hacyc hPcard
      hQcard hQomit hQodd hcornerPositions hruns
  have he : e = 10 := by
    have hbP : (2 : Fin 16) ∈ boundaryForcedPositions55 F := by
      simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength, b] using hbF
    have heCases : e = 2 ∨ e = 6 ∨ e = 10 ∨ e = 14 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at heMid
      rcases heMid with h | h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
    rcases heCases with rfl | rfl | rfl | rfl
    · exact ((Finset.mem_sdiff.mp heO).2 hbP).elim
    · have : (5 : Fin 16) ∈ Q := by simpa using hePrev
      rcases hq2 with hq2 | hq2 <;> rcases hq3 with hq3 | hq3 <;>
        simp [Q, hq2, hq3] at this
    · rfl
    · have : (15 : Fin 16) ∈ Q := by simpa using heNext
      rcases hq2 with hq2 | hq2 <;> rcases hq3 with hq3 | hq3 <;>
        simp [Q, hq2, hq3] at this
  have h15F : ((1, 0) : GridVertex 5 5) ∈ F := by
    by_contra h15
    have h15O : (15 : Fin 16) ∈ (Finset.univ : Finset (Fin 16)) \
        boundaryForcedPositions55 F := by
      simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h15
    have hOcard : ((Finset.univ : Finset (Fin 16)) \
        boundaryForcedPositions55 F).card = 5 := by
      simp [Finset.card_sdiff, hPcard]
    have h15Q : (15 : Fin 16) ∉ Q := by
      rcases hq2 with hq2 | hq2 <;> rcases hq3 with hq3 | hq3 <;>
        simp [Q, hq2, hq3]
    have hdiffCard : (((Finset.univ : Finset (Fin 16)) \
        boundaryForcedPositions55 F) \ Q).card = 1 := by
      rw [Finset.card_sdiff_of_subset hQomit, hOcard, hQcard]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hdiffCard
    have heDiff : e ∈ ((Finset.univ : Finset (Fin 16)) \
        boundaryForcedPositions55 F) \ Q := Finset.mem_sdiff.mpr ⟨heO, heQ⟩
    have h15Diff : (15 : Fin 16) ∈ ((Finset.univ : Finset (Fin 16)) \
        boundaryForcedPositions55 F) \ Q := Finset.mem_sdiff.mpr ⟨h15O, h15Q⟩
    rw [ha] at heDiff h15Diff
    simp only [Finset.mem_singleton] at heDiff h15Diff
    have h15e : (15 : Fin 16) = e := h15Diff.trans heDiff.symm
    rw [he] at h15e
    have := congrArg Fin.val h15e
    norm_num at this
  have h00F : ((0, 0) : GridVertex 5 5) ∈ F := hcorners (by simp [corners55])
  exact forced_six_cycle_false F hacyc x b (0, 1) (0, 0) (1, 0) (1, 1)
    (by simp [x, b])
    (by simp [gridGraph, adjacent, x, b])
    (by simp [gridGraph, adjacent, b])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent, x]) hxF hbF h00F h15F

lemma final_profile_attachment_right_impossible
    (F : Finset (GridVertex 5 5))
    (hxOutside : F \ boundary55 = {((2, 3) : GridVertex 5 5)})
    (hxF : ((2, 3) : GridVertex 5 5) ∈ F)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hcorners : corners55 ⊆ F)
    (homit00 : (0, 1) ∉ F ∨ (1, 0) ∉ F)
    (homit40 : (4, 1) ∉ F ∨ (3, 0) ∉ F)
    (hruns : boundaryForcedRunCount55 F = 3)
    (hdegree : ((gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))).degree
      ⟨(2, 3), hxF⟩ = 1) : False := by
  classical
  let x : GridVertex 5 5 := (2, 3)
  let b : GridVertex 5 5 := (2, 4)
  have hbF : b ∈ F := attachment_boundary_neighbor_forced F x b hxOutside hxF
    (by simpa [x] using hdegree) (by
      intro y hxy hyB
      change adjacent 5 5 x y at hxy
      simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and] at hyB
      dsimp [x, b] at hxy ⊢
      rcases hxy with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
        rcases hyB with h | h | h | h <;>
        apply Prod.ext <;> apply Fin.ext <;> norm_num at hr hc h ⊢ <;> omega)
  have h14not : ((1, 4) : GridVertex 5 5) ∉ F := by
    intro h14
    have hp := forced_two_edge_walk_parallel hacyc hxF hbF h14
      (by simp [gridGraph, adjacent, b]) (by simp [gridGraph, adjacent, b])
    rcases hp with hp | hp <;> norm_num [x, b] at hp <;> omega
  have h34not : ((3, 4) : GridVertex 5 5) ∉ F := by
    intro h34
    have hp := forced_two_edge_walk_parallel hacyc hxF hbF h34
      (by simp [gridGraph, adjacent, b]) (by simp [gridGraph, adjacent, b])
    rcases hp with hp | hp <;> norm_num [x, b] at hp <;> omega
  let q0 : Fin 16 := if (1, 0) ∈ F then 1 else 15
  let q3 : Fin 16 := if (4, 1) ∈ F then 13 else 11
  let Q : Finset (Fin 16) := {q0, 5, 7, q3}
  have hq0 : q0 = 1 ∨ q0 = 15 := by
    by_cases h : (1, 0) ∈ F <;> simp [q0, h]
  have hq3 : q3 = 11 ∨ q3 = 13 := by
    by_cases h : (4, 1) ∈ F <;> simp [q3, h]
  have hq0omit : boundaryVertex55 q0 ∉ F := by
    dsimp [q0]
    split_ifs with h
    · rcases homit00 with h' | h'
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
      · exact (h' h).elim
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hq3omit : boundaryVertex55 q3 ∉ F := by
    dsimp [q3]
    split_ifs with h
    · rcases homit40 with h' | h'
      · exact (h' h).elim
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hQcard : Q.card = 4 := by
    rcases hq0 with hq0 | hq0 <;> rcases hq3 with hq3 | hq3 <;>
      simp [Q, hq0, hq3]
  have hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | rfl | rfl | hq
    · subst q; simpa [boundaryForcedPositions55] using hq0omit
    · simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h14not
    · simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h34not
    · subst q; simpa [boundaryForcedPositions55] using hq3omit
  have hQodd : ∀ q ∈ Q, q.val % 2 = 1 := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | rfl | rfl | hq
    · rw [hq]; rcases hq0 with hq0 | hq0 <;> simp [hq0]
    · norm_num
    · norm_num
    · rw [hq]; rcases hq3 with hq3 | hq3 <;> simp [hq3]
  have hcornerPositions : ∀ i : Fin 16, i.val % 4 = 0 →
      i ∈ boundaryForcedPositions55 F := by
    intro i hi
    have hiVal : i.val = 0 ∨ i.val = 4 ∨ i.val = 8 ∨ i.val = 12 := by omega
    have hiCases : i = 0 ∨ i = 4 ∨ i = 8 ∨ i = 12 := by
      rcases hiVal with h | h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
    rcases hiCases with rfl | rfl | rfl | rfl <;>
      simp only [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] <;> apply hcorners <;> simp [corners55]
  have h03F : ((0, 3) : GridVertex 5 5) ∈ F := by
    have h3P := odd_boundary_position_forced_of_three_runs F Q 3 hacyc hPcard
      hQcard hQomit hQodd hcornerPositions hruns (by norm_num) (by
        rcases hq0 with hq0 | hq0 <;> rcases hq3 with hq3 | hq3 <;>
          simp [Q, hq0, hq3])
    simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
      gridBoundaryVertex, gridBoundaryLength] using h3P
  have h04F : ((0, 4) : GridVertex 5 5) ∈ F := hcorners (by simp [corners55])
  exact forced_six_cycle_false F hacyc x b (1, 4) (0, 4) (0, 3) (1, 3)
    (by simp [x, b])
    (by simp [gridGraph, adjacent, x, b])
    (by simp [gridGraph, adjacent, b])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent, x]) hxF hbF h04F h03F

lemma final_profile_attachment_bottom_impossible
    (F : Finset (GridVertex 5 5))
    (hxOutside : F \ boundary55 = {((3, 2) : GridVertex 5 5)})
    (hxF : ((3, 2) : GridVertex 5 5) ∈ F)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5) (↑F : Set _)).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hcorners : corners55 ⊆ F)
    (homit00 : (0, 1) ∉ F ∨ (1, 0) ∉ F)
    (homit04 : (0, 3) ∉ F ∨ (1, 4) ∉ F)
    (hruns : boundaryForcedRunCount55 F = 3)
    (hdegree : ((gridGraph 5 5).induce (↑F : Set _)).degree
      ⟨(3, 2), hxF⟩ = 1) : False := by
  classical
  let x : GridVertex 5 5 := (3, 2)
  let b : GridVertex 5 5 := (4, 2)
  have hbF : b ∈ F := attachment_boundary_neighbor_forced F x b hxOutside hxF
    (by simpa [x] using hdegree) (by
      intro y hxy hyB
      change adjacent 5 5 x y at hxy
      simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and] at hyB
      dsimp [x, b] at hxy ⊢
      rcases hxy with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
        rcases hyB with h | h | h | h <;>
        apply Prod.ext <;> apply Fin.ext <;> norm_num at hr hc h ⊢ <;> omega)
  have h43not : ((4, 3) : GridVertex 5 5) ∉ F := by
    intro h43
    have hp := forced_two_edge_walk_parallel hacyc hxF hbF h43
      (by simp [gridGraph, adjacent, b]) (by simp [gridGraph, adjacent, b])
    rcases hp with hp | hp <;> norm_num [x, b] at hp <;> omega
  have h41not : ((4, 1) : GridVertex 5 5) ∉ F := by
    intro h41
    have hp := forced_two_edge_walk_parallel hacyc hxF hbF h41
      (by simp [gridGraph, adjacent, b]) (by simp [gridGraph, adjacent, b])
    rcases hp with hp | hp <;> norm_num [x, b] at hp <;> omega
  let q0 : Fin 16 := if (1, 0) ∈ F then 1 else 15
  let q1 : Fin 16 := if (1, 4) ∈ F then 3 else 5
  let Q : Finset (Fin 16) := {q0, q1, 9, 11}
  have hq0 : q0 = 1 ∨ q0 = 15 := by
    by_cases h : (1, 0) ∈ F <;> simp [q0, h]
  have hq1 : q1 = 3 ∨ q1 = 5 := by
    by_cases h : (1, 4) ∈ F <;> simp [q1, h]
  have hq0omit : boundaryVertex55 q0 ∉ F := by
    dsimp [q0]; split_ifs with h
    · rcases homit00 with h' | h'
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
      · exact (h' h).elim
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hq1omit : boundaryVertex55 q1 ∉ F := by
    dsimp [q1]; split_ifs with h
    · rcases homit04 with h' | h'
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
      · exact (h' h).elim
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hQcard : Q.card = 4 := by
    rcases hq0 with hq0 | hq0 <;> rcases hq1 with hq1 | hq1 <;>
      simp [Q, hq0, hq1]
  have hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | rfl | rfl
    · subst q; simpa [boundaryForcedPositions55] using hq0omit
    · subst q; simpa [boundaryForcedPositions55] using hq1omit
    · simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h43not
    · simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h41not
  have hQodd : ∀ q ∈ Q, q.val % 2 = 1 := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | rfl | rfl
    · rw [hq]; rcases hq0 with hq0 | hq0 <;> simp [hq0]
    · rw [hq]; rcases hq1 with hq1 | hq1 <;> simp [hq1]
    · norm_num
    · norm_num
  have h13F : ((3, 0) : GridVertex 5 5) ∈ F := by
    have h13P := odd_boundary_position_forced_of_three_runs F Q 13 hacyc hPcard
      hQcard hQomit hQodd (corner_boundary_positions_forced F hcorners) hruns
      (by norm_num) (by
        rcases hq0 with hq0 | hq0 <;> rcases hq1 with hq1 | hq1 <;>
          simp [Q, hq0, hq1])
    simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
      gridBoundaryVertex, gridBoundaryLength] using h13P
  have h40F : ((4, 0) : GridVertex 5 5) ∈ F := hcorners (by simp [corners55])
  exact forced_six_cycle_false F hacyc x b (4, 1) (4, 0) (3, 0) (3, 1)
    (by simp [x, b])
    (by simp [gridGraph, adjacent, x, b])
    (by simp [gridGraph, adjacent, b])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent, x]) hxF hbF h40F h13F

lemma final_profile_attachment_left_impossible
    (F : Finset (GridVertex 5 5))
    (hxOutside : F \ boundary55 = {((2, 1) : GridVertex 5 5)})
    (hxF : ((2, 1) : GridVertex 5 5) ∈ F)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5) (↑F : Set _)).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hcorners : corners55 ⊆ F)
    (homit04 : (0, 3) ∉ F ∨ (1, 4) ∉ F)
    (homit44 : (3, 4) ∉ F ∨ (4, 3) ∉ F)
    (hruns : boundaryForcedRunCount55 F = 3)
    (hdegree : ((gridGraph 5 5).induce (↑F : Set _)).degree
      ⟨(2, 1), hxF⟩ = 1) : False := by
  classical
  let x : GridVertex 5 5 := (2, 1)
  let b : GridVertex 5 5 := (2, 0)
  have hbF : b ∈ F := attachment_boundary_neighbor_forced F x b hxOutside hxF
    (by simpa [x] using hdegree) (by
      intro y hxy hyB
      change adjacent 5 5 x y at hxy
      simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and] at hyB
      dsimp [x, b] at hxy ⊢
      rcases hxy with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
        rcases hyB with h | h | h | h <;>
        apply Prod.ext <;> apply Fin.ext <;> norm_num at hr hc h ⊢ <;> omega)
  have h30not : ((3, 0) : GridVertex 5 5) ∉ F := by
    intro h30
    have hp := forced_two_edge_walk_parallel hacyc hxF hbF h30
      (by simp [gridGraph, adjacent, b]) (by simp [gridGraph, adjacent, b])
    rcases hp with hp | hp <;> norm_num [x, b] at hp
    omega
  have h10not : ((1, 0) : GridVertex 5 5) ∉ F := by
    intro h10
    have hp := forced_two_edge_walk_parallel hacyc hxF hbF h10
      (by simp [gridGraph, adjacent, b]) (by simp [gridGraph, adjacent, b])
    rcases hp with hp | hp <;> norm_num [x, b] at hp
    omega
  let q1 : Fin 16 := if (1, 4) ∈ F then 3 else 5
  let q2 : Fin 16 := if (4, 3) ∈ F then 7 else 9
  let Q : Finset (Fin 16) := {15, q1, q2, 13}
  have hq1 : q1 = 3 ∨ q1 = 5 := by
    by_cases h : (1, 4) ∈ F <;> simp [q1, h]
  have hq2 : q2 = 7 ∨ q2 = 9 := by
    by_cases h : (4, 3) ∈ F <;> simp [q2, h]
  have hq1omit : boundaryVertex55 q1 ∉ F := by
    dsimp [q1]; split_ifs with h
    · rcases homit04 with h' | h'
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
      · exact (h' h).elim
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hq2omit : boundaryVertex55 q2 ∉ F := by
    dsimp [q2]; split_ifs with h
    · rcases homit44 with h' | h'
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
      · exact (h' h).elim
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hQcard : Q.card = 4 := by
    rcases hq1 with hq1 | hq1 <;> rcases hq2 with hq2 | hq2 <;>
      simp [Q, hq1, hq2]
  have hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | hq | hq | rfl
    · simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h10not
    · subst q; simpa [boundaryForcedPositions55] using hq1omit
    · subst q; simpa [boundaryForcedPositions55] using hq2omit
    · simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h30not
  have hQodd : ∀ q ∈ Q, q.val % 2 = 1 := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | hq | hq | rfl
    · norm_num
    · rw [hq]; rcases hq1 with hq1 | hq1 <;> simp [hq1]
    · rw [hq]; rcases hq2 with hq2 | hq2 <;> simp [hq2]
    · norm_num
  have h41F : ((4, 1) : GridVertex 5 5) ∈ F := by
    have h11P := odd_boundary_position_forced_of_three_runs F Q 11 hacyc hPcard
      hQcard hQomit hQodd (corner_boundary_positions_forced F hcorners) hruns
      (by norm_num) (by
        rcases hq1 with hq1 | hq1 <;> rcases hq2 with hq2 | hq2 <;>
          simp [Q, hq1, hq2])
    simpa [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
      gridBoundaryVertex, gridBoundaryLength] using h11P
  have h40F : ((4, 0) : GridVertex 5 5) ∈ F := hcorners (by simp [corners55])
  exact forced_six_cycle_false F hacyc x b (3, 0) (4, 0) (4, 1) (3, 1)
    (by simp [x, b])
    (by simp [gridGraph, adjacent, x, b])
    (by simp [gridGraph, adjacent, b])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent, x]) hxF hbF h40F h41F

end GridGraphs.SmallDiagonalProof
