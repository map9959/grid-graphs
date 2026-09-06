import GridGraphs.Geometry.Diagonal
import GridGraphs.Accounting.LinearWaste
import GridGraphs.Accounting.PerimeterWaste

/-! # Five units of boundary deficiency for feasible square-grid sets -/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- A feasible set in a square of side at least five leaves at least five
units of boundary deficiency in its complement. -/
theorem five_le_boundaryDeficiencySum_compl {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    5 ≤ boundaryDeficiencySum n n (Finset.univ \ F) := by
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
  have hQindependent (u v : GridVertex n n) (hu : u ∈ Q) (hv : v ∈ Q) :
      ¬(gridGraph n n).Adj u v := by
    rcases hQcoords u hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hQcoords v hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gridGraph, adjacent, a, b, c, d, e, f, g, h] <;> omega
  by_contra hbudget
  have hboundaryQ (v : GridVertex n n) (hvU : v ∈ Finset.univ \ F)
      (hvB : IsGridBoundary v) : v ∈ Q := by
    by_contra hvQ
    have hsub : insert v Q ⊆ Finset.univ \ F := Finset.insert_subset hvU hQU
    have hsum : (insert v Q).card ≤ boundaryDeficiencySum n n (Finset.univ \ F) := by
      calc
        (insert v Q).card = ∑ _x ∈ insert v Q, 1 := by simp
        _ ≤ ∑ x ∈ insert v Q, gridBoundaryDeficiency n n x := by
          apply Finset.sum_le_sum
          intro x hx
          apply one_le_gridBoundaryDeficiency_of_boundary (by omega) (by omega)
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hvB
          · exact hQboundary x hx
        _ ≤ boundaryDeficiencySum n n (Finset.univ \ F) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (by simp)
    rw [Finset.card_insert_of_notMem hvQ, hQcard] at hsum
    omega
  obtain ⟨T, hFT, hTG, htree⟩ := SimpleGraph.isAcyclic_extends_to_isTree
    (forcedEdgeGraph_le (gridGraph n n) (↑F : Set _)) hacyc
    (gridGraph_connected (by omega) (by omega))
  let : DecidableRel T.Adj := Classical.decRel _
  obtain ⟨u, v, huv, hnot⟩ := exists_omitted_perimeter_edge (by omega : 2 ≤ n)
    (show IsSpanningSubtree (gridGraph n n) T from ⟨hTG, htree⟩)
  have hu : u ∈ Finset.univ \ F := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hu
    exact hnot (hFT ⟨huv.1, Or.inl hu⟩)
  have hv : v ∈ Finset.univ \ F := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hv
    exact hnot (hFT ⟨huv.1, Or.inr hv⟩)
  exact hQindependent u v (hboundaryQ u hu huv.2.1)
    (hboundaryQ v hv huv.2.2) huv.1

/-- At the residue-two target cardinality, the induced feasible set has at
most `3*k + 6` connected components. -/
theorem induced_components_le_three_mul_add_six {k : Nat}
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hcard : F.card = 3 * k ^ 2 + 7 * k)
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) :
    Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent ≤ 3 * k + 6 := by
  classical
  by_cases hk : 1 ≤ k
  · have hbudget := five_le_boundaryDeficiencySum_compl (by omega) F hacyc
    have hledger := grid_component_reduction F hacyc
    have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
    have htotal := total_boundaryDeficiencySum
      (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
    have hforced : 1 ≤ Fintype.card
        (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
          (↑F : Set _)).ConnectedComponent := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨(forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).connectedComponentMk (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    rw [hcard] at hledger
    nlinarith
  · have hk0 : k = 0 := by omega
    subst k
    have hF : F = ∅ := Finset.card_eq_zero.mp (by simpa using hcard)
    subst F
    simp

/-- For `k >= 7`, no feasible target-cardinality set has at least `4*k`
induced components. -/
theorem not_feasible_target_of_four_mul_le_components {k : Nat} (hk : 7 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hcard : F.card = 3 * k ^ 2 + 7 * k)
    (hr : 4 * k ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent) :
    ¬(forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic := by
  intro hacyc
  have h := induced_components_le_three_mul_add_six F hcard hacyc
  omega

/-- For `k >= 6`, no feasible target-cardinality set has at least `4*k + 1`
induced components. -/
theorem not_feasible_target_of_four_mul_add_one_le_components {k : Nat} (hk : 6 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hcard : F.card = 3 * k ^ 2 + 7 * k)
    (hr : 4 * k + 1 ≤ Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent) :
    ¬(forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic := by
  intro hacyc
  have h := induced_components_le_three_mul_add_six F hcard hacyc
  omega

end GridGraphs
