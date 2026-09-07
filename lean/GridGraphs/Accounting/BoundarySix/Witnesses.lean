import GridGraphs.Accounting.BoundarySix.Geometry

namespace GridGraphs.BoundarySix

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- The four corner cells supply distinct, independent, noncorner holes.
This is the minimal corner-witness argument used in BoundaryFiveEquality. -/
theorem corner_witnesses {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    ∃ Q : Finset (GridVertex n n), Q.card = 4 ∧ Q ⊆ univ \ F ∧
      (∀ v ∈ Q, Near v) := by
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
      (⟨n - 2, by omega⟩ : Fin (n - 1)) (⟨n - 2, by omega⟩ : Fin (n - 1)) hacyc
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
        Prod.ext_iff, Fin.ext_iff] <;> split_ifs <;> omega
  refine ⟨Q, hQcard, ?_, ?_⟩
  · intro v hv
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> simp [hu0, hu1, hu2, hu3]
  · intro v hv
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · rcases hq0 with rfl | rfl <;> simp [Near, a, b]
    · rcases hq1 with rfl | rfl <;> simp [Near, c, d] <;> omega
    · rcases hq2 with rfl | rfl <;> simp [Near, e, f] <;> omega
    · rcases hq3 with rfl | rfl <;> simp [Near, g, h] <;> omega

end GridGraphs.BoundarySix
