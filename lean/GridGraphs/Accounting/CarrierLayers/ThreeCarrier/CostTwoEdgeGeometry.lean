import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoRods

/-! # Physical FF edge geometry for the enlarged rectangle

Rows are shifted by one for the mixed-packing interface. Vertical columns
include the root spokes and the next-ring/deep spokes; horizontal columns
include the shallow next-ring row.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- Opposite cell vertices cannot both be preserved, in either orientation. -/
theorem diagonal_preserved_false {n : Nat} (P : Set (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) P).IsAcyclic)
    (a b : GridVertex n n) (ha : a ∈ P) (hb : b ∈ P)
    (hx : a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val)
    (hy : a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val) : False := by
  let r : Fin (n - 1) := ⟨min a.1.val b.1.val, by omega⟩
  let c : Fin (n - 1) := ⟨min a.2.val b.2.val, by omega⟩
  have he : (a = cell00 r c ∧ b = cell11 r c) ∨
      (a = cell01 r c ∧ b = cell10 r c) ∨
      (b = cell00 r c ∧ a = cell11 r c) ∨
      (b = cell01 r c ∧ a = cell10 r c) := by
    simp only [Prod.ext_iff, Fin.ext_iff, cell00, cell01, cell11, cell10, r, c]
    omega
  have H := grid_cell_has_unforced_edge r c hacyc
  rcases he with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ | ⟨hb', ha'⟩ | ⟨hb', ha'⟩ <;>
    rw [ha'] at ha <;> rw [hb'] at hb <;> rcases H with H | H | H | H <;> tauto

/-- Columns of two depth-directed FF edges on one step are three-spaced. -/
theorem vertical_ff_spacing {n : Nat} (P : Set (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) P).IsAcyclic)
    (x z y : Nat) (hz : z < n) (hy : y + 1 < n) (hxz : x < z)
    (h00 : (⟨x, by omega⟩, ⟨y, by omega⟩) ∈ P)
    (h01 : (⟨x, by omega⟩, ⟨y + 1, by omega⟩) ∈ P)
    (h10 : (⟨z, hz⟩, ⟨y, by omega⟩) ∈ P)
    (h11 : (⟨z, hz⟩, ⟨y + 1, by omega⟩) ∈ P) : x + 3 ≤ z := by
  by_contra h
  have hcases : z = x + 1 ∨ z = x + 2 := by omega
  rcases hcases with he | he
  · exact diagonal_preserved_false P hacyc _ _ h00 h11 (Or.inl he.symm) (Or.inl rfl)
  · have h20 : (⟨x + 2, by omega⟩, ⟨y, by omega⟩) ∈ P := by simpa only [← he] using h10
    have h21 : (⟨x + 2, by omega⟩, ⟨y + 1, by omega⟩) ∈ P := by simpa only [← he] using h11
    exact forced_rectangle_two_rows_false (⟨x, by omega⟩ : Fin (n - 2))
      (⟨y, by omega⟩ : Fin (n - 1)) hacyc h00 h01 h20 h21

noncomputable def rectangleVerticalColumns {n : Nat} (F : Finset (GridVertex n n))
    (s : Fin 4) (t : Nat) : Finset Nat :=
  (Icc 2 (n - 3)).filter fun x => ∃ hx : x < n, ∃ ht : t < n,
    sideChart s (⟨x, hx⟩, ⟨t - 1, by omega⟩) ∈ F ∧ sideChart s (⟨x, hx⟩, ⟨t, ht⟩) ∈ F

noncomputable def rectangleHorizontalColumns {n : Nat} (F : Finset (GridVertex n n))
    (s : Fin 4) (r : Nat) : Finset Nat :=
  (Icc 2 (n - 4)).filter fun x => ∃ hx : x + 1 < n, ∃ hr : r - 1 < n,
    sideChart s (⟨x, by omega⟩, ⟨r - 1, hr⟩) ∈ F ∧
      sideChart s (⟨x + 1, hx⟩, ⟨r - 1, hr⟩) ∈ F

/-- Actual vertical edge-column sets satisfy the mixed rectangle's spacing
and eligible-column hypotheses on every step, including step one. -/
theorem cost_two_vertical_columns_eligible {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2)
    (t : Nat) (ht : t ∈ Icc 1 (3 * k - 1)) :
    (∀ x ∈ rectangleVerticalColumns F s t, ∀ z ∈ rectangleVerticalColumns F s t,
      x < z → x + 3 ≤ z) ∧
      rectangleVerticalColumns F s t ⊆ Icc 3 (3 * (k - 1) + 1) := by
  have ht' := mem_Icc.mp ht
  constructor
  · intro x hx z hz hxz
    obtain ⟨_, hx, htx, hx0, hx1⟩ := mem_filter.mp hx
    obtain ⟨_, hz, htz, hz0, hz1⟩ := mem_filter.mp hz
    have he : t - 1 + 1 = t := by omega
    apply vertical_ff_spacing _ (sideChart_acyclic s F hacyc) x z (t - 1) hz
      (by omega) hxz hx0 ?_ hz0 ?_
    · change sideChart s (⟨x, by omega⟩, ⟨t - 1 + 1, by omega⟩) ∈ F
      simpa only [he] using hx1
    · change sideChart s (⟨z, hz⟩, ⟨t - 1 + 1, by omega⟩) ∈ F
      simpa only [he] using hz1
  · intro x hx
    obtain ⟨hxI, hxn, htn, hx0, hx1⟩ := mem_filter.mp hx
    have hxI' := mem_Icc.mp hxI
    have he : t - 1 + 1 = t := by omega
    have hcol := cost_two_vertical_edge_columns hk F hacyc s hW x (t - 1)
      (by omega) (by omega) hx0 (by simpa only [he] using hx1)
    apply mem_Icc.mpr
    omega

/-- The full four-step shadow follows from opposite-cell obstructions for
the actual horizontal and vertical FF endpoints. It is not an assumed rod loss. -/
theorem rectangle_ff_shadow {n : Nat} (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (r t : Nat) (hr : 2 ≤ r) (ht : 1 ≤ t)
    (hband : t ∈ Icc (r - 2) (r + 1))
    (v : Nat) (hv : v ∈ rectangleVerticalColumns F s t)
    (x : Nat) (hx : x ∈ rectangleHorizontalColumns F s r) :
    v + 1 < x ∨ x + 2 < v := by
  obtain ⟨_, hvn, htn, hv0, hv1⟩ := mem_filter.mp hv
  obtain ⟨_, hxn, hrn, hx0, hx1⟩ := mem_filter.mp hx
  have hband' := mem_Icc.mp hband
  by_contra h
  push Not at h
  have hrow : (t - 1 + 1 = r - 1 ∨ r - 1 + 1 = t - 1) ∨
      (t + 1 = r - 1 ∨ r - 1 + 1 = t) := by omega
  have hcol : (v + 1 = x ∨ x + 1 = v) ∨ (v + 1 = x + 1 ∨ x + 1 + 1 = v) := by omega
  have hP := sideChart_acyclic s F hacyc
  rcases hrow with hrow | hrow <;> rcases hcol with hcol | hcol
  · exact diagonal_preserved_false _ hP _ _ hv0 hx0 hcol hrow
  · exact diagonal_preserved_false _ hP _ _ hv0 hx1 hcol hrow
  · exact diagonal_preserved_false _ hP _ _ hv1 hx0 hcol hrow
  · exact diagonal_preserved_false _ hP _ _ hv1 hx1 hcol hrow

/-- Different horizontal rows at distance at most two have disjoint actual
edge-column sets. At distance two the obstruction is a boundary six-cycle. -/
theorem nearby_horizontal_columns_disjoint {n : Nat} (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (r t : Nat) (hr : 1 ≤ r) (hrt : r < t) (hne : t ≤ r + 2) :
    Disjoint (rectangleHorizontalColumns F s r) (rectangleHorizontalColumns F s t) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨_, hxn, hrn, hx0, hx1⟩ := mem_filter.mp hx
  obtain ⟨_, _, htn, hy0, hy1⟩ := mem_filter.mp hy
  have hcases : t = r + 1 ∨ t = r + 2 := by omega
  rcases hcases with he | he
  · exact diagonal_preserved_false _ (sideChart_acyclic s F hacyc) _ _ hx0 hy1
      (Or.inl rfl) (Or.inl (by dsimp; omega))
  · have he' : r - 1 + 2 = t - 1 := by omega
    apply forced_rectangle_two_rows_false (⟨r - 1, by omega⟩ : Fin (n - 2))
      (⟨x, by omega⟩ : Fin (n - 1)) (chart_transpose_acyclic F hacyc s) hx0 hx1
    · change sideChart s (⟨x, by omega⟩, ⟨r - 1 + 2, by omega⟩) ∈ F
      simpa only [he'] using hy0
    · change sideChart s (⟨x + 1, by omega⟩, ⟨r - 1 + 2, by omega⟩) ∈ F
      simpa only [he'] using hy1

end GridGraphs.CarrierLayers.ThreeCarrier
