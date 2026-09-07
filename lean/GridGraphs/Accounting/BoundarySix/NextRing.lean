import GridGraphs.Accounting.BoundarySix.Pairs
import GridGraphs.Geometry.GridLayers

/-! # The boundary-six next-ring bound

This is a grid-level bound for every feasible set, not an assumption on a
boundary certificate. Coordinates are zero-based, and the four corners of the
once-cropped square are included in the next ring.
-/

namespace GridGraphs

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

namespace BoundarySix

private def Supports {n : Nat} (v x y : GridVertex n n) : Prop :=
  (((v.1.val = 1 ∧ x.1.val = 0 ∧ y.1.val = 0) ∨
    (v.1.val + 2 = n ∧ x.1.val + 1 = n ∧ y.1.val + 1 = n)) ∧
    x.2.val + 1 = v.2.val ∧ v.2.val + 1 = y.2.val) ∨
  (((v.2.val = 1 ∧ x.2.val = 0 ∧ y.2.val = 0) ∨
    (v.2.val + 2 = n ∧ x.2.val + 1 = n ∧ y.2.val + 1 = n)) ∧
    x.1.val + 1 = v.1.val ∧ v.1.val + 1 = y.1.val)

private theorem supports_gap {n : Nat} {v x y : GridVertex n n}
    (h : Supports v x y) : Gap x y := by
  unfold Supports Gap at *
  omega

private theorem supports_injective {n : Nat} {v w x y s t : GridVertex n n}
    (hv : Supports v x y) (hw : Supports w s t) (h : s(x, y) = s(s, t)) : v = w := by
  simp only [Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff] at h
  apply Prod.ext <;> apply Fin.ext
  all_goals unfold Supports at *; omega

private theorem preserved_support {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    {v : GridVertex n n} (hvF : v ∈ F) (hv : IsNextRing v) :
    ∃ x y, x ∉ F ∧ y ∉ F ∧ Supports v x y := by
  obtain ⟨hrlo, hrhi, hclo, hchi, hside⟩ := hv
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
  rcases hside with htop | hbottom | hleft | hright
  · have hx := h00 z cm (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell11, z, cm] <;> omega)
    have hy := h01 z c (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell10, z, c]
      omega)
    refine ⟨cell00 z cm, cell01 z c, hx, hy, ?_⟩
    unfold Supports
    left
    simp [cell00, cell01, z, cm, c]
    omega
  · have hx := h10 r cm (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell01, r, cm]
      omega)
    have hy := h11 r c (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell00, r, c])
    refine ⟨cell10 r cm, cell11 r c, hx, hy, ?_⟩
    unfold Supports
    left
    simp [cell10, cell11, r, cm, c]
    omega
  · have hx := h00 rm z (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell11, rm, z] <;> omega)
    have hy := h10 r z (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell01, r, z]
      omega)
    refine ⟨cell00 rm z, cell10 r z, hx, hy, ?_⟩
    unfold Supports
    right
    simp [cell00, cell10, rm, r, z]
    omega
  · have hx := h01 rm c (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell10, rm, c]
      omega)
    have hy := h11 r c (by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell00, r, c])
    refine ⟨cell01 rm c, cell11 r c, hx, hy, ?_⟩
    unfold Supports
    right
    simp [cell01, cell11, rm, r, c]
    omega

/-- A preserved next-ring vertex forces a same-side distance-two pair of holes. -/
theorem preserved_gap {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    {v : GridVertex n n} (hvF : v ∈ F) (hv : IsNextRing v) :
    ∃ x y, x ∉ F ∧ y ∉ F ∧ Gap x y := by
  obtain ⟨x, y, hx, hy, h⟩ := preserved_support hn F hacyc hvF hv
  exact ⟨x, y, hx, hy, supports_gap h⟩

end BoundarySix

/-- U1: two preserved vertices on the next ring must coincide at deficiency six.
No exclusion of next-ring corners or boundary normalization is assumed. -/
theorem boundaryDeficiencySum_compl_eq_six_next_ring_unique
    {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    {v w : GridVertex n n} (hvF : v ∈ F) (hwF : w ∈ F)
    (hv : IsNextRing v) (hw : IsNextRing w) : v = w := by
  obtain ⟨x, y, hx, hy, hvxy⟩ := BoundarySix.preserved_support hn F hacyc hvF hv
  obtain ⟨s, t, hs, ht, hwst⟩ := BoundarySix.preserved_support hn F hacyc hwF hw
  exact BoundarySix.supports_injective hvxy hwst (BoundarySix.gap_unique hn F hacyc hb
    hx hy hs ht (BoundarySix.supports_gap hvxy) (BoundarySix.supports_gap hwst))

/-- At most one vertex of a feasible set lies on the boundary of the once-cropped
square when its complementary boundary deficiency is six and `n ≥ 9`. -/
theorem boundaryDeficiencySum_compl_eq_six_next_ring_card_le_one
    {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6) :
    (F.filter IsNextRing).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro v hv w hw
  exact boundaryDeficiencySum_compl_eq_six_next_ring_unique hn F hacyc hb
    (mem_filter.mp hv).1 (mem_filter.mp hw).1 (mem_filter.mp hv).2 (mem_filter.mp hw).2

end GridGraphs
