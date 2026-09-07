import GridGraphs.Accounting.BoundarySix.Decomposition

namespace GridGraphs.BoundarySix

open Finset SimpleGraph

set_option maxHeartbeats 800000

private theorem gap_ne {n : Nat} {x y : GridVertex n n} (h : Gap x y) : x ≠ y := by
  intro H
  subst y
  unfold Gap at h
  omega

private theorem gap_not_adj {n : Nat} {x y : GridVertex n n} (h : Gap x y) :
    ¬ (gridGraph n n).Adj x y := by
  simp only [gridGraph, adjacent, Fin.ext_iff]
  unfold Gap at h
  omega

private theorem hub_unique {n : Nat} (P : GridVertex n n → Prop) (v : GridVertex n n)
    (haway : ∀ x y, P x → P y → ¬ Gap x y)
    (hpartner : ∀ x y, P x → P y → Gap v x → Gap v y → x = y)
    {x y s t : GridVertex n n}
    (hx : P x ∨ x = v) (hy : P y ∨ y = v)
    (hs : P s ∨ s = v) (ht : P t ∨ t = v)
    (hxy : Gap x y) (hst : Gap s t) : s(x, y) = s(s, t) := by
  have orient {a b : GridVertex n n} (ha : P a ∨ a = v) (hb : P b ∨ b = v)
      (hab : Gap a b) : ∃ q, P q ∧ Gap v q ∧ s(a, b) = s(v, q) := by
    rcases ha with ha | rfl <;> rcases hb with hb | rfl
    · exact False.elim (haway a b ha hb hab)
    · exact ⟨a, ha, gap_symm hab, Sym2.eq_swap⟩
    · exact ⟨b, hb, hab, rfl⟩
    · exact False.elim (gap_ne hab rfl)
  obtain ⟨q, hq, hvq, heq⟩ := orient hx hy hxy
  obtain ⟨r, hr, hvr, her⟩ := orient hs ht hst
  rw [heq, her, hpartner q r hq hr hvq hvr]

private theorem second_unique {n : Nat} (hn : 9 ≤ n) {u v x y s t : GridVertex n n}
    (hu : Second u) (hv : ¬ Corner v)
    (hx : Near x ∨ x = u ∨ x = v) (hy : Near y ∨ y = u ∨ y = v)
    (hs : Near s ∨ s = u ∨ s = v) (ht : Near t ∨ t = u ∨ t = v)
    (hxy : Gap x y) (hst : Gap s t) : s(x, y) = s(s, t) := by
  apply hub_unique (fun z => Near z ∨ z = u) v ?_ ?_
    (or_assoc.mpr hx) (or_assoc.mpr hy) (or_assoc.mpr hs) (or_assoc.mpr ht) hxy hst
  · intro a b ha hb hab
    rcases ha with ha | rfl <;> rcases hb with hb | rfl
    · exact near_not_gap hn ha hb hab
    · exact second_not_gap_near hn hu ha (gap_symm hab)
    · exact second_not_gap_near hn hu hb hab
    · exact gap_ne hab rfl
  · intro a b ha hb hva hvb
    rcases ha with ha | rfl <;> rcases hb with hb | rfl
    · exact near_gap_unique hn ha hb hva hvb
    · exact False.elim (second_gap_excludes_near hn hu hv ha (gap_symm hvb) hva)
    · exact False.elim (second_gap_excludes_near hn hu hv hb (gap_symm hva) hvb)
    · rfl

private theorem adjacent_unique {n : Nat} (hn : 9 ≤ n) {u v x y s t : GridVertex n n}
    (huv : (gridGraph n n).Adj u v)
    (hx : Near x ∨ x = u ∨ x = v) (hy : Near y ∨ y = u ∨ y = v)
    (hs : Near s ∨ s = u ∨ s = v) (ht : Near t ∨ t = u ∨ t = v)
    (hxy : Gap x y) (hst : Gap s t) : s(x, y) = s(s, t) := by
  have orient {a b : GridVertex n n}
      (ha : Near a ∨ a = u ∨ a = v) (hb : Near b ∨ b = u ∨ b = v)
      (hab : Gap a b) :
      ∃ z q, (z = u ∨ z = v) ∧ Near q ∧ Gap z q ∧ s(a, b) = s(z, q) := by
    rcases ha with ha | rfl | rfl <;> rcases hb with hb | rfl | rfl
    · exact False.elim (near_not_gap hn ha hb hab)
    · exact ⟨b, a, Or.inl rfl, ha, gap_symm hab, Sym2.eq_swap⟩
    · exact ⟨b, a, Or.inr rfl, ha, gap_symm hab, Sym2.eq_swap⟩
    · exact ⟨a, b, Or.inl rfl, hb, hab, rfl⟩
    · exact False.elim (gap_ne hab rfl)
    · exact False.elim (gap_not_adj hab huv)
    · exact ⟨a, b, Or.inr rfl, hb, hab, rfl⟩
    · exact False.elim (gap_not_adj hab huv.symm)
    · exact False.elim (gap_ne hab rfl)
  obtain ⟨z, q, hz, hq, hzq, heq⟩ := orient hx hy hxy
  obtain ⟨w, r, hw, hr, hwr, her⟩ := orient hs ht hst
  rw [heq, her]
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
  · rw [near_gap_unique hn hq hr hzq hwr]
  · exact False.elim (adjacent_gap_near_exclusive hn huv hq hr hzq hwr)
  · exact False.elim (adjacent_gap_near_exclusive hn huv.symm hq hr hzq hwr)
  · rw [near_gap_unique hn hq hr hzq hwr]

/-- There is at most one unordered same-side distance-two pair of boundary holes. -/
theorem gap_unique {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    {x y s t : GridVertex n n} (hx : x ∉ F) (hy : y ∉ F) (hs : s ∉ F) (ht : t ∉ F)
    (hxy : Gap x y) (hst : Gap s t) : s(x, y) = s(s, t) := by
  have boundary {a b : GridVertex n n} (h : Gap a b) : IsGridBoundary a := by
    unfold Gap IsGridBoundary at *
    omega
  rcases decomposition hn F hacyc hb with ⟨u, hu, cover⟩ | ⟨u, v, huc, hvc, huv, cover⟩
  · have Hx := cover x hx (boundary hxy)
    have Hy := cover y hy (boundary (gap_symm hxy))
    exfalso
    rcases Hx with Hx | rfl <;> rcases Hy with Hy | rfl
    · exact near_not_gap hn Hx Hy hxy
    · rcases hu with hu | hu
      · exact corner_not_gap_near hn hu Hx (gap_symm hxy)
      · exact second_not_gap_near hn hu Hx (gap_symm hxy)
    · rcases hu with hu | hu
      · exact corner_not_gap_near hn hu Hy hxy
      · exact second_not_gap_near hn hu Hy hxy
    · exact gap_ne hxy rfl
  · have Hx := cover x hx (boundary hxy)
    have Hy := cover y hy (boundary (gap_symm hxy))
    have Hs := cover s hs (boundary hst)
    have Ht := cover t ht (boundary (gap_symm hst))
    rcases huv with hu | hv | huv
    · exact second_unique hn hu hvc Hx Hy Hs Ht hxy hst
    · have swap {z : GridVertex n n} (h : Near z ∨ z = u ∨ z = v) :
          Near z ∨ z = v ∨ z = u := h.imp_right Or.symm
      exact second_unique hn hv huc (swap Hx) (swap Hy) (swap Hs) (swap Ht) hxy hst
    · exact adjacent_unique hn huv Hx Hy Hs Ht hxy hst

end GridGraphs.BoundarySix
