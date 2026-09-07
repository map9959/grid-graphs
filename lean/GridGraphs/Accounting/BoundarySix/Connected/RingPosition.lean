import GridGraphs.Accounting.BoundarySix.Connected.Inward

/-! # The two possible next-ring positions

A distance-two pair of holes must contain a near-corner or second-position
hole. Thus, after excluding next-ring corners, a preserved next-ring vertex
has side position two or three from an end. Position three is not discarded:
the two extra holes can occupy positions two and four.
-/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier

/-- The perimeter omission forces a near-corner or second-position endpoint
in every distance-two pair of boundary holes. -/
theorem gap_has_near_or_second {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    {x y : GridVertex n n} (hx : x ∉ F) (hy : y ∉ F) (hxy : Gap x y) :
    Near x ∨ Near y ∨ Second x ∨ Second y := by
  have hxb : IsGridBoundary x := by unfold Gap IsGridBoundary at *; omega
  have hyb : IsGridBoundary y := by unfold Gap IsGridBoundary at *; omega
  have hne : x ≠ y := by intro he; subst y; unfold Gap at hxy; omega
  have hnotadj : ¬ (gridGraph n n).Adj x y := by
    simp only [gridGraph, adjacent, Fin.ext_iff]
    unfold Gap at hxy
    omega
  rcases decomposition hn F hacyc hb with ⟨u, _, cover⟩ | ⟨u, v, _, _, huv, cover⟩
  · rcases cover x hx hxb with h | rfl
    · exact Or.inl h
    · rcases cover y hy hyb with h | he
      · exact Or.inr (Or.inl h)
      · exact (hne he.symm).elim
  · rcases cover x hx hxb with h | rfl | rfl
    · exact Or.inl h
    · rcases cover y hy hyb with h | he | rfl
      · exact Or.inr (Or.inl h)
      · exact (hne he.symm).elim
      · rcases huv with h | h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact (hnotadj h).elim
    · rcases cover y hy hyb with h | rfl | he
      · exact Or.inr (Or.inl h)
      · rcases huv with h | h | h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h))
        · exact (hnotadj h.symm).elim
      · exact (hne he.symm).elim

/-- If neither endpoint of the pair is near a corner, they are precisely the
two possible non-near holes in the boundary-six decomposition. -/
theorem gap_covers_non_near_holes {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    {x y : GridVertex n n} (hx : x ∉ F) (hy : y ∉ F) (hxy : Gap x y)
    (hxN : ¬ Near x) (hyN : ¬ Near y) :
    ∀ z, z ∉ F → IsGridBoundary z → Near z ∨ z = x ∨ z = y := by
  have hxb : IsGridBoundary x := by unfold Gap IsGridBoundary at *; omega
  have hyb : IsGridBoundary y := by unfold Gap IsGridBoundary at *; omega
  have hne : x ≠ y := by intro he; subst y; unfold Gap at hxy; omega
  rcases decomposition hn F hacyc hb with ⟨u, _, cover⟩ | ⟨u, v, _, _, _, cover⟩
  · have hxu := (cover x hx hxb).resolve_left hxN
    have hyu := (cover y hy hyb).resolve_left hyN
    exact (hne (hxu.trans hyu.symm)).elim
  · have hxu := (cover x hx hxb).resolve_left hxN
    have hyu := (cover y hy hyb).resolve_left hyN
    rcases hxu with rfl | rfl <;> rcases hyu with rfl | rfl
    · exact (hne rfl).elim
    · exact cover
    · intro z hz hzb
      exact (cover z hz hzb).imp_right Or.symm
    · exact (hne rfl).elim

private theorem chart_second {n : Nat} (s : Fin 4) (v : GridVertex n n) :
    Second (sideChart s v) ↔ Second v := by
  fin_cases s <;> simp [sideChart, Second] <;> omega

/-- With no shallow carriers, the only possible side positions are two or
three from an end. This includes the extra-hole pair at positions two and four. -/
theorem inward_position_two_or_three {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (hzero : (nextRingCarriers F).card = 0)
    (s : Fin 4) (t : Fin n) (ht : 0 < t.val ∧ t.val + 1 < n)
    (hw : sideChart s (t, ⟨1, by omega⟩) ∈ F) :
    t.val = 2 ∨ t.val = 3 ∨ t.val + 4 = n ∨ t.val + 3 = n := by
  have hbounds := inward_position_bounds hn F hacyc hb hzero s t ht hw
  obtain ⟨hx, hy⟩ := inward_diagonal_holes (by omega) F hacyc s t.val ht.1 ht.2 hw
  have hgap : Gap
      (sideChart (n := n) s (⟨t.val - 1, by omega⟩, ⟨0, by omega⟩))
      (sideChart s (⟨t.val + 1, by omega⟩, ⟨0, by omega⟩)) := by
    fin_cases s <;> simp [sideChart, Gap] <;> omega
  have h := gap_has_near_or_second hn F hacyc hb hx hy hgap
  simp only [sideChart_near, chart_second] at h
  simp only [Near, Second] at h
  omega

/-- In the surviving third-position case the boundary vertex directly
outside the ring vertex is preserved. The diagonal holes are the two extras,
at positions two and four (or their reflected positions). -/
theorem third_position_outer_preserved {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (s : Fin 4) (t : Fin n) (hpos : t.val = 3 ∨ t.val + 4 = n)
    (hw : sideChart s (t, ⟨1, by omega⟩) ∈ F) :
    sideChart s (t, ⟨0, by omega⟩) ∈ F := by
  have ht : 0 < t.val ∧ t.val + 1 < n := by omega
  obtain ⟨hx, hy⟩ := inward_diagonal_holes (by omega) F hacyc s t.val ht.1 ht.2 hw
  have hgap : Gap
      (sideChart (n := n) s (⟨t.val - 1, by omega⟩, ⟨0, by omega⟩))
      (sideChart s (⟨t.val + 1, by omega⟩, ⟨0, by omega⟩)) := by
    fin_cases s <;> simp [sideChart, Gap] <;> omega
  have hxN : ¬ Near (sideChart (n := n) s
      (⟨t.val - 1, by omega⟩, ⟨0, by omega⟩)) := by
    rw [sideChart_near]
    simp only [Near]
    omega
  have hyN : ¬ Near (sideChart (n := n) s
      (⟨t.val + 1, by omega⟩, ⟨0, by omega⟩)) := by
    rw [sideChart_near]
    simp only [Near]
    omega
  by_contra hroot
  have h := gap_covers_non_near_holes hn F hacyc hb hx hy hgap hxN hyN _ hroot
    ((sideChart_boundary s _).mpr (by simp [IsGridBoundary]))
  rcases h with h | h | h
  · rw [sideChart_near] at h
    simp only [Near] at h
    omega
  · have he := congrArg (fun v : GridVertex n n => v.1.val) (sideChart_injective s h)
    dsimp at he
    omega
  · have he := congrArg (fun v : GridVertex n n => v.1.val) (sideChart_injective s h)
    dsimp at he
    omega

end GridGraphs.BoundarySix.Connected
