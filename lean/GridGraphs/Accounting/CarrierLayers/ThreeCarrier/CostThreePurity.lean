import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostThreeBoundary

/-! # No off-side next-ring occupancy at W3

Two diagonal holes of an off-side next-ring vertex must use a far witness
and the extra hole. This determines the candidate's second position. The
remaining two corners of a six-cycle are then preserved by the same exact
three-hole list, giving a contradiction without assuming contact purity.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- W3 has no preserved next-ring vertex off the missing-side depth-one
line. This requires neither a score nor a pure-carrier count. -/
theorem cost_three_nextRing_chart {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3)
    (v : GridVertex (3 * k + 2) (3 * k + 2)) (hv : v ∈ F) (hvr : IsNextRing v) :
    ∃ x : Fin (3 * k + 2), 2 ≤ x.val ∧ x.val + 2 < 3 * k + 2 ∧
      v = sideChart s (x, ⟨1, by omega⟩) := by
  classical
  let n := 3 * k + 2
  let P : Set (GridVertex n n) := {u | sideChart s u ∈ F}
  have hP := sideChart_acyclic s F hacyc
  have hPT := chart_transpose_acyclic F hacyc s
  obtain ⟨u, rfl⟩ := sideChart_surjective s v
  have hu : u ∈ P := hv
  have hr : IsNextRing u := by
    fin_cases s <;> simp [sideChart, IsNextRing] at hvr ⊢ <;> omega
  have hcorners (w : GridVertex n n) (hw : BoundarySix.Corner w) : w ∈ P :=
    (cost_three_boundary (by omega) F hacyc s hW).1 _ ((sideChart_corner s w).mpr hw)
  obtain ⟨a, b, c', ha, hb, _, _, _, _, hO⟩ := cost_three_far_holes_plus_one hk F hacyc s hW
  obtain ⟨c, hc⟩ := sideChart_surjective s c'
  have hhole (w : GridVertex n n) (hwb : IsGridBoundary w)
      (hws : ¬ (w.2.val = 0 ∧ 0 < w.1.val ∧ w.1.val + 1 < n)) (hw : w ∉ P) :
      w = a ∨ w = b ∨ w = c := by
    have hm : sideChart s w ∈ (univ \ F).filter
        (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) :=
      mem_filter.mpr ⟨by simp [show sideChart s w ∉ F from hw],
        (sideChart_boundary s w).mpr hwb, fun h => hws ((sideChart_openSide s w).mp h)⟩
    rw [hO, ← hc] at hm
    simpa only [mem_insert, mem_singleton, (sideChart_injective s).eq_iff] using hm
  have hfill (w : GridVertex n n) (hwb : IsGridBoundary w)
      (hws : ¬ (w.2.val = 0 ∧ 0 < w.1.val ∧ w.1.val + 1 < n))
      (hne : w ≠ a ∧ w ≠ b ∧ w ≠ c) : w ∈ P := by
    by_contra hw
    rcases hhole w hwb hws hw with h | h | h
    · exact hne.1 h
    · exact hne.2.1 h
    · exact hne.2.2 h
  have hdiag (w : GridVertex n n)
      (hx : u.1.val + 1 = w.1.val ∨ w.1.val + 1 = u.1.val)
      (hy : u.2.val + 1 = w.2.val ∨ w.2.val + 1 = u.2.val) : w ∉ P := by
    intro hw
    exact diagonal_preserved_false P hP u w hu hw hx hy
  have ha' := ha
  have hb' := hb
  simp only [Prod.ext_iff, Fin.ext_iff] at ha' hb'
  have hr' := hr
  unfold IsNextRing at hr'
  have hside (i : Nat) (hi : i = 0 ∨ i = n - 1)
      (hux : u.1.val = if i = 0 then 1 else n - 2) : False := by
    have hy : 2 ≤ u.2.val ∧ u.2.val + 2 < n := by
      have hlow : u.2.val ≠ 1 := by
        intro he
        have hw := hdiag (⟨i, by omega⟩, ⟨0, by omega⟩)
          (by dsimp; split_ifs at hux <;> omega) (by dsimp; omega)
        exact hw (hcorners _ (by dsimp [BoundarySix.Corner]; omega))
      have hhigh : u.2.val ≠ n - 2 := by
        intro he
        have hw := hdiag (⟨i, by omega⟩, ⟨n - 1, by omega⟩)
          (by dsimp; split_ifs at hux <;> omega) (by dsimp; omega)
        exact hw (hcorners _ (by dsimp [BoundarySix.Corner]; omega))
      omega
    let l : GridVertex n n := (⟨i, by omega⟩, ⟨u.2.val - 1, by omega⟩)
    let r : GridVertex n n := (⟨i, by omega⟩, ⟨u.2.val + 1, by omega⟩)
    have hl := hhole l (by dsimp [l, IsGridBoundary]; omega)
      (by dsimp [l]; omega) (hdiag l (by dsimp [l]; split_ifs at hux <;> omega)
        (by dsimp [l]; omega))
    have hh := hhole r (by dsimp [r, IsGridBoundary]; omega)
      (by dsimp [r]; omega) (hdiag r (by dsimp [r]; split_ifs at hux <;> omega)
        (by dsimp [r]; omega))
    simp only [Prod.ext_iff, Fin.ext_iff] at hl hh
    dsimp [l, r] at hl hh
    have hloc : u.2.val = n - 3 ∧ c.1.val = i ∧ c.2.val = n - 4 := by
      dsimp [n] at hi hux hy hl hh ⊢
      split_ifs at hux <;> omega
    let p : GridVertex n n := (⟨i, by omega⟩, ⟨n - 3, by omega⟩)
    let q : GridVertex n n := (u.1, ⟨n - 1, by omega⟩)
    have hp : p ∈ P := hfill p (by dsimp [p, IsGridBoundary]; omega)
      (by dsimp [p]; omega) (by
        simp only [Ne, Prod.ext_iff, Fin.ext_iff]
        dsimp [p, n] at hloc ⊢
        omega)
    have hq : q ∈ P := hfill q (by dsimp [q, IsGridBoundary]; omega)
      (by dsimp [q]; omega) (by
        simp only [Ne, Prod.ext_iff, Fin.ext_iff]
        dsimp [q, n] at hloc hi hux ⊢
        split_ifs at hux <;> omega)
    have he : n - 3 + 2 = n - 1 := by omega
    have hu' : (u.1, ⟨n - 3, by omega⟩) ∈ P := by
      convert hu using 1
      exact Prod.ext rfl (Fin.ext hloc.1.symm)
    have hcF : (⟨i, by omega⟩, ⟨n - 1, by omega⟩) ∈ P :=
      hcorners _ (by dsimp [BoundarySix.Corner]; omega)
    rcases hi with hi | hi
    · have hi' : i = 0 := hi
      have hx : u.1 = ⟨1, by omega⟩ := Fin.ext (by rw [hi'] at hux; simpa using hux)
      apply forced_rectangle_two_rows_false (⟨n - 3, by omega⟩ : Fin (n - 2))
        (⟨0, by omega⟩ : Fin (n - 1)) hPT
      · change (⟨0, by omega⟩, ⟨n - 3, by omega⟩) ∈ P
        simpa only [p, hi'] using hp
      · change (⟨1, by omega⟩, ⟨n - 3, by omega⟩) ∈ P
        simpa only [hx] using hu'
      · change (⟨0, by omega⟩, ⟨n - 3 + 2, by omega⟩) ∈ P
        simpa only [he, hi'] using hcF
      · change (⟨1, by omega⟩, ⟨n - 3 + 2, by omega⟩) ∈ P
        simpa only [q, he, hx] using hq
    · have hix : u.1.val = n - 2 := by split_ifs at hux <;> omega
      have hx : u.1 = ⟨n - 2, by omega⟩ := Fin.ext hix
      have he' : n - 2 + 1 = n - 1 := by omega
      apply forced_rectangle_two_rows_false (⟨n - 3, by omega⟩ : Fin (n - 2))
        (⟨n - 2, by omega⟩ : Fin (n - 1)) hPT
      · change (⟨n - 2, by omega⟩, ⟨n - 3, by omega⟩) ∈ P
        simpa only [hx] using hu'
      · change (⟨n - 2 + 1, by omega⟩, ⟨n - 3, by omega⟩) ∈ P
        simpa only [p, hi, he'] using hp
      · change (⟨n - 2, by omega⟩, ⟨n - 3 + 2, by omega⟩) ∈ P
        simpa only [q, he, hx] using hq
      · change (⟨n - 2 + 1, by omega⟩, ⟨n - 3 + 2, by omega⟩) ∈ P
        simpa only [he, hi, he'] using hcF
  have hfar (huy : u.2.val = n - 2) : False := by
    have hx : 2 ≤ u.1.val ∧ u.1.val + 2 < n := by
      have hlow : u.1.val ≠ 1 := by
        intro he
        exact hdiag (⟨0, by omega⟩, ⟨n - 1, by omega⟩) (by dsimp; omega)
          (by dsimp; omega) (hcorners _ (by dsimp [BoundarySix.Corner]; omega))
      have hhigh : u.1.val ≠ n - 2 := by
        intro he
        exact hdiag (⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩) (by dsimp; omega)
          (by dsimp; omega) (hcorners _ (by dsimp [BoundarySix.Corner]; omega))
      omega
    let l : GridVertex n n := (⟨u.1.val - 1, by omega⟩, ⟨n - 1, by omega⟩)
    let r : GridVertex n n := (⟨u.1.val + 1, by omega⟩, ⟨n - 1, by omega⟩)
    have hl := hhole l (by dsimp [l, IsGridBoundary]; omega)
      (by dsimp [l]; omega) (hdiag l (by dsimp [l]; omega) (by dsimp [l]; omega))
    have hh := hhole r (by dsimp [r, IsGridBoundary]; omega)
      (by dsimp [r]; omega) (hdiag r (by dsimp [r]; omega) (by dsimp [r]; omega))
    simp only [Prod.ext_iff, Fin.ext_iff] at hl hh
    dsimp [l, r] at hl hh
    have hloc : (u.1.val = 2 ∧ c.1.val = 3) ∨
        (u.1.val = n - 3 ∧ c.1.val = n - 4) := by dsimp [n] at hl hh hx ⊢; omega
    have hcy : c.2.val = n - 1 := by dsimp [n] at hl hh hx ⊢; omega
    let i := if u.1.val = 2 then 0 else n - 1
    have hi : i = 0 ∨ i = n - 1 := by dsimp [i]; split <;> simp
    let p : GridVertex n n := (u.1, ⟨n - 1, by omega⟩)
    let q : GridVertex n n := (⟨i, by omega⟩, ⟨n - 2, by omega⟩)
    have hp : p ∈ P := hfill p (by dsimp [p, IsGridBoundary]; omega)
      (by dsimp [p]; omega) (by
        simp only [Ne, Prod.ext_iff, Fin.ext_iff]
        dsimp [p, n] at hloc hcy ⊢
        omega)
    have hq : q ∈ P := hfill q (by dsimp [q, IsGridBoundary]; omega)
      (by dsimp [q]; omega) (by
        simp only [Ne, Prod.ext_iff, Fin.ext_iff]
        dsimp [q, i, n] at hloc hcy hl hh ⊢
        split <;> omega)
    have hcF : (⟨i, by omega⟩, ⟨n - 1, by omega⟩) ∈ P :=
      hcorners _ (by dsimp [BoundarySix.Corner]; omega)
    have hu' : (u.1, ⟨n - 2, by omega⟩) ∈ P := by
      convert hu using 1
      exact Prod.ext rfl (Fin.ext huy.symm)
    have he : n - 2 + 1 = n - 1 := by omega
    rcases hloc with ⟨hx, _⟩ | ⟨hx, _⟩
    · have hi' : i = 0 := by simp [i, hx]
      have hx' : u.1 = ⟨2, by omega⟩ := Fin.ext hx
      apply forced_rectangle_two_rows_false (⟨0, by omega⟩ : Fin (n - 2))
        (⟨n - 2, by omega⟩ : Fin (n - 1)) hP
      · simpa only [q, hi'] using hq
      · simpa only [he, hi'] using hcF
      · simpa only [hx'] using hu'
      · simpa only [p, he, hx'] using hp
    · have hi' : i = n - 1 := by simp [i, hx, show n - 3 ≠ 2 by omega]
      have hx' : u.1 = ⟨n - 3, by omega⟩ := Fin.ext hx
      have he' : n - 3 + 2 = n - 1 := by omega
      apply forced_rectangle_two_rows_false (⟨n - 3, by omega⟩ : Fin (n - 2))
        (⟨n - 2, by omega⟩ : Fin (n - 1)) hP
      · simpa only [hx'] using hu'
      · simpa only [p, he, hx'] using hp
      · simpa only [q, hi', he'] using hq
      · simpa only [he, hi', he'] using hcF
  have huy : u.2.val = 1 := by
    rcases hr'.2.2.2.2 with h | h | h | h
    · exact (hside 0 (Or.inl rfl) (by simpa using h)).elim
    · exact (hside (n - 1) (Or.inr rfl) (by split <;> omega)).elim
    · exact h
    · exact (hfar (by omega)).elim
  have hue : u = (u.1, ⟨1, by omega⟩) := Prod.ext rfl (Fin.ext huy)
  have hbnd := chart_depth_one_away_from_ends (by omega) F hacyc
    (cost_three_boundary (by omega) F hacyc s hW).1 s u.1
    (by omega) (by simpa only [← hue] using hv)
  exact ⟨u.1, hbnd.1, hbnd.2, congrArg (sideChart s) hue⟩

/-- Every preserved off-side boundary contact belongs to an actual pure carrier at W3. -/
theorem cost_three_offside_carrier_pure {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3)
    (C : ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).ConnectedComponent)
    (v : (↑F : Set _)) (hv : v ∈ C.supp)
    (hb : IsGridBoundary v.val) (hs : ¬ OnOpenSide s v.val) :
    C ∈ pureBoundaryCarriers F := by
  by_contra hC
  obtain ⟨w, _, hwr, hadj⟩ := boundary_nonpure_carrier_nextRing_neighbor
    (by omega) F hacyc C hC hv hb
  obtain ⟨x, hx, hxn, he⟩ := cost_three_nextRing_chart hk F hacyc s hW w.val w.property hwr
  rw [he] at hadj
  have hvs : OnOpenSide s v.val := by
    fin_cases s <;> norm_num only [sideChart, Fin.reduceFinMk, ↓reduceIte] at hadj <;>
      simp only [ite_true, ite_false, gridGraph, adjacent, Fin.ext_iff, Fin.val_rev] at hadj <;>
      dsimp [OnOpenSide, OnSide] <;> unfold IsGridBoundary at hb <;> omega
  exact hs hvs

end GridGraphs.CarrierLayers.ThreeCarrier
