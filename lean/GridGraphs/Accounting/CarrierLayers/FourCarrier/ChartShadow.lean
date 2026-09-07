import GridGraphs.Accounting.CarrierLayers.FourCarrier.MapPartition

/-! # Expanded shadows in side-chart coordinates

Only grid edges and local cycles are transported. The fixed boundary map is
not transported. Shadows are actual boundary holes, including their endpoints.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

/-- A depth-one preserved vertex forbids either diagonally adjacent boundary
vertex. This includes the two boundary corners. -/
theorem chart_diagonal_boundary_hole {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (a b : Fin n) (hdiag : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (haF : sideChart s (a, ⟨1, by omega⟩) ∈ F) :
    sideChart s (b, ⟨0, by omega⟩) ∉ F := by
  intro hbF
  have hP := sideChart_acyclic s F hacyc
  rcases hdiag with h | h
  · let r : Fin (n - 1) := ⟨a.val, by omega⟩
    let c : Fin (n - 1) := ⟨0, by omega⟩
    have he : (⟨a.val + 1, by omega⟩ : Fin n) = b := Fin.ext h
    have hb' : sideChart s (⟨a.val + 1, by omega⟩, ⟨0, by omega⟩) ∈ F := by
      simpa only [he] using hbF
    have H := grid_cell_has_unforced_edge r c hP
    simp only [cell00, cell01, cell11, cell10, r, c] at H
    rcases H with H | H | H | H
    · exact H.2 haF
    · exact H.1 haF
    · exact H.2 hb'
    · exact H.1 hb'
  · let r : Fin (n - 1) := ⟨b.val, by omega⟩
    let c : Fin (n - 1) := ⟨0, by omega⟩
    have he : (⟨b.val + 1, by omega⟩ : Fin n) = a := Fin.ext h
    have ha' : sideChart s (⟨b.val + 1, by omega⟩, ⟨1, by omega⟩) ∈ F := by
      simpa only [he] using haF
    have H := grid_cell_has_unforced_edge r c hP
    simp only [cell00, cell01, cell11, cell10, r, c] at H
    rcases H with H | H | H | H
    · exact H.1 hbF
    · exact H.2 ha'
    · exact H.1 ha'
    · exact H.2 hbF

/-- Preserved corners remove all four next-ring corner positions, in any chart. -/
theorem chart_depth_one_away_from_ends {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hcorners : ∀ v, BoundarySix.Corner v → v ∈ F)
    (s : Fin 4) (a : Fin n) (ha : 0 < a.val ∧ a.val + 1 < n)
    (haF : sideChart s (a, ⟨1, by omega⟩) ∈ F) :
    2 ≤ a.val ∧ a.val + 2 < n := by
  have hfirst : a.val ≠ 1 := by
    intro he
    have hU := chart_diagonal_boundary_hole hn F hacyc s a ⟨0, by omega⟩
      (Or.inr (by dsimp; omega)) haF
    exact hU (hcorners _ ((sideChart_corner s _).mpr (by simp [BoundarySix.Corner])))
  have hlast : a.val + 2 ≠ n := by
    intro he
    have hU := chart_diagonal_boundary_hole hn F hacyc s a ⟨n - 1, by omega⟩
      (Or.inl (by dsimp; omega)) haF
    exact hU (hcorners _ ((sideChart_corner s _).mpr (by dsimp [BoundarySix.Corner]; omega)))
  omega

/-- Interval filling for two chart-depth-one vertices in one actual carrier. -/
theorem chart_carrier_depth_one_interval {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (u v : (↑F : Set (GridVertex n n))) (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (a b : Fin n) (hua : u.val = sideChart s (a, ⟨1, by omega⟩))
    (hvb : v.val = sideChart s (b, ⟨1, by omega⟩))
    (t : Fin n) (ht : a.val ≤ t.val ∧ t.val ≤ b.val) :
    sideChart s (t, ⟨1, by omega⟩) ∈ F := by
  by_cases hs : s.val < 2
  · have hrow : u.val.1 = v.val.1 := by
      rw [hua, hvb]
      fin_cases s <;> simp [sideChart] at hs ⊢
    have hbetween : u.val.2.val ≤ t.val ∧ t.val ≤ v.val.2.val := by
      rw [hua, hvb]
      fin_cases s <;> simp [sideChart] at hs ⊢ <;> omega
    obtain ⟨hwF, _⟩ := induced_forced_connectedComponent_horizontal_interval_of_le
      hacyc C hu hv hrow t hbetween.1 hbetween.2
    have he : (u.val.1, t) = sideChart s (t, ⟨1, by omega⟩) := by
      rw [hua]
      fin_cases s <;> simp [sideChart] at hs ⊢
    exact he ▸ hwF
  · have hcol : u.val.2 = v.val.2 := by
      rw [hua, hvb]
      fin_cases s <;> simp [sideChart] at hs ⊢
    have hbetween : u.val.1.val ≤ t.val ∧ t.val ≤ v.val.1.val := by
      rw [hua, hvb]
      fin_cases s <;> simp [sideChart] at hs ⊢ <;> omega
    obtain ⟨hwF, _⟩ := induced_forced_connectedComponent_vertical_interval
      hacyc C hu hv hcol t (Or.inl hbetween)
    have he : (t, u.val.2) = sideChart s (t, ⟨1, by omega⟩) := by
      rw [hua]
      fin_cases s <;> simp [sideChart] at hs ⊢
    exact he ▸ hwF

/-- The expanded shadow of an actual parallel carrier is a contiguous hole
interval from `a-1` to `b+1`, in all four orientations. -/
theorem chart_carrier_expanded_shadow {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (u v : (↑F : Set (GridVertex n n))) (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (a b : Fin n) (hua : u.val = sideChart s (a, ⟨1, by omega⟩))
    (hvb : v.val = sideChart s (b, ⟨1, by omega⟩))
    (ha : 1 ≤ a.val) (hab : a.val < b.val) (hb : b.val + 1 < n)
    (t : Fin n) (ht : a.val - 1 ≤ t.val ∧ t.val ≤ b.val + 1) :
    sideChart s (t, ⟨0, by omega⟩) ∉ F := by
  let j : Fin n := ⟨if t.val ≤ a.val then t.val + 1 else t.val - 1, by split <;> omega⟩
  have hj : a.val ≤ j.val ∧ j.val ≤ b.val := by dsimp [j]; split <;> omega
  have hjF := chart_carrier_depth_one_interval hn F hacyc s C u v hu hv a b hua hvb j hj
  apply chart_diagonal_boundary_hole hn F hacyc s j t _ hjF
  dsimp [j]
  split <;> omega

end GridGraphs.CarrierLayers.FourCarrier
