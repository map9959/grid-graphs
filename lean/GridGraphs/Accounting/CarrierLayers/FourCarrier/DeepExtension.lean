import GridGraphs.Accounting.CarrierLayers.FourCarrier.RootDeficit

/-! # Inward extension when no shallow carriers exist

An actual nonpure carrier must reach the deep layer if the shallow-carrier
finset is empty. Straightness and interval filling then force depth two.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- With no shallow nonpure carriers, a preserved depth-one vertex extends
to depth two in the same inward direction. This is uniform in the chosen side. -/
theorem inward_depth_two_of_no_shallow {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hzero : (nextRingCarriers F).card = 0) (s : Fin 4)
    (t : Fin n) (ht : 0 < t.val ∧ t.val + 1 < n)
    (hwF : sideChart s (t, ⟨1, by omega⟩) ∈ F) :
    sideChart s (t, ⟨2, by omega⟩) ∈ F := by
  classical
  let w : (↑F : Set (GridVertex n n)) := ⟨sideChart s (t, ⟨1, by omega⟩), hwF⟩
  let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk w
  let z := sideChart s (t, (⟨2, by omega⟩ : Fin n))
  have hw : w ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have hwb : ¬ IsGridBoundary w.val := by
    change ¬ IsGridBoundary (sideChart s _)
    rw [sideChart_boundary]
    dsimp [IsGridBoundary]
    omega
  have hnonpure : C ∉ pureBoundaryCarriers F := fun h => hwb ((mem_filter.mp h).2 w hw)
  have hdeep : ∃ v ∈ C.supp, ¬ IsGridBoundary v.val ∧ ¬ IsNextRing v.val := by
    by_contra h
    push Not at h
    have hm : C ∈ nextRingCarriers F := mem_filter.mpr ⟨mem_univ _, hnonpure, by
      intro v hv
      by_cases hb : IsGridBoundary v.val
      · exact Or.inl hb
      · exact Or.inr (h v hv hb)⟩
    simp only [card_eq_zero.mp hzero, Finset.notMem_empty] at hm
  obtain ⟨v, hv, hvb, hvr⟩ := hdeep
  have hvdeep : 2 ≤ v.val.1.val ∧ v.val.1.val < n - 2 ∧
      2 ≤ v.val.2.val ∧ v.val.2.val < n - 2 := by
    unfold IsGridBoundary at hvb
    unfold IsNextRing at hvr
    omega
  change z ∈ F
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · have hwrow := congrArg Fin.val (hr w hw)
    have hvrow := congrArg Fin.val (hr v hv)
    have hgeom : z.1 = w.val.1 ∧
        ((w.val.2.val ≤ z.2.val ∧ z.2.val ≤ v.val.2.val) ∨
         (v.val.2.val ≤ z.2.val ∧ z.2.val ≤ w.val.2.val)) := by
      fin_cases s <;> simp [w, z, sideChart, Fin.ext_iff] at hwrow ⊢ <;> omega
    obtain ⟨hzF, _⟩ := induced_forced_connectedComponent_horizontal_interval
      hacyc C hw hv ((hr w hw).trans (hr v hv).symm) z.2 hgeom.2
    have he : (w.val.1, z.2) = z := Prod.ext hgeom.1.symm rfl
    exact he ▸ hzF
  · have hwcol := congrArg Fin.val (hc w hw)
    have hvcol := congrArg Fin.val (hc v hv)
    have hgeom : z.2 = w.val.2 ∧
        ((w.val.1.val ≤ z.1.val ∧ z.1.val ≤ v.val.1.val) ∨
         (v.val.1.val ≤ z.1.val ∧ z.1.val ≤ w.val.1.val)) := by
      fin_cases s <;> simp [w, z, sideChart, Fin.ext_iff] at hwcol ⊢ <;> omega
    obtain ⟨hzF, _⟩ := induced_forced_connectedComponent_vertical_interval
      hacyc C hw hv ((hc w hw).trans (hc v hv).symm) z.1 hgeom.2
    have he : (z.1, w.val.2) = z := Prod.ext rfl hgeom.1.symm
    exact he ▸ hzF

/-- In a connected forced graph the middle of an empty boundary triple has
its inward vertex preserved. Corners and end gaps are not discarded. -/
theorem empty_chart_triple_inward {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent = 1)
    (s : Fin 4) (a : Nat) (ha : a + 2 < n)
    (h0 : sideChart s (⟨a, by omega⟩, ⟨0, by omega⟩) ∉ F)
    (h1 : sideChart s (⟨a + 1, by omega⟩, ⟨0, by omega⟩) ∉ F)
    (h2 : sideChart s (⟨a + 2, by omega⟩, ⟨0, by omega⟩) ∉ F) :
    sideChart s (⟨a + 1, by omega⟩, ⟨1, by omega⟩) ∈ F := by
  obtain ⟨w, hwF, hadj⟩ := preserved_neighbor_of_one_forced_component (by omega) F hc _ h1
  obtain ⟨z, hz⟩ := sideChart_surjective s w
  have hzF : sideChart s z ∈ F := hz ▸ hwF
  have hadj' : (gridGraph n n).Adj (⟨a + 1, by omega⟩, ⟨0, by omega⟩) z := by
    apply (sideChart_adj s _ _).mp
    rwa [hz]
  have hgeom : z = (⟨a, by omega⟩, ⟨0, by omega⟩) ∨
      z = (⟨a + 2, by omega⟩, ⟨0, by omega⟩) ∨
      z = (⟨a + 1, by omega⟩, ⟨1, by omega⟩) := by
    simp only [gridGraph, adjacent, Fin.ext_iff] at hadj'
    simp only [Prod.ext_iff, Fin.ext_iff]
    omega
  rcases hgeom with rfl | rfl | rfl
  · exact (h0 hzF).elim
  · exact (h2 hzF).elim
  · exact hzF

/-- Without shallow carriers, two inward preserved vertices cannot be one
or two positions apart: extension gives a unit cell or a six-cycle. -/
theorem close_inward_vertices_false_of_no_shallow {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hzero : (nextRingCarriers F).card = 0) (s : Fin 4)
    (a b : Nat) (ha : 0 < a) (hab : a < b) (hb : b + 1 < n) (hclose : b ≤ a + 2)
    (haF : sideChart s (⟨a, by omega⟩, ⟨1, by omega⟩) ∈ F)
    (hbF : sideChart s (⟨b, by omega⟩, ⟨1, by omega⟩) ∈ F) : False := by
  have ha2 := inward_depth_two_of_no_shallow hn F hacyc hzero s
    (⟨a, by omega⟩ : Fin n) (by dsimp; omega) haF
  have hb2 := inward_depth_two_of_no_shallow hn F hacyc hzero s
    (⟨b, by omega⟩ : Fin n) (by dsimp; omega) hbF
  have hP := sideChart_acyclic s F hacyc
  by_cases he : b = a + 1
  · subst b
    have H := grid_cell_has_unforced_edge
      (⟨a, by omega⟩ : Fin (n - 1)) (⟨1, by omega⟩ : Fin (n - 1)) hP
    simp only [cell00, cell01, cell11, cell10] at H
    rcases H with H | H | H | H
    · exact H.1 haF
    · exact H.1 ha2
    · exact H.1 hb2
    · exact H.1 hbF
  · have he : b = a + 2 := by omega
    subst b
    exact forced_rectangle_two_rows_false (⟨a, by omega⟩ : Fin (n - 2))
      (⟨1, by omega⟩ : Fin (n - 1)) hP haF ha2 hbF hb2

end GridGraphs.CarrierLayers.FourCarrier
