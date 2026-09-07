import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.Ledger
import GridGraphs.Accounting.CarrierLayers.FourCarrier.ChartShadow
import GridGraphs.Accounting.CarrierLayers.FourCarrier.ThreeOffside

/-! # Physical geometry at weighted off-side cost two

The ordinary holes exhaust two actual near-corner witnesses. Diagonal cell
obstructions then remove every next-ring vertex off the missing-side line.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

/-- Cost two preserves all corners and leaves exactly two ordinary off-side
holes, both near corners. No root count or score is assumed. -/
theorem cost_two_boundary {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) :
    (∀ v, BoundarySix.Corner v → v ∈ F) ∧
      ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card = 2 ∧
      (∀ v, IsGridBoundary v → ¬ OnOpenSide s v → v ∉ F → BoundarySix.Near v) := by
  classical
  have hcorners := corners_preserved_of_offside_le_three hn F hacyc s (by omega)
  have hj : ((univ \ F).filter BoundarySix.Corner).card = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact (mem_sdiff.mp (mem_filter.mp hv).1).2 (hcorners v (mem_filter.mp hv).2)
  let O := (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)
  have hweight := offside_deficiency_eq_holes_add_corners (by omega) F s
  have hO : O.card = 2 := by dsimp [O]; omega
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := BoundarySix.corner_witnesses hn F hacyc
  let R := Q.filter (fun v => ¬ OnOpenSide s v)
  have hnear := near_openSide_card_le_two (by omega) Q hQnear s
  have hpart := card_filter_add_card_filter_not (s := Q) (p := OnOpenSide s)
  have hR : 2 ≤ R.card := by dsimp [R]; omega
  have hsub : R ⊆ O := by
    intro v hv
    have hvn := hQnear v (mem_filter.mp hv).1
    refine mem_filter.mpr ⟨hQU (mem_filter.mp hv).1, ?_, (mem_filter.mp hv).2⟩
    unfold BoundarySix.Near at hvn
    unfold IsGridBoundary
    omega
  have heq : R = O := eq_of_subset_of_card_le hsub (by omega)
  refine ⟨hcorners, hO, ?_⟩
  intro v hv hs hu
  have hvO : v ∈ O := mem_filter.mpr ⟨by simp [hu], hv, hs⟩
  rw [← heq] at hvO
  exact hQnear v (mem_filter.mp hvO).1

/-- On any other side, a depth-one preserved vertex would force two near
holes two positions apart. For `n>=9` no such pair exists. -/
theorem cost_two_other_depth_one_notMem {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2)
    (t : Fin 4) (ht : t ≠ s) (a : Fin n) (ha : 0 < a.val ∧ a.val + 1 < n) :
    sideChart t (a, ⟨1, by omega⟩) ∉ F := by
  intro haF
  obtain ⟨hcorners, _, hnear⟩ := cost_two_boundary hn F hacyc s hW
  have hab := chart_depth_one_away_from_ends (by omega) F hacyc hcorners t a ha haF
  let l : Fin n := ⟨a.val - 1, by omega⟩
  let r : Fin n := ⟨a.val + 1, by omega⟩
  have hlU := chart_diagonal_boundary_hole (by omega) F hacyc t a l
    (Or.inr (by dsimp [l]; omega)) haF
  have hrU := chart_diagonal_boundary_hole (by omega) F hacyc t a r
    (Or.inl rfl) haF
  have hpos (b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n)
      (hbU : sideChart t (b, ⟨0, by omega⟩) ∉ F) : b.val = 1 ∨ b.val = n - 2 := by
    have hbt := (sideChart_openSide t (b, ⟨0, by omega⟩)).mpr ⟨rfl, hb⟩
    have hbs : ¬ OnOpenSide s (sideChart t (b, ⟨0, by omega⟩)) := by
      intro h
      exact ht (openSide_unique hbt (by
        unfold OnOpenSide at h
        exact h.1))
    have hn' := (sideChart_near t _).mp (hnear _ (openSide_boundary hbt) hbs hbU)
    dsimp [BoundarySix.Near] at hn'
    omega
  have hl := hpos l (by dsimp [l]; omega) hlU
  have hr := hpos r (by dsimp [r]; omega) hrU
  dsimp [l, r] at hl hr
  omega

/-- Every preserved next-ring vertex is on the missing-side depth-one line,
strictly away from its two endpoints. This is actual occupancy, not an image bound. -/
theorem cost_two_nextRing_chart {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2)
    (v : GridVertex n n) (hv : v ∈ F) (hvr : IsNextRing v) :
    ∃ a : Fin n, 2 ≤ a.val ∧ a.val + 2 < n ∧
      v = sideChart s (a, ⟨1, by omega⟩) := by
  have hex : ∃ t : Fin 4, ∃ a : Fin n, 0 < a.val ∧ a.val + 1 < n ∧
      v = sideChart t (a, ⟨1, by omega⟩) := by
    have hr := hvr
    unfold IsNextRing at hr
    rcases hr.2.2.2.2 with h | h | h | h
    · exact ⟨0, v.2, by omega, by omega, by
        simp [sideChart, Prod.ext_iff, Fin.ext_iff]; omega⟩
    · exact ⟨1, v.2, by omega, by omega, by
        simp [sideChart, Prod.ext_iff, Fin.ext_iff]; omega⟩
    · exact ⟨2, v.1, by omega, by omega, by
        simp [sideChart, Prod.ext_iff, Fin.ext_iff]; omega⟩
    · exact ⟨3, v.1, by omega, by omega, by
        simp [sideChart, Prod.ext_iff, Fin.ext_iff]; omega⟩
  obtain ⟨t, a, ha0, han, he⟩ := hex
  have hts : t = s := by
    by_contra h
    exact cost_two_other_depth_one_notMem hn F hacyc s hW t h a ⟨ha0, han⟩ (he ▸ hv)
  subst t
  have hab := chart_depth_one_away_from_ends (by omega) F hacyc
    (cost_two_boundary hn F hacyc s hW).1 s a ⟨ha0, han⟩ (he ▸ hv)
  exact ⟨a, hab.1, hab.2, he⟩

/-- A preserved missing-side corner must attach to its off-side neighbor:
the side endpoint is a hole, and an isolated corner would use a fourth pure carrier. -/
theorem missing_corner_offside_neighbor_mem {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3)
    (t : Fin (3 * k + 2)) (ht : t.val = 0 ∨ t.val = 3 * k + 1)
    (hc : sideChart s (t, ⟨0, by omega⟩) ∈ F) :
    sideChart s (t, ⟨1, by omega⟩) ∈ F := by
  have hW := (three_pure_missing_side_root_cost hk F hacyc s hmissing hf hp).2.2
  by_contra hu
  apply corner_notMem_of_neighbors_notMem hk F hacyc hf hp _ ?_ ?_ hc
  · rw [sideChart_corner]
    dsimp [BoundarySix.Corner]
    omega
  · intro v hadj hv
    obtain ⟨z, rfl⟩ := sideChart_surjective s v
    have hadj' := (sideChart_adj s _ _).mp hadj
    have hz : z = (t, ⟨1, by omega⟩) ∨
        (z.2.val = 0 ∧ (z.1.val = 1 ∨ z.1.val = 3 * k)) := by
      simp only [gridGraph, adjacent, Fin.ext_iff] at hadj'
      simp only [Prod.ext_iff, Fin.ext_iff]
      omega
    rcases hz with rfl | ⟨hz0, hz1⟩
    · exact hu hv
    · have hzs := (sideChart_openSide s z).mpr ⟨hz0, by omega, by omega⟩
      have hpos := root_positions_of_offside_deficiency_le_five (by omega) F hacyc
        s hmissing (by omega) _ hv hzs
      rw [sideChart_position] at hpos
      omega

/-- Preserved missing-side corners exclude the second-position roots as well
as the endpoints. This conclusion is not restricted to W2. -/
theorem root_positions_of_corners_preserved {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hcorners : ∀ v, BoundarySix.Corner v → v ∈ F)
    (v : GridVertex (3 * k + 2) (3 * k + 2)) (hv : v ∈ F) (hs : OnOpenSide s v) :
    3 ≤ sidePosition s v ∧ sidePosition s v + 3 < 3 * k + 2 := by
  let n := 3 * k + 2
  have hW := (three_pure_missing_side_root_cost hk F hacyc s hmissing hf hp).2.2
  have hpos := root_positions_of_offside_deficiency_le_five (by omega) F hacyc
    s hmissing (by omega) v hv hs
  obtain ⟨u, rfl⟩ := sideChart_surjective s v
  have hus := (sideChart_openSide s u).mp hs
  have hu0 : u = (u.1, ⟨0, by omega⟩) := Prod.ext rfl (Fin.ext hus.1)
  have hroot : sideChart s (u.1, ⟨0, by omega⟩) ∈ F := by rwa [hu0] at hv
  have hin := sideChart_root_inward (by omega) F hacyc s hmissing u.1 hus.2 hroot
  have hP := sideChart_acyclic s F hacyc
  have hc0 : sideChart s (⟨0, by omega⟩, ⟨0, by omega⟩) ∈ F :=
    hcorners _ ((sideChart_corner s _).mpr (by simp [BoundarySix.Corner]))
  have hc1 : sideChart s (⟨n - 1, by omega⟩, ⟨0, by omega⟩) ∈ F :=
    hcorners _ ((sideChart_corner s _).mpr (by dsimp [BoundarySix.Corner]; omega))
  have hn0 := missing_corner_offside_neighbor_mem hk F hacyc s hmissing hf hp
    ⟨0, by omega⟩ (Or.inl rfl) hc0
  have hn1 := missing_corner_offside_neighbor_mem hk F hacyc s hmissing hf hp
    ⟨n - 1, by omega⟩ (Or.inr (by dsimp [n])) hc1
  have hfirst : u.1.val ≠ 2 := by
    intro he
    have hu : u.1 = ⟨2, by omega⟩ := Fin.ext he
    rw [hu] at hroot hin
    exact forced_rectangle_two_rows_false (⟨0, by omega⟩ : Fin (n - 2))
      (⟨0, by omega⟩ : Fin (n - 1)) hP hc0 hn0 hroot hin
  have hlast : u.1.val ≠ n - 3 := by
    intro he
    have hu : u.1 = ⟨n - 3, by omega⟩ := Fin.ext he
    rw [hu] at hroot hin
    have he' : n - 3 + 2 = n - 1 := by omega
    apply forced_rectangle_two_rows_false (⟨n - 3, by omega⟩ : Fin (n - 2))
      (⟨0, by omega⟩ : Fin (n - 1)) hP hroot hin
    · change sideChart s (⟨n - 3 + 2, by omega⟩, ⟨0, by omega⟩) ∈ F
      simpa only [he'] using hc1
    · change sideChart s (⟨n - 3 + 2, by omega⟩, ⟨1, by omega⟩) ∈ F
      simpa only [he'] using hn1
  rw [sideChart_position] at hpos ⊢
  dsimp [n] at hlast
  omega

/-- Every preserved off-side boundary contact belongs to an actual pure
carrier in W2. Together with `p=3`, this is the three-carrier off-side frame. -/
theorem cost_two_offside_carrier_pure {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (v : (↑F : Set _)) (hv : v ∈ C.supp)
    (hb : IsGridBoundary v.val) (hs : ¬ OnOpenSide s v.val) :
    C ∈ pureBoundaryCarriers F := by
  by_contra hC
  obtain ⟨w, _, hwr, hadj⟩ := boundary_nonpure_carrier_nextRing_neighbor
    (by omega) F hacyc C hC hv hb
  obtain ⟨a, ha0, han, he⟩ := cost_two_nextRing_chart hn F hacyc s hW w.val w.property hwr
  rw [he] at hadj
  have hvs : OnOpenSide s v.val := by
    fin_cases s <;>
      simp [sideChart, gridGraph, adjacent, Fin.ext_iff] at hadj <;>
      dsimp [OnOpenSide, OnSide] <;> unfold IsGridBoundary at hb <;> omega
  exact hs hvs

/-- The two physical holes are one near each far corner. Their choice of
incident side is retained; no canonical orientation of either hole is assumed. -/
theorem cost_two_exact_far_holes {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) :
    ∃ a b : GridVertex (3 * k + 2) (3 * k + 2),
      (a = (⟨0, by omega⟩, ⟨3 * k, by omega⟩) ∨
        a = (⟨1, by omega⟩, ⟨3 * k + 1, by omega⟩)) ∧
      (b = (⟨3 * k, by omega⟩, ⟨3 * k + 1, by omega⟩) ∨
        b = (⟨3 * k + 1, by omega⟩, ⟨3 * k, by omega⟩)) ∧
      (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) =
        {sideChart s a, sideChart s b} := by
  classical
  let n := 3 * k + 2
  let P : Set (GridVertex n n) := {v | sideChart s v ∈ F}
  have hP := sideChart_acyclic s F hacyc
  let a0 : GridVertex n n := (⟨0, by omega⟩, ⟨3 * k, by omega⟩)
  let a1 : GridVertex n n := (⟨1, by omega⟩, ⟨3 * k + 1, by omega⟩)
  let b0 : GridVertex n n := (⟨3 * k, by omega⟩, ⟨3 * k + 1, by omega⟩)
  let b1 : GridVertex n n := (⟨3 * k + 1, by omega⟩, ⟨3 * k, by omega⟩)
  have ha : a0 ∉ P ∨ a1 ∉ P := by
    have H := grid_cell_has_unforced_edge
      (⟨0, by omega⟩ : Fin (n - 1)) (⟨3 * k, by omega⟩ : Fin (n - 1)) hP
    simp only [cell00, cell01, cell11, cell10] at H
    rcases H with H | H | H | H
    · exact Or.inl H.1
    · exact Or.inr H.2
    · exact Or.inr H.1
    · exact Or.inl H.2
  have hb : b0 ∉ P ∨ b1 ∉ P := by
    have H := grid_cell_has_unforced_edge
      (⟨3 * k, by omega⟩ : Fin (n - 1)) (⟨3 * k, by omega⟩ : Fin (n - 1)) hP
    simp only [cell00, cell01, cell11, cell10] at H
    rcases H with H | H | H | H
    · exact Or.inl H.2
    · exact Or.inl H.1
    · exact Or.inr H.2
    · exact Or.inr H.1
  have choose (u v : GridVertex n n) (h : u ∉ P ∨ v ∉ P) :
      ∃ q, (q = u ∨ q = v) ∧ q ∉ P := by
    rcases h with h | h
    · exact ⟨u, Or.inl rfl, h⟩
    · exact ⟨v, Or.inr rfl, h⟩
  obtain ⟨a, ha, haU⟩ := choose a0 a1 ha
  obtain ⟨b, hb, hbU⟩ := choose b0 b1 hb
  let O := (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)
  have haO : sideChart s a ∈ O := by
    refine mem_filter.mpr ⟨by simp [show sideChart s a ∉ F from haU], ?_⟩
    rcases ha with rfl | rfl <;> simp only [sideChart_boundary, sideChart_openSide] <;>
      dsimp [a0, a1, IsGridBoundary] <;> omega
  have hbO : sideChart s b ∈ O := by
    refine mem_filter.mpr ⟨by simp [show sideChart s b ∉ F from hbU], ?_⟩
    rcases hb with rfl | rfl <;> simp only [sideChart_boundary, sideChart_openSide] <;>
      dsimp [b0, b1, IsGridBoundary] <;> omega
  have hab : sideChart s a ≠ sideChart s b := by
    intro he
    have he' := sideChart_injective s he
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [a0, a1, b0, b1, Prod.ext_iff, Fin.ext_iff] at he'
    omega
  have hsub : {sideChart s a, sideChart s b} ⊆ O :=
    insert_subset haO (singleton_subset_iff.mpr hbO)
  have hO := (cost_two_boundary (by omega) F hacyc s hW).2.1
  refine ⟨a, b, ha, hb, ?_⟩
  exact (eq_of_subset_of_card_le hsub (by simpa [hab] using hO.le)).symm

end GridGraphs.CarrierLayers.ThreeCarrier
