import GridGraphs.Accounting.CarrierLayers.FourCarrier.Capacity

/-! # Weighted cost of endpoint roots

A root at the first or last open-side position makes its adjacent corner a
hole. Three of the four distinct near-corner witnesses must then be off-side.
The corner has weight two and is different from all three witnesses.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Exact weighted partition into open-side holes and off-side deficiency.
The off-side filter retains corners and harmless zero-weight interior vertices. -/
theorem offside_deficiency_add_side_holes {n : Nat} (hn : 2 ≤ n)
    (F : Finset (GridVertex n n)) (s : Fin 4) :
    boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) +
      ((univ \ F).filter (OnOpenSide s)).card =
        boundaryDeficiencySum n n (univ \ F) := by
  have hside : (∑ v ∈ (univ \ F).filter (OnOpenSide s), gridBoundaryDeficiency n n v) =
      ((univ \ F).filter (OnOpenSide s)).card := by
    calc
      _ = ∑ _v ∈ (univ \ F).filter (OnOpenSide s), 1 := by
        apply sum_congr rfl
        intro v hv
        have hs := (mem_filter.mp hv).2
        rw [gridBoundaryDeficiency_eq_four_side_indicators hn hn]
        unfold OnOpenSide OnSide at hs
        split_ifs <;> omega
      _ = _ := by simp
  have h := sum_filter_add_sum_filter_not (univ \ F) (OnOpenSide s)
    (gridBoundaryDeficiency n n)
  rw [hside] at h
  unfold boundaryDeficiencySum
  omega

/-- A root on a missing open side has an actual preserved inward neighbor. -/
theorem missing_side_root_inward {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (v : GridVertex n n) (hv : v ∈ F) (hs : OnOpenSide s v) :
    ∃ w ∈ F, IsNextRing w ∧ (gridGraph n n).Adj v w := by
  let u : (↑F : Set _) := ⟨v, hv⟩
  let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk u
  have hu : u ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have hC : C ∉ pureBoundaryCarriers F := fun h => hmissing C h u hu hs
  obtain ⟨w, _, hw, hadj⟩ := boundary_nonpure_carrier_nextRing_neighbor
    hn F hacyc C hC hu (openSide_boundary hs)
  exact ⟨w.val, w.property, hw, hadj⟩

/-- The corner next to an endpoint root cannot be preserved: otherwise its
actual induced carrier would turn from the boundary into the next ring. -/
theorem endpoint_root_corner_hole {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (v : GridVertex n n) (hv : v ∈ F) (hs : OnOpenSide s v)
    (hend : sidePosition s v = 1 ∨ sidePosition s v = n - 2) :
    ∃ a, BoundarySix.Corner a ∧ (gridGraph n n).Adj a v ∧ a ∉ F := by
  classical
  let t : Fin n := ⟨if sidePosition s v = 1 then 0 else n - 1, by split <;> omega⟩
  let a : GridVertex n n := if s.val < 2 then (v.1, t) else (t, v.2)
  have ha : BoundarySix.Corner a ∧ (gridGraph n n).Adj a v := by
    unfold a t
    unfold OnOpenSide OnSide at hs
    unfold sidePosition at hend
    dsimp [sidePosition]
    split_ifs at * <;>
      simp [BoundarySix.Corner, gridGraph, adjacent, Fin.ext_iff] <;> omega
  refine ⟨a, ha.1, ha.2, ?_⟩
  intro haF
  let u : (↑F : Set _) := ⟨v, hv⟩
  let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk u
  have hu : u ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have hC : C ∉ pureBoundaryCarriers F := fun h => hmissing C h u hu hs
  obtain ⟨w, hwC, hwr, _⟩ := boundary_nonpure_carrier_nextRing_neighbor
    hn F hacyc C hC hu (openSide_boundary hs)
  have haC : (⟨a, haF⟩ : (↑F : Set _)) ∈ C.supp :=
    C.mem_supp_of_adj_mem_supp hu ha.2.symm
  have hac := ha.1
  have hadj := ha.2
  unfold BoundarySix.Corner at hac
  unfold OnOpenSide OnSide at hs
  unfold IsNextRing at hwr
  simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · have hvr := congrArg Fin.val (hr u hu)
    have har := congrArg Fin.val (hr _ haC)
    have hwr' := congrArg Fin.val (hr w hwC)
    change a.1.val = r.val at har
    change w.val.1.val = r.val at hwr'
    dsimp [u] at hvr
    omega
  · have hvc := congrArg Fin.val (hc u hu)
    have hac' := congrArg Fin.val (hc _ haC)
    have hwc := congrArg Fin.val (hc w hwC)
    change a.2.val = c.val at hac'
    change w.val.2.val = c.val at hwc
    dsimp [u] at hvc
    omega

/-- An endpoint root costs at least five weighted off-side units, independently
of root count, pure-carrier count, or the global score. -/
theorem endpoint_root_offside_deficiency_ge_five {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (v : GridVertex n n) (hv : v ∈ F) (hs : OnOpenSide s v)
    (hend : sidePosition s v = 1 ∨ sidePosition s v = n - 2) :
    5 ≤ boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) := by
  classical
  obtain ⟨a, hac, _, haU⟩ := endpoint_root_corner_hole (by omega) F hacyc s hmissing v hv hs hend
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := BoundarySix.corner_witnesses hn F hacyc
  have hpos (u : GridVertex n n) (hus : OnOpenSide s u) (hun : BoundarySix.Near u) :
      sidePosition s u = 1 ∨ sidePosition s u = n - 2 := by
    unfold OnOpenSide OnSide at hus
    unfold BoundarySix.Near at hun
    unfold sidePosition
    split <;> omega
  have hsmall : (Q.filter (OnOpenSide s)).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    have hxs := (mem_filter.mp hx).2
    have hys := (mem_filter.mp hy).2
    have hxp := hpos x hxs (hQnear x (mem_filter.mp hx).1)
    have hyp := hpos y hys (hQnear y (mem_filter.mp hy).1)
    have hxne : sidePosition s x ≠ sidePosition s v := by
      intro he
      have heq := sidePosition_injective hxs hs he
      exact (mem_sdiff.mp (hQU (mem_filter.mp hx).1)).2 (heq ▸ hv)
    have hyne : sidePosition s y ≠ sidePosition s v := by
      intro he
      have heq := sidePosition_injective hys hs he
      exact (mem_sdiff.mp (hQU (mem_filter.mp hy).1)).2 (heq ▸ hv)
    exact sidePosition_injective hxs hys (by omega)
  let R := Q.filter (fun u => ¬ OnOpenSide s u)
  let O := (univ \ F).filter (fun u => ¬ OnOpenSide s u)
  have hpart := card_filter_add_card_filter_not (s := Q) (p := OnOpenSide s)
  have hR : 3 ≤ R.card := by dsimp [R]; omega
  have hsub : insert a R ⊆ O := by
    apply insert_subset
    · apply mem_filter.mpr
      refine ⟨by simp [haU], ?_⟩
      unfold BoundarySix.Corner at hac
      unfold OnOpenSide OnSide
      omega
    · intro u hu
      exact mem_filter.mpr ⟨hQU (mem_filter.mp hu).1, (mem_filter.mp hu).2⟩
  have haR : a ∉ R := by
    intro h
    have hnear := hQnear a (mem_filter.mp h).1
    unfold BoundarySix.Corner at hac
    unfold BoundarySix.Near at hnear
    omega
  have hweight : gridBoundaryDeficiency n n a = 2 := by
    rw [gridBoundaryDeficiency_eq_four_side_indicators (by omega) (by omega)]
    unfold BoundarySix.Corner at hac
    split_ifs <;> omega
  have hRsum : R.card ≤ ∑ u ∈ R, gridBoundaryDeficiency n n u := by
    calc
      _ = ∑ _u ∈ R, 1 := by simp
      _ ≤ _ := sum_le_sum (by
        intro u hu
        apply one_le_gridBoundaryDeficiency_of_boundary (by omega) (by omega)
        have hnear := hQnear u (mem_filter.mp hu).1
        unfold BoundarySix.Near at hnear
        unfold IsGridBoundary
        omega)
  have hsum := sum_le_sum_of_subset_of_nonneg hsub
    (f := gridBoundaryDeficiency n n) (by simp)
  rw [sum_insert haR, hweight] at hsum
  change 5 ≤ ∑ u ∈ O, gridBoundaryDeficiency n n u
  omega

/-- Weighted off-side budget at most four removes both endpoint positions. -/
theorem root_positions_of_offside_deficiency_le_four {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hW : boundaryDeficiencySum n n ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 4)
    (v : GridVertex n n) (hv : v ∈ F) (hs : OnOpenSide s v) :
    2 ≤ sidePosition s v ∧ sidePosition s v < n - 2 := by
  have hb := sidePosition_bounds hs
  have hne : ¬ (sidePosition s v = 1 ∨ sidePosition s v = n - 2) := by
    intro h
    have hfive := endpoint_root_offside_deficiency_ge_five hn F hacyc s hmissing v hv hs h
    omega
  omega

end GridGraphs.CarrierLayers.FourCarrier
