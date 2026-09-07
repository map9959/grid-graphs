import GridGraphs.Accounting.CarrierLayers.FourCarrier.SaturatedBoundary

/-! # Five physical pure carriers at root saturation

The two missing-side corners are isolated in the preserved graph. Three pairs
of adjacent preserved vertices on the other sides give three more pure carriers.
The count concerns actual induced components, including the two singletons.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

private theorem corner_carrier_pure {n : Nat} (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (u : (↑F : Set (GridVertex n n))) (hu : u ∈ C.supp) (hc : BoundarySix.Corner u.val) :
    C ∈ pureBoundaryCarriers F := by
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  intro v hv
  unfold BoundarySix.Corner at hc
  unfold IsGridBoundary
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc'⟩
  · have hu' := congrArg Fin.val (hr u hu)
    have hv' := congrArg Fin.val (hr v hv)
    omega
  · have hu' := congrArg Fin.val (hc' u hu)
    have hv' := congrArg Fin.val (hc' v hv)
    omega

private theorem adjacent_boundary_carrier_pure {n : Nat} (hn : 3 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (u v : (↑F : Set (GridVertex n n))) (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (hub : IsGridBoundary u.val) (hvb : IsGridBoundary v.val)
    (hadj : (gridGraph n n).Adj u.val v.val) : C ∈ pureBoundaryCarriers F := by
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  intro w hw
  unfold IsGridBoundary at hub hvb ⊢
  simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · have hu' := congrArg Fin.val (hr u hu)
    have hv' := congrArg Fin.val (hr v hv)
    have hw' := congrArg Fin.val (hr w hw)
    omega
  · have hu' := congrArg Fin.val (hc u hu)
    have hv' := congrArg Fin.val (hc v hv)
    have hw' := congrArg Fin.val (hc w hw)
    omega

private theorem chart_common_side {n : Nat} (s t : Fin 4) (u v : GridVertex n n)
    (hu : OnSide t (sideChart s u)) (hv : OnSide t (sideChart s v)) :
    (u.1.val = 0 ∧ v.1.val = 0) ∨ (u.1.val + 1 = n ∧ v.1.val + 1 = n) ∨
      (u.2.val = 0 ∧ v.2.val = 0) ∨ (u.2.val + 1 = n ∧ v.2.val + 1 = n) := by
  fin_cases s <;> simp [sideChart, OnSide] at hu hv <;> omega

/-- Full root saturation with `W<=4` forces at least five actual pure carriers.
This needs no counterexample score hypothesis or assumption on `p`. -/
theorem saturated_missing_side_five_pure {k : Nat} (hk : 3 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hq : (F.filter (OnOpenSide s)).card = k)
    (hW : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) ≤ 4) :
    5 ≤ (pureBoundaryCarriers F).card := by
  classical
  let n := 3 * k + 2
  obtain ⟨_, hnear0, hnear1, hholes⟩ :=
    saturated_missing_side_boundary hk F hacyc s hmissing hq hW
  have hend : n - 1 = 3 * k + 1 := by omega
  have hfill (u : GridVertex n n) (hb : IsGridBoundary u)
      (hs : ¬ (u.2.val = 0 ∧ 0 < u.1.val ∧ u.1.val + 1 < n))
      (hn : ¬ BoundarySix.Near u) : sideChart s u ∈ F := by
    by_contra hu
    exact hn ((sideChart_near s u).mp (hholes _ ((sideChart_boundary s u).mpr hb)
      (fun h => hs ((sideChart_openSide s u).mp h)) hu))
  let x (i : Fin 5) : GridVertex n n :=
    if i.val = 0 then (⟨0, by omega⟩, ⟨0, by omega⟩)
    else if i.val = 1 then (⟨n - 1, by omega⟩, ⟨0, by omega⟩)
    else if i.val = 2 then (⟨0, by omega⟩, ⟨2, by omega⟩)
    else if i.val = 3 then (⟨2, by omega⟩, ⟨n - 1, by omega⟩)
    else (⟨n - 1, by omega⟩, ⟨2, by omega⟩)
  have hxB (i : Fin 5) : IsGridBoundary (x i) := by
    fin_cases i <;> simp [x, IsGridBoundary] <;> omega
  have hxF (i : Fin 5) : sideChart s (x i) ∈ F := by
    apply hfill (x i) (hxB i)
    · fin_cases i <;> simp [x] <;> omega
    · fin_cases i <;> simp [x, BoundarySix.Near] <;> omega
  have hxinj : Function.Injective x := by
    intro i j he
    have hr := congrArg (fun v : GridVertex n n => v.1.val) he
    have hc := congrArg (fun v : GridVertex n n => v.2.val) he
    apply Fin.ext
    fin_cases i <;> fin_cases j <;> simp [x] at hr hc ⊢ <;> omega
  let y (i : Fin 5) : GridVertex n n :=
    if i.val = 2 then (⟨0, by omega⟩, ⟨3, by omega⟩)
    else if i.val = 3 then (⟨3, by omega⟩, ⟨n - 1, by omega⟩)
    else (⟨n - 1, by omega⟩, ⟨3, by omega⟩)
  have hyB (i : Fin 5) : IsGridBoundary (y i) := by
    fin_cases i <;> simp [y, IsGridBoundary] <;> omega
  have hyF (i : Fin 5) : sideChart s (y i) ∈ F := by
    apply hfill (y i) (hyB i)
    · fin_cases i <;> simp [y]
      omega
    · fin_cases i <;> simp [y, BoundarySix.Near] <;> omega
  have hxy (i : Fin 5) (hi : 2 ≤ i.val) : (gridGraph n n).Adj (x i) (y i) := by
    simp only [gridGraph, adjacent, Fin.ext_iff]
    have hcases : i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
    rcases hcases with he | he | he <;>
      norm_num only [x, y, he, ite_true, ite_false] <;> simp
  let G := (gridGraph n n).induce (↑F : Set _)
  let u (i : Fin 5) : (↑F : Set (GridVertex n n)) := ⟨sideChart s (x i), hxF i⟩
  let C (i : Fin 5) := G.connectedComponentMk (u i)
  have hu (i : Fin 5) : u i ∈ (C i).supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have hpure (i : Fin 5) : C i ∈ pureBoundaryCarriers F := by
    by_cases hi : i.val < 2
    · apply corner_carrier_pure F hacyc (C i) (u i) (hu i)
      apply (sideChart_corner s _).mpr
      fin_cases i <;> simp [x, BoundarySix.Corner] at hi ⊢
      omega
    · let v : (↑F : Set (GridVertex n n)) := ⟨sideChart s (y i), hyF i⟩
      have hadj : G.Adj (u i) v := (sideChart_adj s _ _).mpr (hxy i (by omega))
      have hv : v ∈ (C i).supp := (C i).mem_supp_of_adj_mem_supp (hu i) hadj
      exact adjacent_boundary_carrier_pure (by omega) F hacyc (C i) (u i) v (hu i) hv
        ((sideChart_boundary s _).mpr (hxB i)) ((sideChart_boundary s _).mpr (hyB i)) hadj
  have hsideHole (t : Fin n) (ht : t.val = 1 ∨ t.val = n - 2) :
      sideChart s (t, ⟨0, by omega⟩) ∉ F := by
    intro hv
    have hs := (sideChart_openSide s (t, ⟨0, by omega⟩)).mpr (by dsimp; omega)
    have hpos := root_positions_of_offside_deficiency_le_four (by omega) F hacyc s hmissing
      hW _ hv hs
    rw [sideChart_position] at hpos
    dsimp at hpos
    omega
  have hiso (i : Fin 5) (hi : i.val < 2) (v : (↑F : Set (GridVertex n n))) :
      ¬ G.Adj (u i) v := by
    intro hadj
    obtain ⟨z, hz⟩ := sideChart_surjective s v.val
    have hadj' : (gridGraph n n).Adj (x i) z := by
      apply (sideChart_adj s _ _).mp
      rw [hz]
      exact hadj
    have hgeom :
        (i.val = 0 ∧ (z = (⟨1, by omega⟩, ⟨0, by omega⟩) ∨
          z = (⟨0, by omega⟩, ⟨1, by omega⟩))) ∨
        (i.val = 1 ∧ (z = (⟨n - 2, by omega⟩, ⟨0, by omega⟩) ∨
          z = (⟨n - 1, by omega⟩, ⟨1, by omega⟩))) := by
      have hcases : i.val = 0 ∨ i.val = 1 := by omega
      simp only [gridGraph, adjacent, Fin.ext_iff] at hadj'
      simp only [Prod.ext_iff, Fin.ext_iff]
      rcases hcases with he | he <;>
        norm_num only [x, he, ite_true, ite_false] at hadj' ⊢ <;>
        simp only [true_and, false_and, false_or, or_false] <;> omega
    have hzF : sideChart s z ∈ F := hz ▸ v.property
    rcases hgeom with ⟨_, rfl | rfl⟩ | ⟨_, rfl | rfl⟩
    · exact hsideHole _ (Or.inl rfl) hzF
    · exact hnear0 hzF
    · exact hsideHole _ (Or.inr rfl) hzF
    · apply hnear1
      simpa only [hend] using hzF
  have hisoeq (i j : Fin 5) (hi : i.val < 2) (he : C i = C j) : i = j := by
    have hr : G.Reachable (u i) (u j) := ConnectedComponent.exact he
    have hue : u i = u j := by
      by_contra hne
      have hm := mem_support_of_reachable hne hr
      obtain ⟨z, hz⟩ := (mem_support G).mp hm
      exact hiso i hi z hz
    exact hxinj (sideChart_injective s (congrArg Subtype.val hue))
  have hCinj : Function.Injective C := by
    intro i j he
    by_cases hi : i.val < 2
    · exact hisoeq i j hi he
    by_cases hj : j.val < 2
    · exact (hisoeq j i hj he.symm).symm
    obtain ⟨t, ht⟩ := pure_carrier_on_side (by omega) F hacyc (C j) (hpure j)
    have hui : u i ∈ (C j).supp := he ▸ hu i
    have hsides := chart_common_side s t (x i) (x j) (ht _ hui) (ht _ (hu j))
    fin_cases i <;> fin_cases j <;> simp [x] at hi hj hsides ⊢ <;> omega
  let f : Fin 5 → pureBoundaryCarriers F := fun i => ⟨C i, hpure i⟩
  have hf : Function.Injective f := fun _ _ he => hCinj (congrArg Subtype.val he)
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hf

end GridGraphs.CarrierLayers.FourCarrier
