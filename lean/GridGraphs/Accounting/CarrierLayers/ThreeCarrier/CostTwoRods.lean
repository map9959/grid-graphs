import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoRectangle

/-! # Actual nonpure horizontal carriers

Horizontal means varying position along the chosen missing side. The family
includes shallow carriers and excludes singletons; no rod list is postulated.
-/

namespace GridGraphs.CarrierLayers.ThreeCarrier

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

noncomputable def horizontalNonpureCarriers {n : Nat} (F : Finset (GridVertex n n))
    (s : Fin 4) : Finset ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent :=
  univ.filter fun C => C ∉ pureBoundaryCarriers F ∧
    ∃ u ∈ C.supp, ∃ v ∈ C.supp, sidePosition s u.val ≠ sidePosition s v.val

/-- A root carrier is transverse to the missing side: all its vertices have
the root's position. This uses straightness and an actual inward neighbor. -/
theorem root_carrier_constant_position {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (u : (↑F : Set (GridVertex n n))) (hus : OnOpenSide s u.val)
    (v : (↑F : Set (GridVertex n n)))
    (hv : v ∈ (((gridGraph n n).induce (↑F : Set _)).connectedComponentMk u).supp) :
    sidePosition s v.val = sidePosition s u.val := by
  let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk u
  have hu : u ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  obtain ⟨w, hw, hwr, hadj⟩ := missing_side_root_inward hn F hacyc s hmissing u.val u.property hus
  let wF : (↑F : Set _) := ⟨w, hw⟩
  have hwC : wF ∈ C.supp := C.mem_supp_of_adj_mem_supp hu hadj
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · have hur := congrArg Fin.val (hr u hu)
    have hvr := congrArg Fin.val (hr v hv)
    have hwr' := congrArg Fin.val (hr wF hwC)
    change w.1.val = r.val at hwr'
    fin_cases s <;> dsimp [sidePosition, OnOpenSide, OnSide, IsNextRing] at hus hwr ⊢ <;> omega
  · have huc := congrArg Fin.val (hc u hu)
    have hvc := congrArg Fin.val (hc v hv)
    have hwc := congrArg Fin.val (hc wF hwC)
    change w.2.val = c.val at hwc
    fin_cases s <;> dsimp [sidePosition, OnOpenSide, OnSide, IsNextRing] at hus hwr ⊢ <;> omega

/-- All horizontal nonpure carriers are extras beyond the root carriers and
pure carriers. Thus their number is at most z, in particular at most three. -/
theorem horizontal_nonpure_card_le_slack {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 3) :
    (horizontalNonpureCarriers F s).card ≤
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent - (F.filter (OnOpenSide s)).card - 3 ∧
      (horizontalNonpureCarriers F s).card ≤ 3 := by
  have hdisj : Disjoint (horizontalNonpureCarriers F s) (pureBoundaryCarriers F) := by
    apply Finset.disjoint_left.mpr
    intro C hC hpC
    exact (mem_filter.mp hC).2.1 hpC
  have havoid : ∀ u : (↑F : Set (GridVertex (3 * k + 2) (3 * k + 2))), OnOpenSide s u.val →
      ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk u ∉
        horizontalNonpureCarriers F s := by
    intro u hus hC
    obtain ⟨v, hv, w, hw, hne⟩ := (mem_filter.mp hC).2.2
    exact hne ((root_carrier_constant_position (by omega) F hacyc s hmissing u hus v hv).trans
      (root_carrier_constant_position (by omega) F hacyc s hmissing u hus w hw).symm)
  have hcount := missing_side_roots_add_pure_add_extras_le_components F hacyc s hmissing
    (horizontalNonpureCarriers F s) hdisj havoid
  have hprofile := three_pure_missing_side_exact_profile hk F hacyc s hmissing hf hp
  dsimp only at hprofile
  omega

/-- Two chart vertices at the same depth and distinct columns force their
entire actual component to stay at that depth. -/
theorem horizontal_carrier_constant_depth {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (u v w : (↑F : Set _)) (hu : u ∈ C.supp) (hv : v ∈ C.supp) (hw : w ∈ C.supp)
    (a b c : GridVertex n n) (hua : u.val = sideChart s a)
    (hvb : v.val = sideChart s b) (hwc : w.val = sideChart s c)
    (hneq : a.1.val ≠ b.1.val) : c.2.val = a.2.val := by
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨t, ht⟩
  · have h1 := congrArg Fin.val (hr u hu)
    have h2 := congrArg Fin.val (hr v hv)
    have h3 := congrArg Fin.val (hr w hw)
    rw [hua] at h1
    rw [hvb] at h2
    rw [hwc] at h3
    fin_cases s <;> simp [sideChart] at h1 h2 h3 <;> omega
  · have h1 := congrArg Fin.val (ht u hu)
    have h2 := congrArg Fin.val (ht v hv)
    have h3 := congrArg Fin.val (ht w hw)
    rw [hua] at h1
    rw [hvb] at h2
    rw [hwc] at h3
    fin_cases s <;> simp [sideChart] at h1 h2 h3 <;> omega

end GridGraphs.CarrierLayers.ThreeCarrier
