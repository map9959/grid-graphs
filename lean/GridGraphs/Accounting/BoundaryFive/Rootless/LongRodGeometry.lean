import GridGraphs.Accounting.BoundaryFive.Rootless.Geometry
import GridGraphs.Accounting.BoundaryFive.Rootless.LongRods
import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoEdgeGeometry

/-!
# Actual-grid validation of the long-rod local restrictions

The contact and distance-two hypotheses in LongRods follow from actual
induced-component membership and forced acyclicity. `Rod.Represents` records
the full physical interval, in both directions; it does not assume a length
or a deficit. RodInventory uses these results to count actual carriers.
-/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph

def Rod.vertex {m : Nat} (R : Rod m) (j : Fin m) : GridVertex m m :=
  if R.horizontal = true then (R.axis, j) else (j, R.axis)

theorem Rod.vertex_injective {m : Nat} (R : Rod m) : Function.Injective R.vertex := by
  intro i j he
  by_cases hd : R.horizontal = true <;> simpa [Rod.vertex, hd] using he

structure Rod.Represents {m : Nat} (R : Rod m) (F : Set (GridVertex m m))
    (C : ((gridGraph m m).induce F).ConnectedComponent) : Prop where
  mem : ∀ j : Fin m, j.val ∈ R.span →
    ∃ hjF : R.vertex j ∈ F, (⟨R.vertex j, hjF⟩ : F) ∈ C.supp
  cover : ∀ v ∈ C.supp, ∃ j : Fin m, j.val ∈ R.span ∧ R.vertex j = v.1

theorem Rod.Represents.card {m : Nat} {R : Rod m} {F : Set (GridVertex m m)}
    {C : ((gridGraph m m).induce F).ConnectedComponent} (h : R.Represents F C) :
    C.supp.ncard = R.length := by
  classical
  rw [Set.ncard_eq_toFinset_card', ← R.span_card]
  let f (j : Nat) (hj : j ∈ R.span) : F :=
    ⟨R.vertex ⟨j, mem_range.mp (R.span_subset hj)⟩, (h.mem _ hj).choose⟩
  have hf (j : Nat) (hj : j ∈ R.span) : f j hj ∈ C.supp := (h.mem _ hj).choose_spec
  symm
  apply card_bij f
  · intro j hj
    exact Set.mem_toFinset.mpr (hf j hj)
  · intro i hi j hj he
    have he' := R.vertex_injective (congrArg Subtype.val he)
    exact congrArg Fin.val he'
  · intro v hv
    obtain ⟨j, hj, he⟩ := h.cover v (Set.mem_toFinset.mp hv)
    exact ⟨j.val, hj, Subtype.ext he⟩

/-- Actual distinct carriers have no Chebyshev-distance-one pair. Equality
and grid adjacency merge the carriers; the diagonal case forces a four-cycle. -/
theorem distinct_components_far {m : Nat} {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    (C D : ((gridGraph m m).induce F).ConnectedComponent) (hne : C ≠ D)
    (u v : F) (hu : u ∈ C.supp) (hv : v ∈ D.supp) :
    u.1.1.val + 1 < v.1.1.val ∨ v.1.1.val + 1 < u.1.1.val ∨
      u.1.2.val + 1 < v.1.2.val ∨ v.1.2.val + 1 < u.1.2.val := by
  have hneq : u ≠ v := by
    intro he
    exact hne (ConnectedComponent.eq_of_common_vertex (he ▸ hu) hv)
  have hnoadj : ¬ (gridGraph m m).Adj u.1 v.1 := by
    intro he
    exact hne (ConnectedComponent.eq_of_common_vertex (C.mem_supp_of_adj_mem_supp hu he) hv)
  by_contra hn
  by_cases hr : u.1.1 = v.1.1
  · by_cases hc : u.1.2 = v.1.2
    · exact hneq (Subtype.ext (Prod.ext hr hc))
    · apply hnoadj
      left
      refine ⟨hr, ?_⟩
      have hc' : u.1.2.val ≠ v.1.2.val := fun he => hc (Fin.ext he)
      omega
  · by_cases hc : u.1.2 = v.1.2
    · apply hnoadj
      right
      refine ⟨hc, ?_⟩
      have hr' : u.1.1.val ≠ v.1.1.val := fun he => hr (Fin.ext he)
      omega
    · have hr' : u.1.1.val ≠ v.1.1.val := fun he => hr (Fin.ext he)
      have hc' : u.1.2.val ≠ v.1.2.val := fun he => hc (Fin.ext he)
      exact CarrierLayers.ThreeCarrier.diagonal_preserved_false F hacyc u.1 v.1 u.2 v.2
        (by omega) (by omega)

theorem Rod.Represents.separated {m : Nat} {R S : Rod m} {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    {C D : ((gridGraph m m).induce F).ConnectedComponent} (hne : C ≠ D)
    (hR : R.Represents F C) (hS : S.Represents F D) : R.Separated S := by
  intro x hx y hy
  let x' : Fin m := ⟨x, mem_range.mp (R.span_subset hx)⟩
  let y' : Fin m := ⟨y, mem_range.mp (S.span_subset hy)⟩
  obtain ⟨hxF, hxC⟩ := hR.mem x' hx
  obtain ⟨hyF, hyD⟩ := hS.mem y' hy
  have h := distinct_components_far hacyc C D hne _ _ hxC hyD
  by_cases hr : R.horizontal = true <;> by_cases hs : S.horizontal = true <;>
    simpa [Rod.vertex, Rod.point, hr, hs, x', y'] using h

theorem transpose_forced_acyclic {m : Nat} {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic) :
    (forcedEdgeGraph (gridGraph m m) {v | v.swap ∈ F}).IsAcyclic := by
  let f : forcedEdgeGraph (gridGraph m m) {v | v.swap ∈ F} →g
      forcedEdgeGraph (gridGraph m m) F :=
    ⟨Prod.swap, fun {u v} h => ⟨by
      simpa only [gridGraph, adjacent, Prod.fst_swap, Prod.snd_swap, or_comm] using h.1, h.2⟩⟩
  exact hacyc.comap f (by intro x y h; exact Prod.swap_injective h)

/-- The local distance-two length bound is a forced rectangle six-cycle
consequence in either orientation. No separation or root assumption is used. -/
theorem Rod.Represents.two_step {m : Nat} {R S : Rod m} {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    {C D : ((gridGraph m m).induce F).ConnectedComponent}
    (hR : R.Represents F C) (hS : S.Represents F D)
    (hdir : R.horizontal = S.horizontal)
    (hdist : R.axis.val + 2 = S.axis.val ∨ S.axis.val + 2 = R.axis.val) :
    R.length + S.length ≤ m + 1 := by
  have hmemR (j : Fin m) (hj : j ∈ Icc R.lo R.hi) : R.vertex j ∈ F :=
    (hR.mem j (by simpa only [Rod.span, mem_Icc, Fin.le_iff_val_le_val] using hj)).1
  have hmemS (j : Fin m) (hj : j ∈ Icc S.lo S.hi) : S.vertex j ∈ F :=
    (hS.mem j (by simpa only [Rod.span, mem_Icc, Fin.le_iff_val_le_val] using hj)).1
  have hcard (T : Rod m) : (Icc T.lo T.hi).card = T.length := by
    simp [Rod.length]
  by_cases hs : S.horizontal = true
  · have hr : R.horizontal = true := hdir.trans hs
    simp only [Rod.vertex, hr, hs, if_true] at hmemR hmemS
    rcases hdist with hdist | hdist
    · simpa only [hcard] using horizontal_carrier_card_sum_le hacyc R.axis S.axis hdist
        R.lo R.hi S.lo S.hi hmemR hmemS
    · have h := horizontal_carrier_card_sum_le hacyc S.axis R.axis hdist
        S.lo S.hi R.lo R.hi hmemS hmemR
      simpa only [hcard, Nat.add_comm] using h
  · have hr : R.horizontal ≠ true := fun h => hs (hdir ▸ h)
    simp only [Rod.vertex, if_neg hr, if_neg hs] at hmemR hmemS
    have hac := transpose_forced_acyclic hacyc
    rcases hdist with hdist | hdist
    · simpa only [hcard] using horizontal_carrier_card_sum_le hac R.axis S.axis hdist
        R.lo R.hi S.lo S.hi hmemR hmemS
    · have h := horizontal_carrier_card_sum_le hac S.axis R.axis hdist
        S.lo S.hi R.lo R.hi hmemS hmemR
      simpa only [hcard, Nat.add_comm] using h

/-- A nontrivial represented carrier cannot run along the square boundary:
its two endpoints would be distinct boundary roots in one forced component. -/
theorem Rod.Represents.interior_axis {m : Nat} {R : Rod m} {F : Set (GridVertex m m)}
    {C : ((gridGraph m m).induce F).ConnectedComponent} (hR : R.Represents F C)
    (hroot : UniqueBoundaryRoots F) (hlong : 1 < R.length) :
    1 ≤ R.axis.val ∧ R.axis.val + 1 < m := by
  have hlo : R.lo.val ∈ R.span := by exact mem_Icc.mpr ⟨le_rfl, R.ordered⟩
  have hhi : R.hi.val ∈ R.span := by exact mem_Icc.mpr ⟨R.ordered, le_rfl⟩
  obtain ⟨hlF, hlC⟩ := hR.mem R.lo hlo
  obtain ⟨hhF, hhC⟩ := hR.mem R.hi hhi
  have hne : R.lo ≠ R.hi := by
    intro he
    have := R.ordered
    dsimp [Rod.length] at hlong
    have hv := congrArg Fin.val he
    omega
  by_contra hn
  have hb : R.axis.val = 0 ∨ R.axis.val + 1 = m := by have := R.axis.isLt; omega
  have boundary (j : Fin m) : IsGridBoundary (R.vertex j) := by
    by_cases hd : R.horizontal = true <;>
      simp [Rod.vertex, hd, IsGridBoundary] <;> omega
  have he := hroot _ hlF _ hhF (boundary _) (boundary _)
    (induced_reachable_forced (C.reachable_of_mem_supp hlC hhC))
  exact hne (R.vertex_injective he)

end GridGraphs.BoundaryFive.Rootless
