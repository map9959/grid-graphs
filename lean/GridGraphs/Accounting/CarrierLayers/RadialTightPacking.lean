import GridGraphs.Accounting.CarrierLayers.RadialTightBoundary
import Mathlib.Data.Finset.Sort

/-!
# Exact phase of tight radial packing

Equality in the radial boundary budget leaves no slack after deleting the
two endpoint positions. This is a necessary condition, not an exclusion of
the equality case.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- A three-spaced set of `k` positions between `2` and `3k-1` is precisely
the arithmetic progression `2, 5, ..., 3k-1`. -/
theorem tight_three_spaced_positions {k : Nat} (hk : 1 ≤ k) (S : Finset Nat)
    (hcard : S.card = k)
    (hbound : ∀ x ∈ S, 2 ≤ x ∧ x < 3 * k)
    (hspace : ∀ x ∈ S, ∀ y ∈ S, x < y → x + 3 ≤ y) :
    ∀ x, x ∈ S ↔ ∃ i < k, x = 3 * i + 2 := by
  let e := S.orderEmbOfFin hcard
  have hmem (i : Fin k) : e i ∈ S := S.orderEmbOfFin_mem hcard i
  have hslope (d : Nat) : ∀ (i : Nat) (hi : i < k) (hd : i + d < k),
      e ⟨i, hi⟩ + 3 * d ≤ e ⟨i + d, hd⟩ := by
    induction d with
    | zero => intro i hi hd; simp
    | succ d ih =>
      intro i hi hd
      have hid : i + d < k := by omega
      have hprev := ih i hi hid
      have hlt : e ⟨i + d, hid⟩ < e ⟨i + (d + 1), hd⟩ :=
        e.strictMono (by simp)
      have hnext := hspace _ (hmem ⟨i + d, hid⟩) _ (hmem ⟨i + (d + 1), hd⟩) hlt
      omega
  have he (i : Fin k) : e i = 3 * i.val + 2 := by
    have hlo := (hbound _ (hmem ⟨0, by omega⟩)).1
    have hhi := (hbound _ (hmem ⟨k - 1, by omega⟩)).2
    have hleft := hslope i.val 0 (by omega) (by simp)
    have hright := hslope (k - 1 - i.val) i.val i.isLt (by omega)
    have hidx : i.val + (k - 1 - i.val) = k - 1 := by omega
    simp only [Nat.zero_add] at hleft
    simp only [hidx] at hright
    change e ⟨0, by omega⟩ + 3 * i.val ≤ e i at hleft
    change e i + 3 * (k - 1 - i.val) ≤ e ⟨k - 1, by omega⟩ at hright
    omega
  intro x
  constructor
  · intro hx
    let i := (S.orderIsoOfFin hcard).symm ⟨x, hx⟩
    refine ⟨i.val, i.isLt, ?_⟩
    have hix : e i = x := congrArg Subtype.val ((S.orderIsoOfFin hcard).apply_symm_apply ⟨x, hx⟩)
    rw [← hix]
    exact he i
  · rintro ⟨i, hi, rfl⟩
    rw [← he ⟨i, hi⟩]
    exact hmem ⟨i, hi⟩

/-- Every vertex on a missing pure-carrier side is preserved exactly when its
position is `3i+2`, for `i < k`, at boundary budget `2k+2`.
No maximality, cardinality lower bound, or global bound on pure carriers is
needed once the missing side is supplied. -/
theorem tight_missing_side_exact_phase {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 2)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    ∀ v, OnOpenSide s v → (v ∈ F ↔ ∃ i < k, sidePosition s v = 3 * i + 2) := by
  classical
  let A := F.filter (OnOpenSide s)
  let S := A.image (sidePosition s)
  have hcardA : A.card = k := (tight_missing_side_boundary hk F hacyc hb s hmissing).1
  have hcard : S.card = k := by
    rw [card_image_iff.mpr, hcardA]
    intro u hu v hv he
    exact sidePosition_injective (mem_filter.mp hu).2 (mem_filter.mp hv).2 he
  have hneighbor (u : A) : ∃ w : GridVertex (3 * k + 2) (3 * k + 2),
      w ∈ F ∧ IsNextRing w ∧ (gridGraph (3 * k + 2) (3 * k + 2)).Adj u.val w := by
    let v : (↑F : Set _) := ⟨u.val, (mem_filter.mp u.property).1⟩
    let C := ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).connectedComponentMk v
    have hv : v ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
    have hC : C ∉ pureBoundaryCarriers F := fun h =>
      hmissing C h v hv (mem_filter.mp u.property).2
    obtain ⟨w, _, hwr, hadj⟩ := boundary_nonpure_carrier_nextRing_neighbor
      (by omega) F hacyc C hC hv (openSide_boundary (mem_filter.mp u.property).2)
    exact ⟨w.val, w.property, hwr, hadj⟩
  have hbound : ∀ x ∈ S, 2 ≤ x ∧ x < 3 * k := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    obtain ⟨hvF, hvs⟩ := mem_filter.mp hv
    have hbounds := sidePosition_bounds hvs
    have hnotend : sidePosition s v ≠ 1 ∧ sidePosition s v ≠ 3 * k := by
      have hnear : sidePosition s v = 1 ∨ sidePosition s v = 3 * k → BoundarySix.Near v := by
        intro he
        have hs := hvs
        unfold OnOpenSide OnSide at hs
        unfold sidePosition at he
        unfold BoundarySix.Near
        split at he <;> omega
      constructor <;> intro he
      · exact tight_missing_side_endpoints_unpreserved hk F hacyc hb s hmissing
          v hvs (hnear (Or.inl he)) hvF
      · exact tight_missing_side_endpoints_unpreserved hk F hacyc hb s hmissing
          v hvs (hnear (Or.inr he)) hvF
    omega
  have hspace : ∀ x ∈ S, ∀ y ∈ S, x < y → x + 3 ≤ y := by
    intro x hx y hy hlt
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
    obtain ⟨w, hw, hwr, huw⟩ := hneighbor ⟨u, hu⟩
    obtain ⟨z, hz, hzr, hvz⟩ := hneighbor ⟨v, hv⟩
    exact radial_pair_spacing (by omega) F hacyc s
      (mem_filter.mp hu).1 (mem_filter.mp hv).1 hw hz
      (mem_filter.mp hu).2 (mem_filter.mp hv).2 hwr hzr huw hvz hlt
  have hphase := tight_three_spaced_positions (by omega) S hcard hbound hspace
  intro v hvs
  rw [← hphase]
  constructor
  · intro hv
    exact mem_image.mpr ⟨v, mem_filter.mpr ⟨hv, hvs⟩, rfl⟩
  · intro hv
    obtain ⟨u, hu, he⟩ := mem_image.mp hv
    have huv := sidePosition_injective (mem_filter.mp hu).2 hvs he
    exact huv ▸ (mem_filter.mp hu).1

/-- The at-most-three branch has a missing side with the exact phase above
whenever its boundary budget is tight. -/
theorem tight_pure_carriers_le_three_exact_phase {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 2) :
    ∃ s : Fin 4,
      (∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val) ∧
      ∀ v, OnOpenSide s v → (v ∈ F ↔ ∃ i < k, sidePosition s v = 3 * i + 2) := by
  obtain ⟨s, hs⟩ := exists_side_without_pure_carrier (by omega) F hacyc hp
  exact ⟨s, hs, tight_missing_side_exact_phase hk F hacyc hb s hs⟩

end GridGraphs.CarrierLayers
