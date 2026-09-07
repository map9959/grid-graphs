import GridGraphs.Accounting.CarrierLayers.OneExcessSeparated
import GridGraphs.Geometry.CarrierPacking

/-!
# Concentrated missing-side gaps

Six-cycle spacing bounds the roots outside a single empty interval. This
controls concentration even when inward witnesses reuse the same carrier.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

private theorem spaced_card_bound (A : Finset Nat) (lo hi : Nat)
    (hbound : ∀ x ∈ A, lo ≤ x ∧ x ≤ hi)
    (hspace : ∀ x ∈ A, ∀ y ∈ A, x < y → x + 3 ≤ y) :
    3 * A.card ≤ hi - lo + 3 := by
  classical
  let f : A → Fin ((hi - lo) / 3 + 1) := fun x =>
    ⟨(x.val - lo) / 3, by have h := hbound x.val x.property; omega⟩
  have hinj : Function.Injective f := by
    intro x y he
    have he' := congrArg Fin.val he
    have hx := hbound x.val x.property
    have hy := hbound y.val y.property
    dsimp [f] at he'
    apply Subtype.ext
    rcases lt_trichotomy x.val y.val with h | h | h
    · have := hspace x.val x.property y.val y.property h
      omega
    · exact h
    · have := hspace y.val y.property x.val x.property h
      omega
  have h := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe, Fintype.card_fin] at h
  omega

/-- A root-free interval of length `L` costs at least `(L-4)/3` missing
roots. The four-unit endpoint allowance includes gaps touching an open-side
endpoint; no endpoint preservation is assumed. -/
theorem missing_side_gap_length_budget {k : Nat} (hk : 1 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (a b : Nat) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3 * k)
    (hgap : ∀ u ∈ F, OnOpenSide s u → a ≤ sidePosition s u →
      sidePosition s u ≤ b → False) :
    3 * (F.filter (OnOpenSide s)).card + (b - a + 1) ≤ 3 * k + 4 := by
  classical
  let S := F.filter (OnOpenSide s)
  have hneighbor (u : S) : ∃ w : GridVertex (3 * k + 2) (3 * k + 2),
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
  let A := S.image (sidePosition s)
  have hA : A.card = S.card := by
    apply card_image_iff.mpr
    intro u hu v hv he
    exact sidePosition_injective (mem_filter.mp hu).2 (mem_filter.mp hv).2 he
  have hspace : ∀ x ∈ A, ∀ y ∈ A, x < y → x + 3 ≤ y := by
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
    obtain ⟨w, hw, hwr, huw⟩ := hneighbor ⟨u, hu⟩
    obtain ⟨z, hz, hzr, hvz⟩ := hneighbor ⟨v, hv⟩
    exact radial_pair_spacing (by omega) F hacyc s
      (mem_filter.mp hu).1 (mem_filter.mp hv).1 hw hz
      (mem_filter.mp hu).2 (mem_filter.mp hv).2 hwr hzr huw hvz hxy
  have hbounds : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 3 * k ∧ (x < a ∨ b < x) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    have hs := (mem_filter.mp hu).2
    have := sidePosition_bounds hs
    refine ⟨by omega, by omega, ?_⟩
    by_contra h
    exact hgap u (mem_filter.mp hu).1 hs (by omega) (by omega)
  let L := A.filter (fun x => x < a)
  let R := A.filter (fun x => ¬ x < a)
  have hL : 3 * L.card ≤ a + 1 := by
    by_cases he : L = ∅
    · simp [he]
    have h := spaced_card_bound L 1 (a - 1)
      (by intro x hx; have := (mem_filter.mp hx).2
          have := hbounds x (mem_filter.mp hx).1; omega)
      (by intro x hx y hy; exact hspace x (mem_filter.mp hx).1 y (mem_filter.mp hy).1)
    have ha2 : 2 ≤ a := by
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr he
      have := hbounds x (mem_filter.mp hx).1
      have := (mem_filter.mp hx).2
      omega
    omega
  have hR : 3 * R.card ≤ 3 * k - b + 2 := by
    by_cases he : R = ∅
    · simp [he]
    have h := spaced_card_bound R (b + 1) (3 * k)
      (by intro x hx; have := (mem_filter.mp hx).2
          have := hbounds x (mem_filter.mp hx).1; omega)
      (by intro x hx y hy; exact hspace x (mem_filter.mp hx).1 y (mem_filter.mp hy).1)
    have hb' : b < 3 * k := by
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr he
      have := hbounds x (mem_filter.mp hx).1
      have := (mem_filter.mp hx).2
      omega
    omega
  have hpart := card_filter_add_card_filter_not (s := A) (p := fun x => x < a)
  change L.card + R.card = A.card at hpart
  change 3 * S.card + (b - a + 1) ≤ 3 * k + 4
  omega

/-- In a one-excess profile a concentrated gap has length at most `3e+7`,
and hence at most sixteen, uniformly in the grid size. -/
theorem one_excess_gap_length_le_sixteen {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hcard : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (a b : Nat) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3 * k)
    (hgap : ∀ u ∈ F, OnOpenSide s u → a ≤ sidePosition s u →
      sidePosition s u ≤ b → False) :
    b - a + 1 ≤ 16 ∧
      b - a + 1 + 6 * k ≤
        3 * boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) - 2 := by
  obtain ⟨a', d, e, m, hs, _, _, hb', hm, hme, _, _⟩ :=
    one_excess_missing_side_slack hk F hacyc hp hcard s hmissing
  have := missing_side_gap_length_budget (by omega) F hacyc s hmissing a b ha hab hb hgap
  omega

/-- Shared inward witnesses force the entire closed interval between their
boundary holes to be root-free, not just the selected empty blocks. -/
theorem shared_inward_carrier_root_free_interval {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (x y : GridVertex n n)
    (hx : OnOpenSide s x) (hy : OnOpenSide s y) (hxU : x ∉ F) (hyU : y ∉ F)
    (w z : (↑F : Set (GridVertex n n)))
    (hwb : ¬ IsGridBoundary w.val) (hzb : ¬ IsGridBoundary z.val)
    (hxw : (gridGraph n n).Adj x w.val) (hyz : (gridGraph n n).Adj y z.val)
    (he : ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk w =
      ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk z) :
    ∀ u ∈ F, OnOpenSide s u → sidePosition s x ≤ sidePosition s u →
      sidePosition s u ≤ sidePosition s y → False := by
  intro u hu hus hxu huy
  have hleft : sidePosition s x < sidePosition s u := by
    by_contra h
    have heq := sidePosition_injective hx hus (by omega)
    exact hxU (heq ▸ hu)
  have hright : sidePosition s u < sidePosition s y := by
    by_contra h
    have heq := sidePosition_injective hus hy (by omega)
    exact hyU (heq ▸ hu)
  exact inward_carriers_distinct_of_root_between F hacyc s x y hx hy hxU
    ⟨u, hu⟩ w z hus hleft hright hwb hzb hxw hyz he

/-- A carrier shared across side holes consumes root-deficit budget in
proportion to the full span, whether or not there are roots elsewhere. -/
theorem shared_inward_carrier_span_budget {k : Nat} (hk : 1 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (x y : GridVertex (3 * k + 2) (3 * k + 2))
    (hx : OnOpenSide s x) (hy : OnOpenSide s y) (hxU : x ∉ F) (hyU : y ∉ F)
    (hxy : sidePosition s x ≤ sidePosition s y)
    (w z : (↑F : Set (GridVertex (3 * k + 2) (3 * k + 2))))
    (hwb : ¬ IsGridBoundary w.val) (hzb : ¬ IsGridBoundary z.val)
    (hxw : (gridGraph (3 * k + 2) (3 * k + 2)).Adj x w.val)
    (hyz : (gridGraph (3 * k + 2) (3 * k + 2)).Adj y z.val)
    (he : ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk w =
      ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk z) :
    3 * (F.filter (OnOpenSide s)).card +
      (sidePosition s y - sidePosition s x + 1) ≤ 3 * k + 4 := by
  exact missing_side_gap_length_budget hk F hacyc s hmissing
    (sidePosition s x) (sidePosition s y) (sidePosition_bounds hx).1 hxy
    (by have := sidePosition_bounds hy; omega)
    (shared_inward_carrier_root_free_interval F hacyc s x y hx hy hxU hyU
      w z hwb hzb hxw hyz he)

/-- Conditional sharp exclusion: two holes seventeen or more positions in
inclusive span cannot reuse an inward carrier in a one-excess configuration
with at most three pure carriers. No root-separation hypothesis is imposed. -/
theorem card_le_target_of_long_shared_inward_carrier {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (x y : GridVertex (3 * k + 2) (3 * k + 2))
    (hx : OnOpenSide s x) (hy : OnOpenSide s y) (hxU : x ∉ F) (hyU : y ∉ F)
    (hlong : sidePosition s x + 16 ≤ sidePosition s y)
    (w z : (↑F : Set (GridVertex (3 * k + 2) (3 * k + 2))))
    (hwb : ¬ IsGridBoundary w.val) (hzb : ¬ IsGridBoundary z.val)
    (hxw : (gridGraph (3 * k + 2) (3 * k + 2)).Adj x w.val)
    (hyz : (gridGraph (3 * k + 2) (3 * k + 2)).Adj y z.val)
    (he : ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk w =
      ((gridGraph (3 * k + 2) (3 * k + 2)).induce (↑F : Set _)).connectedComponentMk z) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  by_contra h
  have hgap := shared_inward_carrier_root_free_interval F hacyc s x y hx hy hxU hyU
    w z hwb hzb hxw hyz he
  have hbound := one_excess_gap_length_le_sixteen hk F hacyc hp (by omega) s hmissing
    (sidePosition s x) (sidePosition s y) (sidePosition_bounds hx).1 (by omega)
    (by have := sidePosition_bounds hy; omega) hgap
  omega

/-- A long preserved interval removes at least half its length from the
capacity two rows away. Unlike interval-pair packing, the opposite preserved
set may be disconnected and may use arbitrarily many carriers. -/
theorem concentrated_interval_opposite_occupancy {m n : Nat}
    (F : Finset (GridVertex m n))
    (hacyc : (forcedEdgeGraph (gridGraph m n) (↑F : Set _)).IsAcyclic)
    (r t : Fin m) (hrows : r.val + 2 = t.val)
    (a b : Fin n)
    (hinterval : ∀ j ∈ Icc a b, (r, j) ∈ F) :
    ((Icc a b).filter (fun j => (t, j) ∈ F)).card ≤ (b.val - a.val) / 2 + 1 := by
  classical
  let A := (Icc a b).filter (fun j => (t, j) ∈ F)
  let f : A → Fin ((b.val - a.val) / 2 + 1) := fun j =>
    ⟨(j.val.val - a.val) / 2, by
      have h := mem_Icc.mp (mem_filter.mp j.property).1
      simp only [Fin.le_iff_val_le_val] at h
      omega⟩
  have hno (x y : A) (hxy : x.val.val + 1 = y.val.val) : False := by
    let row : Fin (m - 2) := ⟨r.val, by omega⟩
    let col : Fin (n - 1) := ⟨x.val.val, by omega⟩
    have hr : (⟨row.val, by omega⟩ : Fin m) = r := rfl
    have ht : (⟨row.val + 2, by omega⟩ : Fin m) = t := Fin.ext hrows
    have hx : (⟨col.val, by omega⟩ : Fin n) = x.val := rfl
    have hy : (⟨col.val + 1, by omega⟩ : Fin n) = y.val := Fin.ext hxy
    apply forced_rectangle_two_rows_false row col hacyc
    · simpa only [hr, hx, mem_coe] using hinterval x.val (mem_filter.mp x.property).1
    · simpa only [hr, hy, mem_coe] using hinterval y.val (mem_filter.mp y.property).1
    · simpa only [ht, hx, mem_coe] using (mem_filter.mp x.property).2
    · simpa only [ht, hy, mem_coe] using (mem_filter.mp y.property).2
  have hinj : Function.Injective f := by
    intro x y he
    have he' := congrArg Fin.val he
    have hx := mem_Icc.mp (mem_filter.mp x.property).1
    have hy := mem_Icc.mp (mem_filter.mp y.property).1
    simp only [Fin.le_iff_val_le_val] at hx hy
    dsimp [f] at he'
    apply Subtype.ext
    apply Fin.ext
    by_contra h
    have hcases : x.val.val + 1 = y.val.val ∨ y.val.val + 1 = x.val.val := by omega
    rcases hcases with hxy | hyx
    · exact hno x y hxy
    · exact hno y x hyx
  have h := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Fintype.card_fin] using h

/-- Actual row capacity loses `floor(L/2)` to a preserved interval of length
`L` two rows away. These holes are physical vertices, not extra component
charges, so this inequality must not be added blindly to the component ledger. -/
theorem concentrated_interval_row_capacity_loss {m n : Nat}
    (F : Finset (GridVertex m n))
    (hacyc : (forcedEdgeGraph (gridGraph m n) (↑F : Set _)).IsAcyclic)
    (r t : Fin m) (hrows : r.val + 2 = t.val)
    (a b : Fin n) (hab : a ≤ b)
    (hinterval : ∀ j ∈ Icc a b, (r, j) ∈ F) :
    (univ.filter (fun j : Fin n => (t, j) ∈ F)).card +
      (b.val - a.val + 1) / 2 ≤ n := by
  classical
  have hcap := concentrated_interval_opposite_occupancy F hacyc r t hrows a b hinterval
  have hpart := card_filter_add_card_filter_not (s := Icc a b) (p := fun j => (t, j) ∈ F)
  have hlen : (Icc a b).card = b.val - a.val + 1 := by
    rw [Fin.card_Icc]
    have := Fin.le_iff_val_le_val.mp hab
    omega
  rw [hlen] at hpart
  have hsub : (Icc a b).filter (fun j => ¬ (t, j) ∈ F) ⊆
      univ.filter (fun j : Fin n => ¬ (t, j) ∈ F) := by
    intro j hj
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
  have hle := card_le_card hsub
  have htotal := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (p := fun j => (t, j) ∈ F)
  simp only [card_univ, Fintype.card_fin] at htotal
  omega

end GridGraphs.CarrierLayers
