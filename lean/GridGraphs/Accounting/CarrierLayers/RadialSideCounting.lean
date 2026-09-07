import GridGraphs.Accounting.CarrierLayers.RadialPacking
import GridGraphs.Accounting.BoundarySix.Witnesses

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

theorem sidePosition_bounds {n : Nat} {s : Fin 4} {v : GridVertex n n}
    (h : OnOpenSide s v) : 1 ≤ sidePosition s v ∧ sidePosition s v + 1 < n := by
  unfold OnOpenSide OnSide at h
  unfold sidePosition
  split <;> omega

theorem sidePosition_injective {n : Nat} {s : Fin 4} {u v : GridVertex n n}
    (hu : OnOpenSide s u) (hv : OnOpenSide s v)
    (he : sidePosition s u = sidePosition s v) : u = v := by
  unfold OnOpenSide OnSide at hu hv
  unfold sidePosition at he
  split at he <;> apply Prod.ext <;> apply Fin.ext <;> omega

/-- An open side has exactly `n - 2` vertices. -/
theorem openSide_card {n : Nat} (hn : 2 ≤ n) (s : Fin 4) :
    (univ.filter (OnOpenSide (n := n) s)).card = n - 2 := by
  classical
  let S := univ.filter (OnOpenSide (n := n) s)
  let f : S → Fin (n - 2) := fun v =>
    ⟨sidePosition s v.val - 1, by
      have h := sidePosition_bounds (mem_filter.mp v.property).2
      omega⟩
  have hinj : Function.Injective f := by
    intro u v he
    have h := congrArg Fin.val he
    have hu := sidePosition_bounds (mem_filter.mp u.property).2
    have hv := sidePosition_bounds (mem_filter.mp v.property).2
    apply Subtype.ext
    apply sidePosition_injective (mem_filter.mp u.property).2 (mem_filter.mp v.property).2
    dsimp [f] at h
    omega
  have hsurj : Function.Surjective f := by
    intro i
    let a : Fin n := ⟨if s.val = 0 ∨ s.val = 2 then 0 else n - 1, by
      split <;> omega⟩
    let t : Fin n := ⟨i.val + 1, by omega⟩
    let v : GridVertex n n := if s.val < 2 then (a, t) else (t, a)
    have hv : OnOpenSide s v := by
      dsimp [v, a, t, OnOpenSide, OnSide]
      split_ifs <;> simp <;> omega
    refine ⟨⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩⟩, Fin.ext ?_⟩
    dsimp [f, sidePosition, v, t]
    split_ifs <;> simp
  have h := Fintype.card_of_bijective ⟨hinj, hsurj⟩
  simpa only [Fintype.card_coe, Fintype.card_fin, S] using h

/-- Packing into blocks of three bounds occupancy on a side with no pure carrier. -/
theorem missing_side_preserved_card_le {k : Nat} (hk : 1 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) : (F.filter (OnOpenSide s)).card ≤ k := by
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
  have hspace (u v : S) (hlt : sidePosition s u.val < sidePosition s v.val) :
      sidePosition s u.val + 3 ≤ sidePosition s v.val := by
    obtain ⟨w, hw, hwr, huw⟩ := hneighbor u
    obtain ⟨z, hz, hzr, hvz⟩ := hneighbor v
    exact radial_pair_spacing (by omega) F hacyc s
      (mem_filter.mp u.property).1 (mem_filter.mp v.property).1 hw hz
      (mem_filter.mp u.property).2 (mem_filter.mp v.property).2 hwr hzr huw hvz hlt
  let f : S → Fin k := fun u => ⟨(sidePosition s u.val - 1) / 3, by
    have h := sidePosition_bounds (mem_filter.mp u.property).2
    omega⟩
  have hinj : Function.Injective f := by
    intro u v he
    have he' := congrArg Fin.val he
    dsimp [f] at he'
    have hu := sidePosition_bounds (mem_filter.mp u.property).2
    have hv := sidePosition_bounds (mem_filter.mp v.property).2
    apply Subtype.ext
    apply sidePosition_injective (mem_filter.mp u.property).2 (mem_filter.mp v.property).2
    rcases lt_trichotomy (sidePosition s u.val) (sidePosition s v.val) with h | h | h
    · have h' := hspace u v h
      omega
    · exact h
    · have h' := hspace v u h
      omega
  simpa only [Fintype.card_coe, Fintype.card_fin, S] using
    Fintype.card_le_of_injective f hinj

/-- At most two of the near-corner witnesses lie on a given open side. -/
theorem near_openSide_card_le_two {n : Nat} (hn : 5 ≤ n)
    (Q : Finset (GridVertex n n)) (hQ : ∀ v ∈ Q, BoundarySix.Near v) (s : Fin 4) :
    (Q.filter (OnOpenSide s)).card ≤ 2 := by
  classical
  let S := Q.filter (OnOpenSide s)
  have hpos (v : S) : sidePosition s v.val = 1 ∨ sidePosition s v.val + 2 = n := by
    have hnear := hQ v.val (mem_filter.mp v.property).1
    have hs := (mem_filter.mp v.property).2
    unfold BoundarySix.Near at hnear
    unfold OnOpenSide OnSide at hs
    unfold sidePosition
    split <;> omega
  let f : S → Fin 2 := fun v => if sidePosition s v.val = 1 then 0 else 1
  have hinj : Function.Injective f := by
    intro u v he
    have he' := congrArg Fin.val he
    have hu := hpos u
    have hv := hpos v
    apply Subtype.ext
    apply sidePosition_injective (mem_filter.mp u.property).2 (mem_filter.mp v.property).2
    dsimp [f] at he'
    split_ifs at he' <;> simp only [Fin.val_zero, Fin.val_one] at he' <;> omega
  simpa only [Fintype.card_coe, Fintype.card_fin, S] using
    Fintype.card_le_of_injective f hinj

end GridGraphs.CarrierLayers
