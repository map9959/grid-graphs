import GridGraphs.Accounting.CarrierLayers.RadialNearTightBoundary

/-!
# Excluding the remaining three-carrier two-excess profile

An empty triple on the missing side forces an inward preserved vertex by
ambient connectivity. Its carrier is distinct from every radial root carrier
and from every pure boundary carrier, exceeding the component budget.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Fewer than `k` roots leave an empty block among the `k` disjoint triples.
The middle vertex has no preserved boundary neighbor, in any orientation. -/
theorem missing_side_empty_triple_middle {k : Nat} (hk : 1 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2))) (s : Fin 4)
    (hq : (F.filter (OnOpenSide s)).card < k) :
    ∃ v, OnOpenSide s v ∧ v ∉ F ∧
      ∀ z, (gridGraph (3 * k + 2) (3 * k + 2)).Adj v z →
        IsGridBoundary z → z ∉ F := by
  classical
  let A := F.filter (OnOpenSide s)
  let I := A.image (fun v => (sidePosition s v - 1) / 3)
  have hI : I.card < k := (card_image_le).trans_lt hq
  have hex : ∃ i < k, i ∉ I := by
    by_contra h
    push Not at h
    have hsub : range k ⊆ I := fun i hi => h i (mem_range.mp hi)
    have hle := card_le_card hsub
    rw [card_range] at hle
    omega
  obtain ⟨i, hi, hiI⟩ := hex
  have hhole (z : GridVertex (3 * k + 2) (3 * k + 2))
      (hz : OnOpenSide s z) (hblock : (sidePosition s z - 1) / 3 = i) : z ∉ F := by
    intro hzF
    exact hiI (mem_image.mpr ⟨z, mem_filter.mpr ⟨hzF, hz⟩, hblock⟩)
  let a : Fin (3 * k + 2) := ⟨if s.val = 0 ∨ s.val = 2 then 0 else 3 * k + 1, by
    split <;> omega⟩
  let t : Fin (3 * k + 2) := ⟨3 * i + 2, by omega⟩
  let v : GridVertex (3 * k + 2) (3 * k + 2) :=
    if s.val < 2 then (a, t) else (t, a)
  have hvs : OnOpenSide s v := by
    dsimp [v, a, t, OnOpenSide, OnSide]
    split_ifs <;> simp <;> omega
  have hvpos : sidePosition s v = 3 * i + 2 := by
    dsimp [sidePosition, v, t]
    split_ifs <;> rfl
  refine ⟨v, hvs, hhole v hvs (by rw [hvpos]; omega), ?_⟩
  intro z hadj hzb
  have hzgeom : OnOpenSide s z ∧ (sidePosition s z - 1) / 3 = i := by
    have hcoord := hadj
    unfold IsGridBoundary at hzb
    fin_cases s <;>
      dsimp [v, a, t, gridGraph, adjacent, OnOpenSide, OnSide, sidePosition] at hcoord ⊢ <;>
      simp only [Fin.ext_iff, Fin.val_zero] at hcoord <;> omega
  exact hhole z hzgeom.1 hzgeom.2

/-- An inward preserved neighbor of a missing-side hole belongs to no carrier
rooted on that side: straightness would force the root to equal the hole. -/
theorem inward_hole_carrier_avoids_roots {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (v : GridVertex n n) (hvs : OnOpenSide s v) (hv : v ∉ F)
    (w : (↑F : Set (GridVertex n n))) (hwb : ¬ IsGridBoundary w.val)
    (hadj : (gridGraph n n).Adj v w.val) :
    ∀ u : (↑F : Set (GridVertex n n)), OnOpenSide s u.val →
      ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk u ≠
        ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk w := by
  intro u hus he
  have hsame := induced_forced_reachable_same_row_or_column hacyc
    (ConnectedComponent.exact he)
  have huv : u.val = v := by
    apply Prod.ext <;> apply Fin.ext
    all_goals
      simp only [Fin.ext_iff] at hsame
      simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
      unfold OnOpenSide OnSide at hvs hus
      unfold IsGridBoundary at hwb
      omega
  exact hv (huv ▸ u.property)

/-- An additional nonpure carrier avoiding every missing-side root increases
the root-plus-pure component bound by one. -/
theorem missing_side_roots_add_pure_add_one_le_components {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val)
    (D : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (hD : D ∉ pureBoundaryCarriers F)
    (havoid : ∀ u : (↑F : Set (GridVertex n n)), OnOpenSide s u.val →
      ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk u ≠ D) :
    (F.filter (OnOpenSide s)).card + (pureBoundaryCarriers F).card + 1 ≤
      Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let A := F.filter (OnOpenSide s)
  let P := pureBoundaryCarriers F
  let B := univ \ insert D P
  let root : A → (↑F : Set (GridVertex n n)) := fun u =>
    ⟨u.val, (mem_filter.mp u.property).1⟩
  have hmem (u : A) : root u ∈ (G.connectedComponentMk (root u)).supp := by
    simp [ConnectedComponent.mem_supp_iff]
  have hnonpure (u : A) : G.connectedComponentMk (root u) ∉ P := fun h =>
    hmissing _ h _ (hmem u) (mem_filter.mp u.property).2
  let f : A → B := fun u => ⟨G.connectedComponentMk (root u), by
    apply mem_sdiff.mpr
    refine ⟨mem_univ _, ?_⟩
    simp only [mem_insert, not_or]
    exact ⟨havoid (root u) (mem_filter.mp u.property).2, hnonpure u⟩⟩
  have hinj : Function.Injective f := by
    intro u v he
    have heq : G.connectedComponentMk (root u) = G.connectedComponentMk (root v) :=
      congrArg Subtype.val he
    let C := G.connectedComponentMk (root u)
    have hu : root u ∈ C.supp := hmem u
    have hv : root v ∈ C.supp := by
      change root v ∈ (G.connectedComponentMk (root u)).supp
      rw [heq]
      exact hmem v
    have hn : ¬ ∀ w ∈ C.supp, IsGridBoundary w.val := by
      simpa only [P, pureBoundaryCarriers, mem_filter, mem_univ, true_and] using hnonpure u
    push Not at hn
    obtain ⟨w, hw, hwb⟩ := hn
    have hus := (mem_filter.mp u.property).2
    have hvs := (mem_filter.mp v.property).2
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    all_goals
      rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
      · have hur := congrArg Fin.val (hr _ hu)
        have hvr := congrArg Fin.val (hr _ hv)
        have hwr := congrArg Fin.val (hr _ hw)
        dsimp [root] at hur hvr
        unfold OnOpenSide OnSide at hus hvs
        unfold IsGridBoundary at hwb
        omega
      · have huc := congrArg Fin.val (hc _ hu)
        have hvc := congrArg Fin.val (hc _ hv)
        have hwc := congrArg Fin.val (hc _ hw)
        dsimp [root] at huc hvc
        unfold OnOpenSide OnSide at hus hvs
        unfold IsGridBoundary at hwb
        omega
  have hle := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe] at hle
  have hpart := card_sdiff_add_card_inter (univ : Finset G.ConnectedComponent) (insert D P)
  rw [univ_inter, card_insert_of_notMem hD, card_univ] at hpart
  change A.card + P.card + 1 ≤ Fintype.card G.ConnectedComponent
  change A.card ≤ B.card at hle
  change B.card + (P.card + 1) = Fintype.card G.ConnectedComponent at hpart
  omega

/-- The remaining two-excess profile is impossible. The empty triple forces
one more nonpure carrier than the `r = k+2` ledger permits. -/
theorem two_excess_three_carrier_false {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hcard : 3 * k ^ 2 + 7 * k + 2 ≤ F.card) : False := by
  obtain ⟨_, hr, hc, _⟩ := residueTwo_two_excess_three_carrier_profile_unique hk F hacyc hp hcard
  obtain ⟨s, hs⟩ := exists_side_without_pure_carrier (by omega) F hacyc hp
  obtain ⟨hp3, hq, _, _⟩ := two_excess_missing_side_deficient_roots hk F hacyc hp hcard s hs
  obtain ⟨v, hvs, hv, hneighbors⟩ := missing_side_empty_triple_middle (by omega) F s (by omega)
  obtain ⟨w, hw, hwr, hadj⟩ := inward_preserved_of_boundary_neighbors_unpreserved
    (by omega) F hc s v hvs hv hneighbors
  have hwb : ¬ IsGridBoundary w := by
    unfold IsNextRing at hwr
    unfold IsGridBoundary
    omega
  let wF : (↑F : Set (GridVertex (3 * k + 2) (3 * k + 2))) := ⟨w, hw⟩
  let D := ((gridGraph (3 * k + 2) (3 * k + 2)).induce
    (↑F : Set _)).connectedComponentMk wF
  have hwD : wF ∈ D.supp := by simp [D, ConnectedComponent.mem_supp_iff]
  have hD : D ∉ pureBoundaryCarriers F := fun h => hwb ((mem_filter.mp h).2 wF hwD)
  have havoid := inward_hole_carrier_avoids_roots F hacyc s v hvs hv wF hwb hadj
  have hbound := missing_side_roots_add_pure_add_one_le_components F hacyc s hs D hD havoid
  rw [hq, hp3, hr] at hbound
  omega

end GridGraphs.CarrierLayers

namespace GridGraphs

open Finset SimpleGraph CarrierLayers

/-- In the at-most-three-pure-carriers branch, at most one vertex above
`T(k) = 3k^2+7k` is possible. No maximality or connectivity is assumed. -/
theorem residueTwo_card_le_target_add_one_of_pure_carriers_le_three {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3) :
    F.card ≤ 3 * k ^ 2 + 7 * k + 1 := by
  by_contra h
  exact two_excess_three_carrier_false hk F hacyc hp (by omega)

end GridGraphs
