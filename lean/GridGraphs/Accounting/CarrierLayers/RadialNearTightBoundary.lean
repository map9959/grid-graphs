import GridGraphs.Accounting.CarrierLayers.RadialTightExclusion

/-!
# The one-unit-slack radial boundary budget

Off-side deficiency includes corners with weight two. Carrier nonreuse
eliminates the full-root alternative in the surviving two-excess profile;
the deficient-root alternative is not excluded here.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Exact root/off-side-budget alternatives, and preservation of every corner.
The off-side filter may include interior vertices, whose deficiency is zero. -/
theorem near_tight_missing_side_budget {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 3)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    ((F.filter (OnOpenSide s)).card = k ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
        ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 3 ∨
     (F.filter (OnOpenSide s)).card = k - 1 ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
        ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) = 2) ∧
    (∀ v, BoundarySix.Corner v → v ∈ F) := by
  classical
  let U := univ \ F
  let D := U.filter (fun v => ¬ OnOpenSide s v)
  let S := univ.filter (OnOpenSide (n := 3 * k + 2) s)
  let d := gridBoundaryDeficiency (3 * k + 2) (3 * k + 2)
  have hpacking := missing_side_preserved_card_le (by omega) F hacyc s hmissing
  have hScard : S.card = 3 * k := by
    simpa only [Nat.add_sub_cancel] using openSide_card (by omega : 2 ≤ 3 * k + 2) s
  have hSF : S ∩ F = F.filter (OnOpenSide s) := by
    ext v
    simp only [S, mem_inter, mem_filter, mem_univ, true_and]
    exact and_comm
  have hSU : S \ F = U.filter (OnOpenSide s) := by
    ext v
    simp [S, U, and_comm]
  have hpart := card_sdiff_add_card_inter S F
  rw [hSF, hSU, hScard] at hpart
  have hside : ∑ v ∈ U.filter (OnOpenSide s), d v = (U.filter (OnOpenSide s)).card := by
    calc
      _ = ∑ _v ∈ U.filter (OnOpenSide s), 1 := by
        apply sum_congr rfl
        intro v hv
        have hs := (mem_filter.mp hv).2
        dsimp [d]
        rw [gridBoundaryDeficiency_eq_four_side_indicators (by omega) (by omega)]
        unfold OnOpenSide OnSide at hs
        split_ifs <;> omega
      _ = _ := by simp
  have hsum : (U.filter (OnOpenSide s)).card + (∑ v ∈ D, d v) = 2 * k + 3 := by
    rw [← hside]
    exact (sum_filter_add_sum_filter_not U (OnOpenSide s) d).trans hb
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := BoundarySix.corner_witnesses (by omega) F hacyc
  let R := Q.filter (fun v => ¬ OnOpenSide s v)
  have hnear := near_openSide_card_le_two (by omega) Q hQnear s
  have hQpart := card_filter_add_card_filter_not (s := Q) (OnOpenSide s)
  have hRcard : 2 ≤ R.card := by dsimp [R]; omega
  have hRD : R ⊆ D := by
    intro v hv
    exact mem_filter.mpr ⟨hQU (mem_filter.mp hv).1, (mem_filter.mp hv).2⟩
  have hRone : ∀ v ∈ R, 1 ≤ d v := by
    intro v hv
    apply one_le_gridBoundaryDeficiency_of_boundary (by omega) (by omega)
    have hn := hQnear v (mem_filter.mp hv).1
    unfold BoundarySix.Near IsGridBoundary at *
    omega
  have hRsum : R.card ≤ ∑ v ∈ R, d v := by
    calc
      _ = ∑ _v ∈ R, 1 := by simp
      _ ≤ _ := sum_le_sum hRone
  have hRle : (∑ v ∈ R, d v) ≤ ∑ v ∈ D, d v :=
    sum_le_sum_of_subset_of_nonneg hRD (by simp)
  have hDupper : (∑ v ∈ D, d v) ≤ 3 := by omega
  refine ⟨?_, ?_⟩
  · change ((_ = k ∧ (∑ v ∈ D, d v) = 3) ∨
      (_ = k - 1 ∧ (∑ v ∈ D, d v) = 2))
    omega
  · intro v hc
    by_contra hu
    have hvD : v ∈ D := by
      refine mem_filter.mpr ⟨by simp [U, hu], ?_⟩
      unfold BoundarySix.Corner OnOpenSide OnSide at *
      omega
    have hvR : v ∉ R := by
      intro hv
      have hn := hQnear v (mem_filter.mp hv).1
      unfold BoundarySix.Corner BoundarySix.Near at *
      omega
    have hdv : d v = 2 := by
      dsimp [d]
      rw [gridBoundaryDeficiency_eq_four_side_indicators (by omega) (by omega)]
      unfold BoundarySix.Corner at hc
      split_ifs <;> omega
    have hins : insert v R ⊆ D := insert_subset hvD hRD
    have hle := sum_le_sum_of_subset_of_nonneg hins (f := d) (by simp)
    rw [sum_insert hvR, hdv] at hle
    omega

/-- Because corners are preserved, the off-side weighted budget is exactly
the number of off-side boundary holes, not merely an upper bound for it. -/
theorem near_tight_missing_side_hole_count {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 3)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    ((F.filter (OnOpenSide s)).card = k ∧
      ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card = 3) ∨
    ((F.filter (OnOpenSide s)).card = k - 1 ∧
      ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card = 2) := by
  classical
  obtain ⟨hcases, hcorners⟩ := near_tight_missing_side_budget hk F hacyc hb s hmissing
  have he : boundaryDeficiencySum (3 * k + 2) (3 * k + 2)
      ((univ \ F).filter (fun v => ¬ OnOpenSide s v)) =
      ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card := by
    unfold boundaryDeficiencySum
    have hweight : ∀ v ∈ (univ \ F).filter (fun v => ¬ OnOpenSide s v),
        gridBoundaryDeficiency (3 * k + 2) (3 * k + 2) v =
          if IsGridBoundary v then 1 else 0 := by
      intro v hv
      have hnc : ¬ BoundarySix.Corner v := fun h =>
        (mem_sdiff.mp (mem_filter.mp hv).1).2 (hcorners v h)
      rw [gridBoundaryDeficiency_eq_four_side_indicators (by omega) (by omega)]
      unfold BoundarySix.Corner at hnc
      unfold IsGridBoundary
      split_ifs <;> omega
    rw [sum_congr rfl hweight]
    simp only [← sum_filter, sum_const, smul_eq_mul, mul_one, filter_filter]
    congr 1
    ext v
    simp only [mem_filter]
    tauto
  rw [he] at hcases
  exact hcases

/-- At most one off-side hole is away from the near-corner positions.
In the deficient-root branch (`q = k-1`), every off-side hole is near a corner. -/
theorem near_tight_offside_nonNear_holes {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 3)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v ∧
      ¬ BoundarySix.Near v)).card ≤ 1 ∧
    ((F.filter (OnOpenSide s)).card = k - 1 →
      ∀ v, IsGridBoundary v → ¬ OnOpenSide s v → v ∉ F → BoundarySix.Near v) := by
  classical
  let O := (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)
  let N := (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v ∧
    ¬ BoundarySix.Near v)
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := BoundarySix.corner_witnesses (by omega) F hacyc
  let R := Q.filter (fun v => ¬ OnOpenSide s v)
  have hnear := near_openSide_card_le_two (by omega) Q hQnear s
  have hpart := card_filter_add_card_filter_not (s := Q) (OnOpenSide s)
  have hRcard : 2 ≤ R.card := by dsimp [R]; omega
  have hdisj : Disjoint N R := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_filter.mp hv).2.2.2 (hQnear v (mem_filter.mp hw).1)
  have hsub : N ∪ R ⊆ O := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact mem_filter.mpr ⟨(mem_filter.mp hv).1,
        (mem_filter.mp hv).2.1, (mem_filter.mp hv).2.2.1⟩
    · refine mem_filter.mpr ⟨hQU (mem_filter.mp hv).1, ?_, (mem_filter.mp hv).2⟩
      have hn := hQnear v (mem_filter.mp hv).1
      unfold BoundarySix.Near IsGridBoundary at *
      omega
  have hle := card_le_card hsub
  rw [card_union_of_disjoint hdisj] at hle
  have hcases := near_tight_missing_side_hole_count hk F hacyc hb s hmissing
  change (_ = k ∧ O.card = 3) ∨ (_ = k - 1 ∧ O.card = 2) at hcases
  refine ⟨by change N.card ≤ 1; omega, ?_⟩
  intro hq v hv hs hu
  have hNzero : N.card = 0 := by omega
  by_contra hn
  have hm : v ∈ N := mem_filter.mpr ⟨by simp [hu], hv, hs, hn⟩
  rw [card_eq_zero.mp hNzero] at hm
  simp at hm

/-- One ambient component forbids an unpreserved vertex with no preserved
grid neighbor. This counts ambient isolates, not just nontrivial components. -/
theorem preserved_neighbor_of_one_forced_component {n : Nat} (hn : 2 ≤ n)
    (F : Finset (GridVertex n n))
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (v : GridVertex n n) (hu : v ∉ F) :
    ∃ w ∈ F, (gridGraph n n).Adj v w := by
  classical
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have : Subsingleton H.ConnectedComponent := (Fintype.card_le_one_iff_subsingleton).mp (by
    change Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent ≤ 1
    omega)
  have hconn : H.Preconnected := fun a b => ConnectedComponent.exact (Subsingleton.elim _ _)
  obtain ⟨w, hw⟩ := hconn.exists_adj_of_nontrivial v
  exact ⟨w, hw.2.resolve_left hu, hw.1⟩

/-- If an open-side hole has no preserved boundary neighbor, connectivity
forces a preserved inward neighbor. In particular this applies to the middle
of any three consecutive boundary holes, without acyclicity assumptions. -/
theorem inward_preserved_of_boundary_neighbors_unpreserved {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (s : Fin 4) (v : GridVertex n n) (hs : OnOpenSide s v) (hu : v ∉ F)
    (hneighbors : ∀ w, (gridGraph n n).Adj v w → IsGridBoundary w → w ∉ F) :
    ∃ w ∈ F, IsNextRing w ∧ (gridGraph n n).Adj v w := by
  obtain ⟨w, hw, hadj⟩ := preserved_neighbor_of_one_forced_component (by omega) F hc v hu
  refine ⟨w, hw, ?_, hadj⟩
  have hwb : ¬ IsGridBoundary w := fun h => hneighbors w hadj h hw
  unfold OnOpenSide OnSide at hs
  simp only [gridGraph, adjacent] at hadj
  unfold IsGridBoundary at hwb
  unfold IsNextRing
  omega

/-- A coordinate version of the no-isolate constraint on the top side.
Three consecutive holes force the vertex immediately below the middle one. -/
theorem top_three_holes_force_inward {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (j : Nat) (hj : j + 2 < n)
    (hleft : (⟨0, by omega⟩, ⟨j, by omega⟩) ∉ F)
    (hmid : (⟨0, by omega⟩, ⟨j + 1, by omega⟩) ∉ F)
    (hright : (⟨0, by omega⟩, ⟨j + 2, hj⟩) ∉ F) :
    (⟨1, by omega⟩, ⟨j + 1, by omega⟩) ∈ F := by
  obtain ⟨w, hw, hadj⟩ := preserved_neighbor_of_one_forced_component (by omega) F hc
    (⟨0, by omega⟩, ⟨j + 1, by omega⟩) hmid
  have hcoord := hadj
  simp only [gridGraph, adjacent, Fin.ext_iff] at hcoord
  dsimp at hcoord
  have hcases : w = (⟨0, by omega⟩, ⟨j, by omega⟩) ∨
      w = (⟨0, by omega⟩, ⟨j + 2, hj⟩) ∨
      w = (⟨1, by omega⟩, ⟨j + 1, by omega⟩) := by
    simp only [Prod.ext_iff, Fin.ext_iff]
    omega
  rcases hcases with h | h | h
  · exact (hleft (h ▸ hw)).elim
  · exact (hright (h ▸ hw)).elim
  · exact h ▸ hw

/-- Distinct roots on a missing side belong to distinct nonpure carriers.
This is an actual component injection, not a sum of pairwise capacities. -/
theorem missing_side_roots_add_pure_le_components {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    (F.filter (OnOpenSide s)).card + (pureBoundaryCarriers F).card ≤
      Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let A := F.filter (OnOpenSide s)
  let P := pureBoundaryCarriers F
  let B := univ \ P
  let root : A → (↑F : Set (GridVertex n n)) := fun u =>
    ⟨u.val, (mem_filter.mp u.property).1⟩
  have hmem (u : A) : root u ∈ (G.connectedComponentMk (root u)).supp := by
    simp [ConnectedComponent.mem_supp_iff]
  have hnonpure (u : A) : G.connectedComponentMk (root u) ∉ P := fun h =>
    hmissing _ h _ (hmem u) (mem_filter.mp u.property).2
  let f : A → B := fun u => ⟨G.connectedComponentMk (root u), by simp [B, hnonpure u]⟩
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
  have hpart := card_sdiff_add_card_inter (univ : Finset G.ConnectedComponent) P
  simp only [univ_inter, card_univ] at hpart
  change A.card + P.card ≤ Fintype.card G.ConnectedComponent
  change A.card ≤ B.card at hle
  change B.card + P.card = Fintype.card G.ConnectedComponent at hpart
  omega

/-- The surviving two-excess branch has a missing side with the exact hole
alternatives above, all corners preserved, and every hole dominated by `F`.
This is a necessary-condition package, not a contradiction. -/
theorem two_excess_near_tight_geometry {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hcard : 3 * k ^ 2 + 7 * k + 2 ≤ F.card) :
    (∀ v, BoundarySix.Corner v → v ∈ F) ∧
    (∀ v, v ∉ F → ∃ w ∈ F, (gridGraph (3 * k + 2) (3 * k + 2)).Adj v w) ∧
    ∃ s : Fin 4,
      (∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val) ∧
      (((F.filter (OnOpenSide s)).card = k ∧
        ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card = 3) ∨
       ((F.filter (OnOpenSide s)).card = k - 1 ∧
        ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card = 2)) := by
  obtain ⟨_, _, hc, hb⟩ := residueTwo_two_excess_three_carrier_profile_unique hk F hacyc hp hcard
  obtain ⟨s, hs⟩ := exists_side_without_pure_carrier (by omega) F hacyc hp
  exact ⟨(near_tight_missing_side_budget hk F hacyc hb s hs).2,
    preserved_neighbor_of_one_forced_component (by omega) F hc,
    s, hs, near_tight_missing_side_hole_count hk F hacyc hb s hs⟩

/-- Carrier nonreuse eliminates the `q = k` alternative in the two-excess
profile. Every missing side has `k-1` roots and precisely two off-side holes. -/
theorem two_excess_missing_side_deficient_roots {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hcard : 3 * k ^ 2 + 7 * k + 2 ≤ F.card)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    (pureBoundaryCarriers F).card = 3 ∧
    (F.filter (OnOpenSide s)).card = k - 1 ∧
    ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card = 2 ∧
    (∀ v, IsGridBoundary v → ¬ OnOpenSide s v → v ∉ F → BoundarySix.Near v) := by
  obtain ⟨_, hr, _, hb⟩ := residueTwo_two_excess_three_carrier_profile_unique hk F hacyc hp hcard
  have hperim := perimeter_le_pureBoundaryCarriers_add_twice_boundaryDeficiency
    (by omega) F hacyc
  rw [hb] at hperim
  have hp3 : (pureBoundaryCarriers F).card = 3 := by
    by_contra hne
    have hsmall : (pureBoundaryCarriers F).card ≤ 2 := by omega
    have hmul := Nat.mul_le_mul_left (3 * k + 2) hsmall
    omega
  have hnonreuse := missing_side_roots_add_pure_le_components F hacyc s hmissing
  rw [hr, hp3] at hnonreuse
  have hcases := near_tight_missing_side_hole_count hk F hacyc hb s hmissing
  have hq : (F.filter (OnOpenSide s)).card = k - 1 := by omega
  exact ⟨hp3, hq, by omega,
    (near_tight_offside_nonNear_holes hk F hacyc hb s hmissing).2 hq⟩

end GridGraphs.CarrierLayers
