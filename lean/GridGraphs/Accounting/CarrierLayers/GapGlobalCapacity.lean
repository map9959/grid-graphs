import GridGraphs.Accounting.CarrierLayers.ConcentratedGaps

/-!
# Global loss from next-ring carriers

Count actual components, not inward witnesses. A nonpure component contained
in the outer two layers has zero deep capacity, even if many hole middles reuse
it. Boundary endpoints are retained.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Nonpure induced carriers with no deep vertices. Boundary endpoints are
allowed, so horizontal inward carriers are counted even at side contacts. -/
noncomputable def nextRingCarriers {n : Nat} (F : Finset (GridVertex n n)) :
    Finset ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent := by
  classical
  exact univ.filter (fun C => C ∉ pureBoundaryCarriers F ∧
    ∀ v ∈ C.supp, IsGridBoundary v.val ∨ IsNextRing v.val)

/-- Deep capacity with all shallow nonpure carriers removed simultaneously.
The subtraction counts components once, not the number of inward witnesses. -/
theorem card_le_layers_without_nextRing_carriers {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    F.card ≤ (F.filter IsGridBoundary).card + (F.filter IsNextRing).card +
      (n - 4) * (Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent -
        (pureBoundaryCarriers F).card - (nextRingCarriers F).card) := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let P := pureBoundaryCarriers F
  let N := nextRingCarriers F
  let D := F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)
  let R := (univ : Finset G.ConnectedComponent) \ (P ∪ N)
  have hdisj : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro C hp hN
    exact (mem_filter.mp hN).2.1 hp
  have hRcard : R.card = Fintype.card G.ConnectedComponent - P.card - N.card := by
    simp only [R, card_sdiff_of_subset (subset_univ _), card_univ,
      card_union_of_disjoint hdisj, Nat.sub_sub]
  let comp : D → G.ConnectedComponent := fun v =>
    G.connectedComponentMk ⟨v.val, (mem_filter.mp v.property).1⟩
  have hmem (v : D) : comp v ∈ R := by
    have hs : (⟨v.val, (mem_filter.mp v.property).1⟩ : (↑F : Set _)) ∈
        (comp v).supp := by simp [comp, ConnectedComponent.mem_supp_iff]
    have hd := (mem_filter.mp v.property).2
    simp only [R, mem_sdiff, mem_univ, true_and, mem_union, not_or]
    exact ⟨fun h => hd.1 ((mem_filter.mp h).2 _ hs),
      fun h => ((mem_filter.mp h).2.2 _ hs).elim hd.1 hd.2⟩
  have hcap (C : G.ConnectedComponent) :
      ((univ : Finset D).filter (fun v => comp v = C)).card ≤ n - 4 := by
    let A := (univ : Finset D).filter (fun v => comp v = C)
    have hs (v : A) : (⟨v.val.val, (mem_filter.mp v.val.property).1⟩ :
        (↑F : Set _)) ∈ C.supp := by
      rw [← (mem_filter.mp v.property).2]
      simp [comp, ConnectedComponent.mem_supp_iff]
    have hbox (v : A) : 2 ≤ v.val.val.1.val ∧ v.val.val.1.val < n - 2 ∧
        2 ≤ v.val.val.2.val ∧ v.val.val.2.val < n - 2 := by
      have hd := (mem_filter.mp v.val.property).2
      dsimp [IsGridBoundary, IsNextRing] at hd
      omega
    rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
    · let f : A → Fin (n - 4) := fun v => ⟨v.val.val.2.val - 2, by
        have := hbox v; omega⟩
      have hi : Function.Injective f := by
        intro v w he
        have he' := congrArg Fin.val he
        have hv := hbox v
        have hw := hbox w
        apply Subtype.ext
        apply Subtype.ext
        refine Prod.ext ((hr _ (hs v)).trans (hr _ (hs w)).symm) (Fin.ext ?_)
        dsimp [f] at he'
        omega
      simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hi
    · let f : A → Fin (n - 4) := fun v => ⟨v.val.val.1.val - 2, by
        have := hbox v; omega⟩
      have hi : Function.Injective f := by
        intro v w he
        have he' := congrArg Fin.val he
        have hv := hbox v
        have hw := hbox w
        apply Subtype.ext
        apply Subtype.ext
        refine Prod.ext (Fin.ext ?_) ((hc _ (hs v)).trans (hc _ (hs w)).symm)
        dsimp [f] at he'
        omega
      simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hi
  have hcover : R.biUnion (fun C => (univ : Finset D).filter (fun v => comp v = C)) =
      univ := by
    ext v
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, iff_true]
    exact ⟨comp v, hmem v, rfl⟩
  have hdeep : D.card ≤ (n - 4) * R.card := by
    calc
      D.card = (univ : Finset D).card := by simp
      _ = (R.biUnion (fun C => (univ : Finset D).filter (fun v => comp v = C))).card :=
        congrArg Finset.card hcover.symm
      _ ≤ ∑ C ∈ R, ((univ : Finset D).filter (fun v => comp v = C)).card := card_biUnion_le
      _ ≤ ∑ _C ∈ R, (n - 4) := sum_le_sum (fun C _ => hcap C)
      _ = _ := by simp [Nat.mul_comm]
  have houter : F ⊆ (F.filter IsGridBoundary) ∪ (F.filter IsNextRing) ∪ D := by
    intro v hv
    simp only [mem_union, mem_filter, D]
    tauto
  have htotal := (card_le_card houter).trans
    ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  rw [hRcard] at hdeep
  exact htotal.trans (Nat.add_le_add_left hdeep _)

/-- The boundary and next ring together fit in the perimeter budget. Removing
shallow nonpure components therefore saves `n-4` per actual component globally. -/
theorem card_le_perimeter_add_remaining_deep_capacity {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    F.card ≤ 4 * n - 4 + (n - 4) *
      (Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent -
        (pureBoundaryCarriers F).card - (nextRingCarriers F).card) := by
  classical
  have h := card_le_layers_without_nextRing_carriers (by omega) F hacyc
  have hi := forced_nextRing_card_le_compl_boundary_card (by omega) F hacyc
  have hb : (F.filter IsGridBoundary).card +
      ((univ \ F).filter IsGridBoundary).card = 4 * n - 4 := by
    have he : (F.filter IsGridBoundary) ∪ ((univ \ F).filter IsGridBoundary) =
        univ.filter IsGridBoundary := by
      ext v
      by_cases hv : v ∈ F <;> simp [hv]
    have hd : Disjoint (F.filter IsGridBoundary) ((univ \ F).filter IsGridBoundary) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact (mem_sdiff.mp (mem_filter.mp hw).1).2 (mem_filter.mp hv).1
    rw [← card_union_of_disjoint hd, he]
    simpa using BoundaryFiveConstruction.boundary_card hn
  omega

/-- At three pure carriers, a one-excess profile can afford at most `a`
nonpure carriers without deep vertices, where `r=k+2+a`. Unlike the elementary
budget this detects a loss even when boundary and next-ring occupancy are free. -/
theorem one_excess_shallow_carriers_le_induced_slack {k a : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card = 3)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hr : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 2 + a) :
    (nextRingCarriers F).card ≤ a := by
  have h := card_le_perimeter_add_remaining_deep_capacity (by omega) F hacyc
  rw [hp, hr] at h
  by_contra hn
  have hsub : k + 2 + a - 3 - (nextRingCarriers F).card ≤ k - 2 := by omega
  have hm := Nat.mul_le_mul_left (3 * k + 2 - 4) hsub
  have hk2 : k - 2 + 2 = k := by omega
  have hn2 : 3 * k + 2 - 4 = 3 * k - 2 := by omega
  have hn3 : 3 * k - 2 + 2 = 3 * k := by omega
  have hper : 4 * (3 * k + 2) - 4 = 12 * k + 4 := by omega
  rw [hper, hn2] at h
  rw [hn2] at hm
  nlinarith

/-- Two distinct vertices in one next-ring row force their entire actual
carrier to be shallow. Thus arbitrary reuse pays one full deep-carrier loss. -/
theorem horizontal_inward_carrier_mem_nextRingCarriers {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (w z : (↑F : Set (GridVertex n n))) (hw : w ∈ C.supp) (hz : z ∈ C.supp)
    (hne : w.val.2 ≠ z.val.2)
    (hring : w.val.1.val = 1 ∨ w.val.1.val = n - 2)
    (hwb : ¬ IsGridBoundary w.val) : C ∈ nextRingCarriers F := by
  classical
  have hline : ∀ v ∈ C.supp, v.val.1 = w.val.1 := by
    rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
    · intro v hv
      exact (hr v hv).trans (hr w hw).symm
    · exact (hne ((hc w hw).trans (hc z hz).symm)).elim
  have hnonpure : C ∉ pureBoundaryCarriers F := fun h =>
    hwb ((mem_filter.mp h).2 w hw)
  apply mem_filter.mpr
  refine ⟨mem_univ _, hnonpure, ?_⟩
  intro v hv
  have he := congrArg Fin.val (hline v hv)
  by_cases hb : IsGridBoundary v.val
  · exact Or.inl hb
  · right
    dsimp [IsGridBoundary] at hb
    dsimp [IsNextRing]
    omega

end GridGraphs.CarrierLayers
