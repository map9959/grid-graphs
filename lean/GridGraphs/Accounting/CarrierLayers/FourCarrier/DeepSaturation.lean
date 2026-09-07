import GridGraphs.Accounting.CarrierLayers.FourCarrier.ImageBudget

/-! # Zero deep deficit saturates each actual deep carrier

The componentwise caps are summed over the actual complement of pure and
shallow carriers. Equality in that sum forces every remaining cap to be full.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

noncomputable def deepCarrierPart {n : Nat} (F : Finset (GridVertex n n))
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent) :
    Finset (↑F : Set (GridVertex n n)) :=
  C.supp.toFinset.filter (fun v => ¬ IsGridBoundary v.val ∧ ¬ IsNextRing v.val)

theorem deep_carrier_part_card_le {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent) :
    (deepCarrierPart F C).card ≤ n - 4 := by
  classical
  let A := deepCarrierPart F C
  have hs (v : A) : v.val ∈ C.supp := Set.mem_toFinset.mp (mem_filter.mp v.property).1
  have hbox (v : A) : 2 ≤ v.val.val.1.val ∧ v.val.val.1.val < n - 2 ∧
      2 ≤ v.val.val.2.val ∧ v.val.val.2.val < n - 2 := by
    have hd := (mem_filter.mp v.property).2
    unfold IsGridBoundary IsNextRing at hd
    omega
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · let f : A → Fin (n - 4) := fun v => ⟨v.val.val.2.val - 2, by have := hbox v; omega⟩
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
  · let f : A → Fin (n - 4) := fun v => ⟨v.val.val.1.val - 2, by have := hbox v; omega⟩
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

/-- If total deep capacity is attained, every nonpure, nonshallow carrier
attains its own `n-4` cap. -/
theorem deep_carrier_full_of_total_equality {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (heq : (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card =
      (n - 4) * (Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent -
        (pureBoundaryCarriers F).card - (nextRingCarriers F).card))
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (hp : C ∉ pureBoundaryCarriers F) (hs : C ∉ nextRingCarriers F) :
    (deepCarrierPart F C).card = n - 4 := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let P := pureBoundaryCarriers F
  let N := nextRingCarriers F
  let R := (univ : Finset G.ConnectedComponent) \ (P ∪ N)
  let A := (univ : Finset (↑F : Set (GridVertex n n))).filter
    (fun v => ¬ IsGridBoundary v.val ∧ ¬ IsNextRing v.val)
  have hPN : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro D hp hs
    exact (mem_filter.mp hs).2.1 hp
  have hRcard : R.card = Fintype.card G.ConnectedComponent - P.card - N.card := by
    simp only [R, card_sdiff_of_subset (subset_univ _), card_univ,
      card_union_of_disjoint hPN, Nat.sub_sub]
  have hcover : R.biUnion (deepCarrierPart F) = A := by
    ext v
    simp only [mem_biUnion, deepCarrierPart, mem_filter, Set.mem_toFinset, A, mem_univ, true_and]
    constructor
    · rintro ⟨D, _, _, hd⟩
      exact hd
    · intro hd
      let D := G.connectedComponentMk v
      have hv : v ∈ D.supp := by simp [D, ConnectedComponent.mem_supp_iff]
      refine ⟨D, mem_sdiff.mpr ⟨mem_univ _, ?_⟩, hv, hd⟩
      simp only [mem_union, not_or]
      exact ⟨fun h => hd.1 ((mem_filter.mp h).2 v hv),
        fun h => ((mem_filter.mp h).2.2 v hv).elim hd.1 hd.2⟩
  have hAcard : A.card = (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card := by
    apply card_bij (fun v _ => v.val)
    · intro v hv
      exact mem_filter.mpr ⟨v.property, (mem_filter.mp hv).2⟩
    · intro v _ w _ h
      exact Subtype.ext h
    · intro v hv
      exact ⟨⟨v, (mem_filter.mp hv).1⟩, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩, rfl⟩
  have hsum : A.card ≤ ∑ D ∈ R, (deepCarrierPart F D).card := by
    rw [← hcover]
    exact card_biUnion_le
  have hcap := deep_carrier_part_card_le hn F hacyc C
  by_contra h
  have hCR : C ∈ R := by simp [R, P, N, hp, hs]
  have hlt := sum_lt_sum (fun D (_ : D ∈ R) => deep_carrier_part_card_le hn F hacyc D)
    ⟨C, hCR, by omega⟩
  have hconst : (∑ _D ∈ R, (n - 4)) = (n - 4) * R.card := by simp [Nat.mul_comm]
  rw [hconst, hRcard] at hlt
  rw [hAcard, heq] at hsum
  change (n - 4) * (Fintype.card G.ConnectedComponent - P.card - N.card) ≤ _ at hsum
  exact (not_lt_of_ge hsum) hlt

private theorem full_image {A : Type*} [Fintype A] {m : Nat}
    (f : A → Fin m) (hi : Function.Injective f) (hc : Fintype.card A = m) :
    Function.Surjective f := by
  classical
  have he : (univ.image f) = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    rw [card_image_of_injective _ hi]
    simp [hc]
  intro t
  have hm : t ∈ univ.image f := by rw [he]; exact mem_univ _
  obtain ⟨v, _, hv⟩ := mem_image.mp hm
  exact ⟨v, hv⟩

/-- A full deep carrier rooted on the chosen side fills every deep point of
its radial axis. The conclusion concerns actual preserved vertices. -/
theorem full_deep_root_axis {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4) (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (u : (↑F : Set (GridVertex n n))) (hu : u ∈ C.supp)
    (t : Fin n) (hut : u.val = sideChart s (t, ⟨0, by omega⟩))
    (ht : 2 ≤ t.val ∧ t.val + 2 < n)
    (hfull : (deepCarrierPart F C).card = n - 4)
    (d : Fin n) (hd : 2 ≤ d.val ∧ d.val + 2 < n) :
    sideChart s (t, d) ∈ F := by
  classical
  let A := deepCarrierPart F C
  let z := sideChart s (t, d)
  have hs (v : A) : v.val ∈ C.supp := Set.mem_toFinset.mp (mem_filter.mp v.property).1
  have hbox (v : A) : 2 ≤ v.val.val.1.val ∧ v.val.val.1.val < n - 2 ∧
      2 ≤ v.val.val.2.val ∧ v.val.val.2.val < n - 2 := by
    have hd := (mem_filter.mp v.property).2
    unfold IsGridBoundary IsNextRing at hd
    omega
  have hzbox : 2 ≤ z.1.val ∧ z.1.val < n - 2 ∧ 2 ≤ z.2.val ∧ z.2.val < n - 2 := by
    fin_cases s <;> simp [z, sideChart] <;> omega
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < A.card by change 0 < (deepCarrierPart F C).card; omega)
  have hvbox := hbox ⟨v, hv⟩
  dsimp only at hvbox
  change z ∈ F
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · have hur := congrArg Fin.val (hr u hu)
    have hvr := congrArg Fin.val (hr v (hs ⟨v, hv⟩))
    have hzr : z.1 = r := by
      rw [hut] at hur
      fin_cases s <;> simp [z, sideChart, Fin.ext_iff] at hur ⊢ <;> omega
    let f : A → Fin (n - 4) := fun w => ⟨w.val.val.2.val - 2, by have := hbox w; omega⟩
    have hi : Function.Injective f := by
      intro w x he
      have he' := congrArg Fin.val he
      have hw := hbox w
      have hx := hbox x
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext ((hr _ (hs w)).trans (hr _ (hs x)).symm) (Fin.ext ?_)
      dsimp [f] at he'
      omega
    obtain ⟨w, hw⟩ := full_image f hi (by simpa only [Fintype.card_coe] using hfull)
      ⟨z.2.val - 2, by omega⟩
    have he' := congrArg Fin.val hw
    have hwbox := hbox w
    have he : w.val.val = z := by
      apply Prod.ext
      · exact (hr _ (hs w)).trans hzr.symm
      · apply Fin.ext
        dsimp [f] at he'
        omega
    exact he ▸ w.val.property
  · have huc := congrArg Fin.val (hc u hu)
    have hvc := congrArg Fin.val (hc v (hs ⟨v, hv⟩))
    have hzc : z.2 = c := by
      rw [hut] at huc
      fin_cases s <;> simp [z, sideChart, Fin.ext_iff] at huc ⊢ <;> omega
    let f : A → Fin (n - 4) := fun w => ⟨w.val.val.1.val - 2, by have := hbox w; omega⟩
    have hi : Function.Injective f := by
      intro w x he
      have he' := congrArg Fin.val he
      have hw := hbox w
      have hx := hbox x
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext (Fin.ext ?_) ((hc _ (hs w)).trans (hc _ (hs x)).symm)
      dsimp [f] at he'
      omega
    obtain ⟨w, hw⟩ := full_image f hi (by simpa only [Fintype.card_coe] using hfull)
      ⟨z.1.val - 2, by omega⟩
    have he' := congrArg Fin.val hw
    have hwbox := hbox w
    have he : w.val.val = z := by
      apply Prod.ext
      · apply Fin.ext
        dsimp [f] at he'
        omega
      · exact (hc _ (hs w)).trans hzc.symm
    exact he ▸ w.val.property

end GridGraphs.CarrierLayers.FourCarrier
