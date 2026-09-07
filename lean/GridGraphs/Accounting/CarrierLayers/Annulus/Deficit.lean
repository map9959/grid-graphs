import GridGraphs.Accounting.CarrierLayers.Annulus.Bridges

/-! # Annulus loss and actual deep deficits

Each nonfull deep carrier loses at least one deep vertex. Full carriers are
bounded by physical bridges, while pure and shallow carriers survive as
distinct induced annulus components.
-/

namespace GridGraphs.CarrierLayers.Annulus

open Finset SimpleGraph FourCarrier

attribute [local instance] Classical.propDecidable

noncomputable def deepCarriers {n : Nat} (F : Finset (GridVertex n n)) :
    Finset (Carrier F) := univ \ (pureBoundaryCarriers F ∪ nextRingCarriers F)

theorem pure_shallow_disjoint {n : Nat} (F : Finset (GridVertex n n)) :
    Disjoint (pureBoundaryCarriers F) (nextRingCarriers F) := by
  apply Finset.disjoint_left.mpr
  intro C hp hs
  exact (mem_filter.mp hs).2.1 hp

theorem carrier_partition {n : Nat} (F : Finset (GridVertex n n)) :
    (deepCarriers F).card + (pureBoundaryCarriers F).card + (nextRingCarriers F).card =
      Fintype.card (Carrier F) := by
  have h := card_sdiff_add_card_eq_card
    (subset_univ (pureBoundaryCarriers F ∪ nextRingCarriers F))
  rw [card_union_of_disjoint (pure_shallow_disjoint F), card_univ] at h
  change (deepCarriers F).card +
    ((pureBoundaryCarriers F).card + (nextRingCarriers F).card) = Fintype.card (Carrier F) at h
  omega

theorem deepCarriers_card {n : Nat} (F : Finset (GridVertex n n)) :
    (deepCarriers F).card = Fintype.card (Carrier F) -
      (pureBoundaryCarriers F).card - (nextRingCarriers F).card := by
  have h := carrier_partition F
  omega

theorem deepCarrier_of_mem_deepVertices {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n)) (C : Carrier F) {v : GridVertex n n}
    (hv : v ∈ deepVertices F C) : C ∈ deepCarriers F := by
  obtain ⟨hvF, hs, ha⟩ := (mem_deepVertices hn F C v).mp hv
  have hl : ¬ IsGridBoundary v ∧ ¬ IsNextRing v := by
    rw [mem_iff_layers hn] at ha
    exact not_or.mp ha
  refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
  rintro h
  rcases mem_union.mp h with hp | hh
  · exact hl.1 ((mem_filter.mp hp).2 _ hs)
  · exact ((mem_filter.mp hh).2.2 _ hs).elim hl.1 hl.2

theorem fullCarriers_subset_deepCarriers {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n)) : fullCarriers F ⊆ deepCarriers F := by
  intro C hC
  have hc : (deepVertices F C).card = n - 4 := (mem_filter.mp hC).2
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < (deepVertices F C).card by omega)
  exact deepCarrier_of_mem_deepVertices hn F C hv

/-- `d <= M + D`: every nonfull actual deep carrier contributes a deficit unit. -/
theorem deep_count_le_full_add_deficit {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (deepCarriers F).card ≤ (fullCarriers F).card +
      ((n - 4) * (deepCarriers F).card -
        (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card) := by
  let R := deepCarriers F
  let Z := F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)
  have hcover : R.biUnion (deepVertices F) = Z := by
    ext v
    constructor
    · intro hv
      obtain ⟨C, _, hvC⟩ := mem_biUnion.mp hv
      obtain ⟨hvF, _, ha⟩ := (mem_deepVertices hn F C v).mp hvC
      rw [mem_iff_layers hn] at ha
      exact mem_filter.mpr ⟨hvF, not_or.mp ha⟩
    · intro hv
      obtain ⟨hvF, hvb, hvr⟩ := mem_filter.mp hv
      let C := ((gridGraph n n).induce (↑F : Set _)).connectedComponentMk ⟨v, hvF⟩
      have hvC : v ∈ deepVertices F C := (mem_deepVertices hn F C v).mpr
        ⟨hvF, by simp [C, ConnectedComponent.mem_supp_iff],
          fun ha => ((mem_iff_layers hn v).mp ha).elim hvb hvr⟩
      exact mem_biUnion.mpr ⟨C, deepCarrier_of_mem_deepVertices hn F C hvC, hvC⟩
  have hZ : Z.card ≤ ∑ C ∈ R, (deepVertices F C).card := by
    rw [← hcover]
    exact card_biUnion_le
  have hcap (C : Carrier F) : (deepVertices F C).card ≤ n - 4 := by
    rw [deepVertices_card]
    exact deep_carrier_part_card_le hn F hacyc C
  have hlocal (C : Carrier F) : (deepVertices F C).card + 1 ≤
      (n - 4) + (if C ∈ fullCarriers F then 1 else 0) := by
    have hc := hcap C
    by_cases hf : C ∈ fullCarriers F
    · rw [if_pos hf]
      omega
    · rw [if_neg hf]
      have hne : (deepVertices F C).card ≠ n - 4 := by
        simpa only [fullCarriers, mem_filter, mem_univ, true_and] using hf
      omega
  have hsum := sum_le_sum (s := R) (fun C _ => hlocal C)
  have hfilter : R.filter (fun C => C ∈ fullCarriers F) = fullCarriers F := by
    ext C
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨fullCarriers_subset_deepCarriers hn F h, h⟩⟩
  simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one, sum_boole,
    Nat.cast_id, hfilter] at hsum
  change R.card ≤ (fullCarriers F).card + ((n - 4) * R.card - Z.card)
  rw [Nat.mul_comm R.card (n - 4)] at hsum
  omega

/-- Whole pure and shallow carriers have distinct induced annulus components.
The map back into the full induced graph certifies distinctness. -/
theorem pure_add_shallow_le_annulus_components {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n)) :
    (pureBoundaryCarriers F).card + (nextRingCarriers F).card ≤
      Fintype.card ((graph n).induce (↑(selected F) : Set _)).ConnectedComponent := by
  let G := (gridGraph n n).induce (↑F : Set _)
  let L := (graph n).induce (↑(selected F) : Set _)
  let Q := pureBoundaryCarriers F ∪ nextRingCarriers F
  have hex (C : Q) := C.1.nonempty_supp
  choose u hu using hex
  have hA (C : Q) : Mem (u C).1 := by
    apply (mem_iff_layers hn _).mpr
    rcases mem_union.mp C.2 with hp | hs
    · exact Or.inl ((mem_filter.mp hp).2 _ (hu C))
    · exact (mem_filter.mp hs).2.2 _ (hu C)
  let v (C : Q) : (↑(selected F) : Set (Vertex n)) :=
    ⟨⟨(u C).1, hA C⟩, mem_filter.mpr ⟨mem_univ _, (u C).2⟩⟩
  let f (C : Q) : L.ConnectedComponent := L.connectedComponentMk (v C)
  let inc : L →g G :=
    { toFun := fun w => ⟨w.1.1, (mem_filter.mp w.2).2⟩
      map_rel' := by intro x y h; exact h }
  have hmap (C : Q) : (f C).map inc = C.1 := hu C
  have hi : Function.Injective f := by
    intro C D he
    apply Subtype.ext
    exact (hmap C).symm.trans ((congrArg (fun c => c.map inc) he).trans (hmap D))
  have hc := Fintype.card_le_of_injective f hi
  rw [Fintype.card_coe, card_union_of_disjoint (pure_shallow_disjoint F)] at hc
  exact hc

/-- Global physical loss inequality `r + 5 <= 2K + D`. -/
theorem components_add_five_le_twice_loss_add_deficit {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    Fintype.card (Carrier F) + 5 ≤
      2 * ((4 * n - 4) - (F.filter IsGridBoundary).card - (F.filter IsNextRing).card) +
      ((n - 4) * (Fintype.card (Carrier F) -
          (pureBoundaryCarriers F).card - (nextRingCarriers F).card) -
        (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card) := by
  have hb := component_budget hn F hacyc
  have hm := fullCarriers_card_add_one_le_components (by omega : 5 ≤ n) F hacyc
  have hd := deep_count_le_full_add_deficit (by omega : 5 ≤ n) F hacyc
  have ha := pure_add_shallow_le_annulus_components (by omega : 5 ≤ n) F
  have hp := carrier_partition F
  rw [deepCarriers_card] at hd hp
  omega

end GridGraphs.CarrierLayers.Annulus
