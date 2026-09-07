import GridGraphs.Accounting.CarrierLayers.NextRingInjection

/-!
# Physical boundary occupancy without a missing-side assumption

Keep the actual pure-carrier mass rather than replacing it by `n * p`.
Nonpure carriers have at most two boundary contacts, by straightness. These
contacts are counted in disjoint actual component supports, not an auxiliary
forest. This does not assert nonreuse of holes or of inward witnesses of UU gaps.
-/

namespace GridGraphs

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Actual preserved vertices belonging to pure boundary carriers. -/
noncomputable def pureBoundaryVertices {n : Nat} (F : Finset (GridVertex n n)) :
    Finset (↑F : Set (GridVertex n n)) :=
  (pureBoundaryCarriers F).biUnion fun C => C.supp.toFinset

/-- A nonpure straight component has at most two physical boundary contacts. -/
theorem nonpure_carrier_boundary_card_le_two {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (hC : C ∉ pureBoundaryCarriers F) :
    (C.supp.toFinset.filter (fun v : (↑F : Set (GridVertex n n)) =>
      IsGridBoundary v.val)).card ≤ 2 := by
  classical
  have hnot : ¬ ∀ v ∈ C.supp, IsGridBoundary v.val := by
    simpa [pureBoundaryCarriers] using hC
  push Not at hnot
  obtain ⟨u, hu, hub⟩ := hnot
  let S := C.supp.toFinset.filter (fun v => IsGridBoundary v.val)
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · let f : S → Fin 2 := fun v => if v.val.val.2.val = 0 then 0 else 1
    have hinj : Function.Injective f := by
      intro v w he
      have hv := mem_filter.mp v.property
      have hw := mem_filter.mp w.property
      have hrv := hr v.val (Set.mem_toFinset.mp hv.1)
      have hrw := hr w.val (Set.mem_toFinset.mp hw.1)
      have hru := congrArg Fin.val (hr u hu)
      have hvr := congrArg Fin.val hrv
      have hwr := congrArg Fin.val hrw
      have hbV := hv.2
      have hbW := hw.2
      unfold IsGridBoundary at hub hbV hbW
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext (hrv.trans hrw.symm) (Fin.ext ?_)
      dsimp [f] at he
      split_ifs at he <;> norm_num at he <;> omega
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      Fintype.card_le_of_injective f hinj
  · let f : S → Fin 2 := fun v => if v.val.val.1.val = 0 then 0 else 1
    have hinj : Function.Injective f := by
      intro v w he
      have hv := mem_filter.mp v.property
      have hw := mem_filter.mp w.property
      have hcv := hc v.val (Set.mem_toFinset.mp hv.1)
      have hcw := hc w.val (Set.mem_toFinset.mp hw.1)
      have hcu := congrArg Fin.val (hc u hu)
      have hvc := congrArg Fin.val hcv
      have hwc := congrArg Fin.val hcw
      have hbV := hv.2
      have hbW := hw.2
      unfold IsGridBoundary at hub hbV hbW
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext (Fin.ext ?_) (hcv.trans hcw.symm)
      dsimp [f] at he
      split_ifs at he <;> norm_num at he <;> omega
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      Fintype.card_le_of_injective f hinj

/-- Pure occupancy plus two slots per nonpure carrier covers the boundary.
The two slots may be on opposite sides, so no distinct-carrier claim is made
for boundary contacts on different sides. -/
theorem boundary_card_le_pure_mass_add_twice_nonpure {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (F.filter IsGridBoundary).card ≤ (pureBoundaryVertices F).card +
      2 * (Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent -
        (pureBoundaryCarriers F).card) := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let S := pureBoundaryCarriers F
  let B := univ.filter (fun v : (↑F : Set (GridVertex n n)) => IsGridBoundary v.val)
  let R := (univ \ S).biUnion fun C =>
    C.supp.toFinset.filter (fun v => IsGridBoundary v.val)
  have hcover : B ⊆ pureBoundaryVertices F ∪ R := by
    intro v hv
    have hmem : v ∈ (G.connectedComponentMk v).supp.toFinset := by
      simp [ConnectedComponent.mem_supp_iff]
    by_cases h : G.connectedComponentMk v ∈ S
    · exact mem_union_left _ (mem_biUnion.mpr ⟨_, h, hmem⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨_,
        mem_sdiff.mpr ⟨mem_univ _, h⟩, mem_filter.mpr ⟨hmem, (mem_filter.mp hv).2⟩⟩)
  have hR : R.card ≤ 2 * (Fintype.card G.ConnectedComponent - S.card) := by
    calc
      _ ≤ ∑ C ∈ univ \ S,
          (C.supp.toFinset.filter (fun v => IsGridBoundary v.val)).card := card_biUnion_le
      _ ≤ ∑ _C ∈ univ \ S, 2 := sum_le_sum fun C hC =>
        nonpure_carrier_boundary_card_le_two F hacyc C (mem_sdiff.mp hC).2
      _ = _ := by simp [card_sdiff_of_subset (subset_univ S), Nat.mul_comm, G]
  have hB : B.card = (F.filter IsGridBoundary).card := by
    apply card_bij (fun v _ => v.val)
    · intro v hv
      exact mem_filter.mpr ⟨v.property, (mem_filter.mp hv).2⟩
    · intro v _ w _ h
      exact Subtype.ext h
    · intro v hv
      exact ⟨⟨v, (mem_filter.mp hv).1⟩,
        mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩, rfl⟩
  have h := (card_le_card hcover).trans (card_union_le _ _)
  rw [hB] at h
  exact h.trans (Nat.add_le_add_left hR _)

/-- Retaining pure mass in the existing physical next-ring injection. -/
theorem boundary_card_le_pure_mass_add_nextRing {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (F.filter IsGridBoundary).card ≤
      (pureBoundaryVertices F).card + (F.filter IsNextRing).card := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let A := univ.filter (fun u : (↑F : Set (GridVertex n n)) =>
    IsGridBoundary u.val ∧ G.connectedComponentMk u ∉ pureBoundaryCarriers F)
  have hex (u : A) : ∃ w : (↑F : Set (GridVertex n n)),
      w ∈ (G.connectedComponentMk u.val).supp ∧ IsNextRing w.val ∧
        (gridGraph n n).Adj u.val.val w.val :=
    boundary_nonpure_carrier_nextRing_neighbor hn F hacyc _
      (mem_filter.mp u.property).2.2 (by simp [ConnectedComponent.mem_supp_iff, G])
      (mem_filter.mp u.property).2.1
  let f : A → F.filter IsNextRing := fun u => ⟨(hex u).choose.val,
    mem_filter.mpr ⟨(hex u).choose.property, (hex u).choose_spec.2.1⟩⟩
  have hinj : Function.Injective f := by
    intro u v he
    have he' : (hex u).choose.val = (hex v).choose.val :=
      congrArg (fun x : F.filter IsNextRing => x.val) he
    apply Subtype.ext
    apply Subtype.ext
    exact nextRing_preserved_boundary_neighbor_unique hn F hacyc
      u.val.property v.val.property (hex u).choose.property
      (mem_filter.mp u.property).2.1 (mem_filter.mp v.property).2.1
      (hex u).choose_spec.2.1 (hex u).choose_spec.2.2
      (he' ▸ (hex v).choose_spec.2.2)
  have hA : A.card ≤ (F.filter IsNextRing).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  have hcover : univ.filter (fun u : (↑F : Set (GridVertex n n)) =>
      IsGridBoundary u.val) ⊆ pureBoundaryVertices F ∪ A := by
    intro u hu
    by_cases h : G.connectedComponentMk u ∈ pureBoundaryCarriers F
    · exact mem_union_left _ (mem_biUnion.mpr ⟨_, h, by
        simp [ConnectedComponent.mem_supp_iff, G]⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hu).2, h⟩)
  have hcard : (univ.filter (fun u : (↑F : Set (GridVertex n n)) =>
      IsGridBoundary u.val)).card = (F.filter IsGridBoundary).card := by
    apply card_bij (fun v _ => v.val)
    · intro v hv
      exact mem_filter.mpr ⟨v.property, (mem_filter.mp hv).2⟩
    · intro v _ w _ h
      exact Subtype.ext h
    · intro v hv
      exact ⟨⟨v, (mem_filter.mp hv).1⟩,
        mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩, rfl⟩
  have h := (card_le_card hcover).trans (card_union_le _ _)
  rw [hcard] at h
  exact h.trans (Nat.add_le_add_left hA _)

private theorem covered_boundary_partition {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n)) :
    (F.filter IsGridBoundary).card + ((univ \ F).filter IsGridBoundary).card =
      4 * n - 4 := by
  classical
  have hu : F.filter IsGridBoundary ∪ (univ \ F).filter IsGridBoundary =
      ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset := by
    ext v
    simp only [mem_union, mem_filter, mem_sdiff, mem_univ, true_and,
      Set.mem_toFinset, Set.mem_ofPred_eq]
    by_cases h : v ∈ F <;> simp [h]
  have hd : Disjoint (F.filter IsGridBoundary) ((univ \ F).filter IsGridBoundary) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp (mem_filter.mp hw).1).2 (mem_filter.mp hv).1
  rw [← card_union_of_disjoint hd, hu, BoundaryFiveConstruction.boundary_card hn]

/-- General lower bounds on actual pure boundary occupancy. Both budgets hold
simultaneously, but they must not be added: they charge the same contacts. -/
theorem perimeter_le_pure_mass_physical_budgets {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    4 * n - 4 ≤ (pureBoundaryVertices F).card +
        2 * boundaryDeficiencySum n n (univ \ F) ∧
    4 * n - 4 ≤ (pureBoundaryVertices F).card +
        boundaryDeficiencySum n n (univ \ F) +
        2 * (Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent -
          (pureBoundaryCarriers F).card) := by
  have hpartition := covered_boundary_partition hn F
  have hholes := compl_boundary_card_le_boundaryDeficiencySum (by omega) F
  have hring := forced_nextRing_card_le_compl_boundary_card (by omega) F hacyc
  have hmass := boundary_card_le_pure_mass_add_nextRing (by omega) F hacyc
  have hcontacts := boundary_card_le_pure_mass_add_twice_nonpure F hacyc
  omega

/-- The pure mass is the sum of lengths of disjoint actual carriers, and fits
in their full-side capacities. -/
theorem pure_boundary_mass_eq_sum_le_capacity {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (pureBoundaryVertices F).card =
        ∑ C ∈ pureBoundaryCarriers F, C.supp.toFinset.card ∧
      (pureBoundaryVertices F).card ≤ n * (pureBoundaryCarriers F).card := by
  classical
  have heq : (pureBoundaryVertices F).card =
      ∑ C ∈ pureBoundaryCarriers F, C.supp.toFinset.card := by
    apply card_biUnion
    intro C _ D _ hne
    simpa using pairwise_disjoint_supp_connectedComponent
      ((gridGraph n n).induce (↑F : Set _)) hne
  refine ⟨heq, ?_⟩
  rw [heq]
  calc
    _ ≤ ∑ _C ∈ pureBoundaryCarriers F, n := by
      apply sum_le_sum
      intro C _
      rw [Set.toFinset_card]
      rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
      · have hinj : Function.Injective (fun v : C.supp => v.val.val.2) := by
          intro v w h
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext ((hr v.val v.property).trans (hr w.val w.property).symm) h
        simpa using Fintype.card_le_of_injective _ hinj
      · have hinj : Function.Injective (fun v : C.supp => v.val.val.1) := by
          intro v w h
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext h ((hc v.val v.property).trans (hc w.val w.property).symm)
        simpa using Fintype.card_le_of_injective _ hinj
    _ = _ := by simp [Nat.mul_comm]

/-- Full-side capacity shortfall, with no truncated subtraction in the bound.
For exactly four pure carriers this says `n*p - P ≤ 4 + 2*b`. -/
theorem pure_boundary_shortfall_le_deficiency {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    n * (pureBoundaryCarriers F).card - (pureBoundaryVertices F).card + 4 * n ≤
      n * (pureBoundaryCarriers F).card + 4 +
        2 * boundaryDeficiencySum n n (univ \ F) := by
  have hcap := (pure_boundary_mass_eq_sum_le_capacity F hacyc).2
  have hbudget := (perimeter_le_pure_mass_physical_budgets hn F hacyc).1
  omega

/-- In the exactly-four-pure-carrier branch, total full-side shortfall obeys
both the hole budget and the nonpure-contact budget. Coverage itself is not
needed, so the statement also applies before the four sides are identified. -/
theorem pure_boundary_four_carrier_shortfall {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card = 4) :
    4 * n - (pureBoundaryVertices F).card ≤
        4 + 2 * boundaryDeficiencySum n n (univ \ F) ∧
    4 * n - (pureBoundaryVertices F).card + 4 ≤
        boundaryDeficiencySum n n (univ \ F) +
        2 * Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent := by
  have hcap := (pure_boundary_mass_eq_sum_le_capacity F hacyc).2
  have hbudget := perimeter_le_pure_mass_physical_budgets hn F hacyc
  have hpr := pureBoundaryCarriers_card_le F
  rw [hp] at hcap hbudget hpr
  omega

end GridGraphs
