import GridGraphs.Geometry.GridLayers
import GridGraphs.Geometry.StraightForcedComponents

/-!
# Global carrier layer bounds

Pure boundary carriers have capacity `n`. Every other boundary vertex has a
distinct preserved next-ring neighbor, and only nonpure carriers can contribute
to the deep layer, with capacity `n - 4` each. No deficiency is prescribed.
-/

namespace GridGraphs

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Induced preserved components supported entirely on the grid boundary. -/
noncomputable def pureBoundaryCarriers {n : Nat} (F : Finset (GridVertex n n)) :
    Finset ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent :=
  univ.filter (fun C => ∀ v ∈ C.supp, IsGridBoundary v.val)

/-- Pure boundary carriers are among all induced preserved components. -/
theorem pureBoundaryCarriers_card_le {n : Nat} (F : Finset (GridVertex n n)) :
    (pureBoundaryCarriers F).card ≤
      Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent := by
  classical
  simpa using card_le_card (subset_univ (pureBoundaryCarriers F))

/-- A boundary vertex in a nonpure carrier has a preserved next-ring neighbor
in that same carrier. -/
theorem boundary_nonpure_carrier_nextRing_neighbor {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (hC : C ∉ pureBoundaryCarriers F)
    {u : (↑F : Set (GridVertex n n))} (hu : u ∈ C.supp)
    (hub : IsGridBoundary u.val) :
    ∃ w : (↑F : Set (GridVertex n n)), w ∈ C.supp ∧ IsNextRing w.val ∧
      (gridGraph n n).Adj u.val w.val := by
  classical
  have hnot : ¬ ∀ v ∈ C.supp, IsGridBoundary v.val := by
    simpa [pureBoundaryCarriers] using hC
  push Not at hnot
  obtain ⟨v, hv, hvb⟩ := hnot
  have hsame := induced_forced_reachable_same_row_or_column hacyc
    (C.reachable_of_mem_supp hu hv)
  unfold IsGridBoundary at hub hvb
  rcases hsame with hrow | hcol
  · have he := congrArg Fin.val hrow
    let c : Fin n := ⟨if u.val.2.val = 0 then 1 else n - 2, by
      split <;> omega⟩
    have hc : c.val = 1 ∨ c.val = n - 2 := by
      dsimp [c]; split <;> simp
    have hbetween : (u.val.2.val ≤ c.val ∧ c.val ≤ v.val.2.val) ∨
        (v.val.2.val ≤ c.val ∧ c.val ≤ u.val.2.val) := by
      dsimp [c]; split <;> omega
    obtain ⟨hwF, hwC⟩ := induced_forced_connectedComponent_horizontal_interval
      hacyc C hu hv hrow c hbetween
    refine ⟨⟨(u.val.1, c), hwF⟩, hwC, ?_, ?_⟩
    · dsimp [IsNextRing]; omega
    · change adjacent n n u.val (u.val.1, c)
      left
      refine ⟨rfl, ?_⟩
      dsimp [c]; split <;> omega
  · have he := congrArg Fin.val hcol
    let r : Fin n := ⟨if u.val.1.val = 0 then 1 else n - 2, by
      split <;> omega⟩
    have hr : r.val = 1 ∨ r.val = n - 2 := by
      dsimp [r]; split <;> simp
    have hbetween : (u.val.1.val ≤ r.val ∧ r.val ≤ v.val.1.val) ∨
        (v.val.1.val ≤ r.val ∧ r.val ≤ u.val.1.val) := by
      dsimp [r]; split <;> omega
    obtain ⟨hwF, hwC⟩ := induced_forced_connectedComponent_vertical_interval
      hacyc C hu hv hcol r hbetween
    refine ⟨⟨(r, u.val.2), hwF⟩, hwC, ?_, ?_⟩
    · dsimp [IsNextRing]; omega
    · change adjacent n n u.val (r, u.val.2)
      right
      refine ⟨rfl, ?_⟩
      dsimp [r]; split <;> omega

/-- A preserved next-ring vertex has at most one preserved boundary neighbor. -/
theorem nextRing_preserved_boundary_neighbor_unique {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    {u v w : GridVertex n n} (hu : u ∈ F) (hv : v ∈ F) (hw : w ∈ F)
    (hub : IsGridBoundary u) (hvb : IsGridBoundary v) (hwr : IsNextRing w)
    (huw : (gridGraph n n).Adj u w) (hvw : (gridGraph n n).Adj v w) :
    u = v := by
  have hp := forced_two_edge_walk_parallel hacyc hu hw hv huw hvw.symm
  change adjacent n n u w at huw
  change adjacent n n v w at hvw
  simp only [adjacent, Fin.ext_iff] at huw hvw hp
  unfold IsGridBoundary at hub hvb
  unfold IsNextRing at hwr
  apply Prod.ext <;> apply Fin.ext <;> omega

private theorem subset_box_card {n : Nat} {F : Finset (GridVertex n n)}
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (T : Finset (↑F : Set (GridVertex n n))) (hT : ∀ v ∈ T, v ∈ C.supp)
    (lo width : Nat)
    (hbox : ∀ v ∈ T, lo ≤ v.val.1.val ∧ v.val.1.val < lo + width ∧
      lo ≤ v.val.2.val ∧ v.val.2.val < lo + width) : T.card ≤ width := by
  classical
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · let f : T → Fin width := fun v =>
      ⟨v.val.val.2.val - lo, by have h := hbox v.val v.property; omega⟩
    have hinj : Function.Injective f := by
      intro v w h
      have he := congrArg Fin.val h
      have hv := hbox v.val v.property
      have hw := hbox w.val w.property
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext ((hr v.val (hT _ v.property)).trans
        (hr w.val (hT _ w.property)).symm) (Fin.ext ?_)
      dsimp [f] at he
      omega
    simpa using Fintype.card_le_of_injective f hinj
  · let f : T → Fin width := fun v =>
      ⟨v.val.val.1.val - lo, by have h := hbox v.val v.property; omega⟩
    have hinj : Function.Injective f := by
      intro v w h
      have he := congrArg Fin.val h
      have hv := hbox v.val v.property
      have hw := hbox w.val w.property
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext (Fin.ext ?_) ((hc v.val (hT _ v.property)).trans
        (hc w.val (hT _ w.property)).symm)
      dsimp [f] at he
      omega
    simpa using Fintype.card_le_of_injective f hinj

private theorem subtype_filter_card {n : Nat} (F : Finset (GridVertex n n))
    (P : GridVertex n n → Prop) :
    (univ.filter (fun v : (↑F : Set (GridVertex n n)) => P v.val)).card =
      (F.filter P).card := by
  classical
  apply card_bij (fun v _ => v.val)
  · intro v hv
    exact mem_filter.mpr ⟨v.property, (mem_filter.mp hv).2⟩
  · intro v _ w _ h
    exact Subtype.ext h
  · intro v hv
    exact ⟨⟨v, (mem_filter.mp hv).1⟩,
      mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩, rfl⟩

private theorem component_filter_sum {n : Nat} (F : Finset (GridVertex n n))
    (P : (↑F : Set (GridVertex n n)) → Prop) :
    (∑ C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent,
      (C.supp.toFinset.filter P).card) = (univ.filter P).card := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  have hcover : (univ.biUnion fun C : G.ConnectedComponent =>
      C.supp.toFinset.filter P) = univ.filter P := by
    ext v
    simp [ConnectedComponent.mem_supp_iff]
  rw [← hcover, card_biUnion]
  intro C _ D _ hne
  exact (show Disjoint C.supp.toFinset D.supp.toFinset by
    simpa using pairwise_disjoint_supp_connectedComponent G hne).mono
      (filter_subset _ _) (filter_subset _ _)

/-- Global boundary capacity: pure carriers account for at most `n` boundary
vertices each, and the remaining boundary vertices inject into the next ring. -/
theorem forced_boundary_card_le_pureBoundaryCarriers_add_nextRing {n : Nat}
    (hn : 5 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (F.filter IsGridBoundary).card ≤
      n * (pureBoundaryCarriers F).card + (F.filter IsNextRing).card := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let S := pureBoundaryCarriers F
  let A := univ.filter (fun u : (↑F : Set (GridVertex n n)) =>
    IsGridBoundary u.val ∧ G.connectedComponentMk u ∉ S)
  let R := univ.filter (fun w : (↑F : Set (GridVertex n n)) => IsNextRing w.val)
  have hex (u : A) : ∃ w : (↑F : Set (GridVertex n n)),
      w ∈ (G.connectedComponentMk u.val).supp ∧ IsNextRing w.val ∧
        (gridGraph n n).Adj u.val.val w.val :=
    boundary_nonpure_carrier_nextRing_neighbor hn F hacyc _
      (mem_filter.mp u.property).2.2 (by simp [ConnectedComponent.mem_supp_iff, G])
      (mem_filter.mp u.property).2.1
  let f : A → R := fun u => ⟨(hex u).choose,
    mem_filter.mpr ⟨mem_univ _, (hex u).choose_spec.2.1⟩⟩
  have hinj : Function.Injective f := by
    intro u v h
    have he : (hex u).choose = (hex v).choose := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    exact nextRing_preserved_boundary_neighbor_unique hn F hacyc
      u.val.property v.val.property (hex u).choose.property
      (mem_filter.mp u.property).2.1 (mem_filter.mp v.property).2.1
      (hex u).choose_spec.2.1 (hex u).choose_spec.2.2
      (he ▸ (hex v).choose_spec.2.2)
  have hbad : A.card ≤ (F.filter IsNextRing).card := by
    have h := Fintype.card_le_of_injective f hinj
    simpa only [Fintype.card_coe, R, subtype_filter_card] using h
  let Q := S.biUnion (fun C => C.supp.toFinset)
  have hcap : Q.card ≤ n * S.card := by
    calc
      _ ≤ ∑ C ∈ S, C.supp.toFinset.card := card_biUnion_le
      _ ≤ ∑ _C ∈ S, n := sum_le_sum (fun C _ =>
        subset_box_card hacyc C C.supp.toFinset
          (by intro v hv; exact Set.mem_toFinset.mp hv) 0 n (by intro v _; simp))
      _ = _ := by simp [Nat.mul_comm]
  have hcover : univ.filter (fun u : (↑F : Set (GridVertex n n)) =>
      IsGridBoundary u.val) ⊆ Q ∪ A := by
    intro u hu
    by_cases h : G.connectedComponentMk u ∈ S
    · exact mem_union_left _ (mem_biUnion.mpr ⟨_, h, by
        simp [ConnectedComponent.mem_supp_iff, G]⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hu).2, h⟩)
  have h := (card_le_card hcover).trans (card_union_le Q A)
  rw [subtype_filter_card] at h
  change (F.filter IsGridBoundary).card ≤ n * S.card + (F.filter IsNextRing).card
  omega

/-- Global three-layer capacity. The deep portion of each nonpure component
has at most `n - 4` vertices; pure boundary components have no deep vertices. -/
theorem forced_card_le_boundary_add_nextRing_add_nonpure_carriers {n : Nat}
    (hn : 5 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    F.card ≤ (F.filter IsGridBoundary).card + (F.filter IsNextRing).card +
      (n - 4) * (Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent -
        (pureBoundaryCarriers F).card) := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let S := pureBoundaryCarriers F
  let D := fun v : (↑F : Set (GridVertex n n)) =>
    ¬ IsGridBoundary v.val ∧ ¬ IsNextRing v.val
  let d := fun C : G.ConnectedComponent => (C.supp.toFinset.filter D).card
  have hzero : ∑ C ∈ S, d C = 0 := by
    apply sum_eq_zero
    intro C hC
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hb := (mem_filter.mp hC).2 v (Set.mem_toFinset.mp (mem_filter.mp hv).1)
    exact (mem_filter.mp hv).2.1 hb
  have hcap (C : G.ConnectedComponent) : d C ≤ n - 4 := by
    apply subset_box_card hacyc C _
      (by intro v hv; exact Set.mem_toFinset.mp (mem_filter.mp hv).1) 2 (n - 4)
    intro v hv
    have hd := (mem_filter.mp hv).2
    dsimp [D, IsGridBoundary, IsNextRing] at hd
    omega
  have hrest : (∑ C ∈ univ \ S, d C) ≤
      (n - 4) * (Fintype.card G.ConnectedComponent - S.card) := by
    calc
      _ ≤ ∑ _C ∈ univ \ S, (n - 4) := sum_le_sum (fun C _ => hcap C)
      _ = _ := by simp [card_sdiff_of_subset (subset_univ S), Nat.mul_comm, G]
  have hsplit := sum_sdiff (subset_univ S) (f := d)
  rw [hzero, add_zero] at hsplit
  have hdeep : (univ.filter D).card ≤
      (n - 4) * (Fintype.card G.ConnectedComponent - S.card) := by
    calc
      _ = ∑ C : G.ConnectedComponent, d C := by
        simpa only [d, D] using (component_filter_sum F D).symm
      _ = ∑ C ∈ univ \ S, d C := hsplit.symm
      _ ≤ _ := hrest
  have hcover : (univ : Finset (↑F : Set (GridVertex n n))) =
      univ.filter (fun v => IsGridBoundary v.val) ∪
        univ.filter (fun v => IsNextRing v.val) ∪ univ.filter D := by
    ext v
    simp only [mem_univ, mem_union, mem_filter, true_and, D]
    tauto
  have htotal := card_union_le
    (univ.filter (fun v : (↑F : Set (GridVertex n n)) => IsGridBoundary v.val) ∪
      univ.filter (fun v => IsNextRing v.val)) (univ.filter D)
  rw [← hcover] at htotal
  have houter := card_union_le
    (univ.filter (fun v : (↑F : Set (GridVertex n n)) => IsGridBoundary v.val))
    (univ.filter (fun v => IsNextRing v.val))
  rw [subtype_filter_card, subtype_filter_card] at houter
  have hcard : (univ : Finset (↑F : Set (GridVertex n n))).card = F.card := by simp
  rw [hcard] at htotal
  change F.card ≤ (F.filter IsGridBoundary).card + (F.filter IsNextRing).card +
    (n - 4) * (Fintype.card G.ConnectedComponent - S.card)
  omega

end GridGraphs
