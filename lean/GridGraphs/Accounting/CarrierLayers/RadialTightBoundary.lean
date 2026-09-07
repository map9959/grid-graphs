import GridGraphs.Accounting.CarrierLayers.RadialSide

/-!
# Boundary saturation at the tight radial budget

These are necessary conditions, not an exclusion of the tight budget.
No maximality or lower bound on the preserved cardinality is assumed.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Every missing pure-carrier side saturates the packing bound at `b = 2k+2`.
Its complement on the boundary has exactly two holes, both near corners;
all corners are preserved. The statement retains the witness set so that
subsequent geometric arguments can use the exact boundary decomposition. -/
theorem tight_missing_side_boundary {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 2)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    (F.filter (OnOpenSide s)).card = k ∧
    ∃ Q : Finset (GridVertex (3 * k + 2) (3 * k + 2)),
      Q.card = 4 ∧ Q ⊆ univ \ F ∧ (∀ v ∈ Q, BoundarySix.Near v) ∧
      (Q.filter (OnOpenSide s)).card = 2 ∧
      ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card = 2 ∧
      (∀ v, IsGridBoundary v → (v ∉ F ↔ OnOpenSide s v ∧ v ∉ F ∨ v ∈ Q)) ∧
      (∀ v, BoundarySix.Corner v → v ∈ F) := by
  classical
  have hpacking := missing_side_preserved_card_le (by omega) F hacyc s hmissing
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := BoundarySix.corner_witnesses (by omega) F hacyc
  have hnear := near_openSide_card_le_two (by omega) Q hQnear s
  let S := univ.filter (OnOpenSide (n := 3 * k + 2) s)
  let B := (univ \ F).filter IsGridBoundary
  let R := (S \ F) ∪ (Q \ S)
  have hScard : S.card = 3 * k := by
    simpa only [Nat.add_sub_cancel] using openSide_card (by omega : 2 ≤ 3 * k + 2) s
  have hSF : S ∩ F = F.filter (OnOpenSide s) := by
    ext v
    simp only [S, mem_inter, mem_filter, mem_univ, true_and]
    exact and_comm
  have hQS : Q ∩ S = Q.filter (OnOpenSide s) := by
    ext v
    simp [S]
  have hApart := card_sdiff_add_card_inter S F
  have hBpart := card_sdiff_add_card_inter Q S
  rw [hSF] at hApart
  rw [hQS] at hBpart
  have hdisjoint : Disjoint (S \ F) (Q \ S) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_sdiff.mp hv).1
  have hRcard : R.card = (S \ F).card + (Q \ S).card :=
    card_union_of_disjoint hdisjoint
  have hQboundary : ∀ v ∈ Q, IsGridBoundary v := by
    intro v hv
    have h := hQnear v hv
    unfold BoundarySix.Near IsGridBoundary at *
    omega
  have hsub : R ⊆ B := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hv).2⟩,
        openSide_boundary (mem_filter.mp (mem_sdiff.mp hv).1).2⟩
    · exact mem_filter.mpr ⟨hQU (mem_sdiff.mp hv).1,
        hQboundary v (mem_sdiff.mp hv).1⟩
  have hBbound : B.card ≤ 2 * k + 2 := by
    calc
      _ = ∑ _v ∈ B, 1 := by simp
      _ ≤ ∑ v ∈ B, gridBoundaryDeficiency (3 * k + 2) (3 * k + 2) v :=
        sum_le_sum (fun v hv => one_le_gridBoundaryDeficiency_of_boundary
          (by omega) (by omega) v (mem_filter.mp hv).2)
      _ ≤ boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by simp)
      _ = _ := hb
  have hle := card_le_card hsub
  have hpacking_eq : (F.filter (OnOpenSide s)).card = k := by omega
  have hQside : (Q.filter (OnOpenSide s)).card = 2 := by omega
  have hoff : (Q \ S).card = 2 := by omega
  have hRB : R = B := eq_of_subset_of_card_le hsub (by omega)
  have hdecomp (v : GridVertex (3 * k + 2) (3 * k + 2)) (hv : IsGridBoundary v) :
      v ∉ F ↔ OnOpenSide s v ∧ v ∉ F ∨ v ∈ Q := by
    constructor
    · intro hu
      have hm : v ∈ R := hRB.symm ▸ mem_filter.mpr ⟨by simp [hu], hv⟩
      rcases mem_union.mp hm with hm | hm
      · exact Or.inl ⟨(mem_filter.mp (mem_sdiff.mp hm).1).2, (mem_sdiff.mp hm).2⟩
      · exact Or.inr (mem_sdiff.mp hm).1
    · rintro (h | h)
      · exact h.2
      · exact (mem_sdiff.mp (hQU h)).2
  refine ⟨hpacking_eq, Q, hQcard, hQU, hQnear, hQside, ?_, hdecomp, ?_⟩
  · have he : (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) =
        Q \ S := by
      ext v
      simp only [mem_filter, mem_sdiff, mem_univ, true_and, S]
      constructor
      · rintro ⟨hu, hv, hs⟩
        exact ⟨((hdecomp v hv).mp hu).resolve_left (fun h => hs h.1), hs⟩
      · rintro ⟨hq, hs⟩
        exact ⟨(mem_sdiff.mp (hQU hq)).2, hQboundary v hq, hs⟩
    rw [he]
    exact hoff
  · intro v hc
    have hv : IsGridBoundary v := by
      unfold BoundarySix.Corner IsGridBoundary at *
      omega
    by_contra hu
    rcases (hdecomp v hv).mp hu with hs | hq
    · have hs := hs.1
      unfold BoundarySix.Corner OnOpenSide OnSide at *
      omega
    · have hn := hQnear v hq
      unfold BoundarySix.Corner BoundarySix.Near at *
      omega

/-- Both near-corner positions on a missing side are holes at the tight budget. -/
theorem tight_missing_side_endpoints_unpreserved {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 2)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val)
    (v : GridVertex (3 * k + 2) (3 * k + 2))
    (hvs : OnOpenSide s v) (hvn : BoundarySix.Near v) : v ∉ F := by
  classical
  obtain ⟨_, Q, _, hQU, hQnear, hQside, _⟩ :=
    tight_missing_side_boundary hk F hacyc hb s hmissing
  have hpos {w : GridVertex (3 * k + 2) (3 * k + 2)}
      (hs : OnOpenSide s w) (hn : BoundarySix.Near w) :
      sidePosition s w = 1 ∨ sidePosition s w = 3 * k := by
    unfold OnOpenSide OnSide at hs
    unfold BoundarySix.Near at hn
    unfold sidePosition
    split <;> omega
  intro hvF
  have hneq (w : GridVertex (3 * k + 2) (3 * k + 2))
      (hw : w ∈ Q.filter (OnOpenSide s)) : sidePosition s w ≠ sidePosition s v := by
    intro he
    have heq := sidePosition_injective (mem_filter.mp hw).2 hvs he
    exact (mem_sdiff.mp (hQU (mem_filter.mp hw).1)).2 (heq.symm ▸ hvF)
  have hsmall : (Q.filter (OnOpenSide s)).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    apply sidePosition_injective (mem_filter.mp ha).2 (mem_filter.mp hb).2
    have ha' := hpos (mem_filter.mp ha).2 (hQnear a (mem_filter.mp ha).1)
    have hb' := hpos (mem_filter.mp hb).2 (hQnear b (mem_filter.mp hb).1)
    have hv' := hpos hvs hvn
    have hna := hneq a ha
    have hnb := hneq b hb
    omega
  omega

/-- In the at-most-three branch the tight boundary structure occurs on some
side. In particular equality forces all four corners to be preserved. -/
theorem tight_boundary_corners_preserved {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 2) :
    ∀ v, BoundarySix.Corner v → v ∈ F := by
  obtain ⟨s, hs⟩ := exists_side_without_pure_carrier (by omega) F hacyc hp
  obtain ⟨_, Q, _, _, _, _, _, _, hc⟩ := tight_missing_side_boundary hk F hacyc hb s hs
  exact hc

/-- An unpreserved corner rules out the tight endpoint of the radial bound. -/
theorem boundaryDeficiency_ge_of_unpreserved_corner {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (v : GridVertex (3 * k + 2) (3 * k + 2))
    (hc : BoundarySix.Corner v) (hu : v ∉ F) :
    2 * k + 3 ≤ boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) := by
  have hlower := two_mul_add_two_le_boundaryDeficiencySum_of_pure_carriers_le_three
    hk F hacyc hp
  have hne : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) ≠ 2 * k + 2 := by
    intro hb
    exact hu (tight_boundary_corners_preserved hk F hacyc hp hb v hc)
  omega

end GridGraphs.CarrierLayers
