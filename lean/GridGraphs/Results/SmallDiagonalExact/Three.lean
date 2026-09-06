import GridGraphs.Constructions.Finite.FiniteDiagonalConstructions
import GridGraphs.Geometry.StraightForcedComponents
import GridGraphs.Accounting.ComponentReduction
import GridGraphs.Accounting.PerimeterWaste

/-!
# Exact `3 x 3` value

The corner-charge ledger and straightness obstruction give the upper bound of four.
-/

namespace GridGraphs.SmallDiagonalProof

open Finset SimpleGraph

def corners33 : Finset (GridVertex 3 3) :=
  Finset.univ.filter fun v =>
    (v.1.val = 0 ∨ v.1.val + 1 = 3) ∧
      (v.2.val = 0 ∨ v.2.val + 1 = 3)

lemma corners33_card : corners33.card = 4 := by
  let endpoints : Finset (Fin 3) := {0, 2}
  have hcorners : corners33 = endpoints ×ˢ endpoints := by
    ext v
    rw [Finset.mem_product]
    simp only [corners33, Finset.mem_filter, Finset.mem_univ, true_and,
      endpoints, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> rintro ⟨hr, hc⟩
    · constructor
      · rcases hr with h | h
        · left; apply Fin.ext; omega
        · right; apply Fin.ext; omega
      · rcases hc with h | h
        · left; apply Fin.ext; omega
        · right; apply Fin.ext; omega
    · constructor
      · rcases hr with h | h
        · left; simp [h]
        · right; have := congrArg Fin.val h; norm_num at this ⊢; omega
      · rcases hc with h | h
        · left; simp [h]
        · right; have := congrArg Fin.val h; norm_num at this ⊢; omega
  have hendpoints : endpoints.card = 2 := by
    rw [Finset.card_pair]
    intro h
    have := congrArg Fin.val h
    norm_num at this
  rw [hcorners, Finset.card_product, hendpoints]

lemma boundaryDeficiency33_le_corner_charge (v : GridVertex 3 3) :
    gridBoundaryDeficiency 3 3 v ≤ 1 + if v ∈ corners33 then 1 else 0 := by
  by_cases hr : v.1.val = 0 ∨ v.1.val + 1 = 3
  · by_cases hc : v.2.val = 0 ∨ v.2.val + 1 = 3
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_corner (by omega) (by omega) v hr hc]
      have hv : v ∈ corners33 := by
        simp only [corners33, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hr, hc⟩
      simp [hv]
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_border (by omega) (by omega) v (Or.inl ⟨hr, hc⟩)]
      simp [corners33]
  · by_cases hc : v.2.val = 0 ∨ v.2.val + 1 = 3
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_border (by omega) (by omega) v (Or.inr ⟨hr, hc⟩)]
      simp [corners33]
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_interior (by omega) (by omega) v hr hc]
      simp [corners33]

lemma boundaryDeficiencySum33_le (F : Finset (GridVertex 3 3)) :
    boundaryDeficiencySum 3 3 F ≤ F.card + (F ∩ corners33).card := by
  unfold boundaryDeficiencySum
  calc
    (∑ v ∈ F, gridBoundaryDeficiency 3 3 v) ≤
        ∑ v ∈ F, (1 + if v ∈ corners33 then 1 else 0) := by
      exact Finset.sum_le_sum fun v _ => boundaryDeficiency33_le_corner_charge v
    _ = F.card + (F ∩ corners33).card := by
      rw [Finset.sum_add_distrib]
      simp

lemma two_le_induced_component_count_of_card_five
    (F : Finset (GridVertex 3 3)) (hFcard : F.card = 5)
    (hacyc : (forcedEdgeGraph (gridGraph 3 3)
      (↑F : Set (GridVertex 3 3))).IsAcyclic) :
    2 ≤ Fintype.card ((gridGraph 3 3).induce
      (↑F : Set (GridVertex 3 3))).ConnectedComponent := by
  classical
  let H := (gridGraph 3 3).induce (↑F : Set (GridVertex 3 3))
  have hnot : ¬∀ u v : (↑F : Set (GridVertex 3 3)), H.Reachable u v := by
    intro hall
    have hnonempty : (Set.univ : Set (↑F : Set (GridVertex 3 3))).Nonempty := by
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
      exact ⟨⟨v, hv⟩, Set.mem_univ _⟩
    have hstraight := induced_forced_preconnected_set_straight hacyc hnonempty
      (fun _ _ _ _ => hall _ _)
    rcases hstraight with ⟨r, hr⟩ | ⟨c, hc⟩
    · have hinj : Function.Injective
          (fun v : (↑F : Set (GridVertex 3 3)) => v.1.2) := by
        intro u v huv
        apply Subtype.ext
        apply Prod.ext
        · exact (hr u (Set.mem_univ u)).trans (hr v (Set.mem_univ v)).symm
        · exact huv
      have hcard := Fintype.card_le_of_injective _ hinj
      simp [hFcard] at hcard
    · have hinj : Function.Injective
          (fun v : (↑F : Set (GridVertex 3 3)) => v.1.1) := by
        intro u v huv
        apply Subtype.ext
        apply Prod.ext
        · exact huv
        · exact (hc u (Set.mem_univ u)).trans (hc v (Set.mem_univ v)).symm
      have hcard := Fintype.card_le_of_injective _ hinj
      simp [hFcard] at hcard
  push Not at hnot
  obtain ⟨u, v, huv⟩ := hnot
  let cu := H.connectedComponentMk u
  let cv := H.connectedComponentMk v
  have hcne : cu ≠ cv := by
    intro h
    exact huv (ConnectedComponent.exact h)
  let pairComponents : Finset H.ConnectedComponent := {cu, cv}
  have hpair : pairComponents.card = 2 := by
    simp [pairComponents, hcne]
  have hsub : pairComponents ⊆ (Finset.univ : Finset H.ConnectedComponent) :=
    Finset.subset_univ _
  have := Finset.card_le_card hsub
  simpa [H, hpair] using this

lemma perimeter_edge_has_corner33 {u v : GridVertex 3 3}
    (h : IsPerimeterEdge 3 u v) : u ∈ corners33 ∨ v ∈ corners33 := by
  rcases h with ⟨hadj, hu, hv⟩
  unfold IsBoundaryVertex at hu hv
  unfold gridGraph adjacent at hadj
  simp only [corners33, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hadj with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
  · have hrowval := congrArg Fin.val hrow
    rcases hcol with hcol | hcol <;> omega
  · have hcolval := congrArg Fin.val hcol
    rcases hrow with hrow | hrow <;> omega

lemma numPreserved_three_three_le_four
    (T : SimpleGraph (GridVertex 3 3)) [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 3 3) T) :
    numPreserved 3 3 T ≤ 4 := by
  have hbasic := preserved_le_refinedUB (m := 3) (n := 3) (by omega) (by omega) hT
  simp only [refinedUB, I, D] at hbasic
  norm_num at hbasic
  by_contra hnot
  have hscore : numPreserved 3 3 T = 5 := by omega
  let F : Finset (GridVertex 3 3) :=
    Finset.univ.filter fun v => isPreserved 3 3 T v
  have hFcard : F.card = 5 := by simpa [F, numPreserved] using hscore
  have hacyc : (forcedEdgeGraph (gridGraph 3 3)
      (↑F : Set (GridVertex 3 3))).IsAcyclic := by
    apply forcedEdgeGraph_isAcyclic_of_preserves hT.isAcyclic
    intro v hv
    apply preservesIncidentEdges_of_le_of_degree_eq (gridGraph 3 3) T hT.le
    change v ∈ F at hv
    exact (Finset.mem_filter.mp hv).2
  have hcomponent := grid_component_reduction F hacyc
  have hinduced := two_le_induced_component_count_of_card_five F hFcard hacyc
  have hforced : 1 ≤ Fintype.card
      (forcedEdgeGraph (gridGraph 3 3)
        (↑F : Set (GridVertex 3 3))).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (gridGraph 3 3)
      (↑F : Set (GridVertex 3 3))).connectedComponentMk
        ((⟨0, by omega⟩, ⟨0, by omega⟩) : GridVertex 3 3)⟩
  have hdef : 9 ≤ boundaryDeficiencySum 3 3 F := by omega
  have hdefUpper := boundaryDeficiencySum33_le F
  have hcornersCard : (F ∩ corners33).card = 4 := by
    have hinter : (F ∩ corners33).card ≤ corners33.card :=
      Finset.card_le_card (Finset.inter_subset_right)
    rw [corners33_card] at hinter
    omega
  have hcorners : corners33 ⊆ F := by
    have hinterEq : F ∩ corners33 = corners33 := by
      exact Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [hcornersCard, corners33_card])
    intro v hv
    have : v ∈ F ∩ corners33 := by simpa [hinterEq] using hv
    exact (Finset.mem_inter.mp this).1
  obtain ⟨u, v, hperimeter, huv⟩ := exists_omitted_perimeter_edge (n := 3)
    (by omega) hT
  rcases perimeter_edge_has_corner33 hperimeter with hu | hv
  · exact huv (preservesIncidentEdges_of_le_of_degree_eq
      (gridGraph 3 3) T hT.le u
      ((Finset.mem_filter.mp (hcorners hu)).2) hperimeter.1)
  · exact huv ((preservesIncidentEdges_of_le_of_degree_eq
      (gridGraph 3 3) T hT.le v
      ((Finset.mem_filter.mp (hcorners hv)).2) hperimeter.1.symm).symm)

/-- Exactly four vertices can be preserved in the `3 x 3` grid. -/
theorem _root_.GridGraphs.maxPreserved_three_three : maxPreserved 3 3 = 4 := by
  exact Nat.le_antisymm
    (maxPreserved_le_of_forall fun T _ hT => numPreserved_three_three_le_four T hT)
    four_le_maxPreserved_three_three

end GridGraphs.SmallDiagonalProof
