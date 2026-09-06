import GridGraphs.Results.SmallDiagonalExact.LedgerFive
import GridGraphs.Results.SmallDiagonalExact.AttachmentCasesFive
import GridGraphs.Constructions.Finite.FiniteDiagonalConstructions

/-!
# Exact `5 x 5` value

The ledger classification and attachment exclusions give the upper bound of
eleven, matched by the finite diagonal construction.
-/

namespace GridGraphs.SmallDiagonalProof

open Finset SimpleGraph

/-- Every acyclic forced set in the `5 x 5` grid has at most eleven vertices. -/
theorem _root_.GridGraphs.forced_five_five_card_le_eleven
    (F : Finset (GridVertex 5 5))
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic) :
    F.card ≤ 11 := by
  have hle12 := forced_five_five_card_le_twelve F hacyc
  by_contra hnot
  have hcard : F.card = 12 := by omega
  rcases forced_five_five_twelve_ledger_profile F hcard hacyc with hprofile | hprofile
  · rcases hprofile.2.2.2 with hthreeCorners | hfinal
    · exact forced_five_five_twelve_boundary_three_corners_impossible F hcard hacyc
        ⟨hprofile.1, hprofile.2.1, hprofile.2.2.1,
          hthreeCorners.1, hthreeCorners.2⟩
    · have hreduce := forced_five_five_twelve_final_profile_reduction F hcard hacyc
        hfinal.1 hfinal.2 hprofile.2.2.1
      obtain ⟨hcorners, homit00, homit04, homit44, homit40,
        x, hxOutside, hxF, hxNotBoundary, hxLocation⟩ := hreduce
      have hPcard : (boundaryForcedPositions55 F).card = 11 := by
        rw [boundaryForcedPositions55_card_eq_boundary_inter, hfinal.2]
      have hrunsLower := final_profile_three_runs_lower F hacyc hPcard
        homit00 homit04 homit44 homit40
      obtain ⟨hruns, hdegree⟩ := final_profile_three_runs_and_one_attachment
        F x hxOutside hxF hxNotBoundary hxLocation hacyc hcard hprofile.2.1
        hrunsLower
      have hxCases : x = (2, 2) ∨ x = (1, 2) ∨ x = (2, 3) ∨
          x = (3, 2) ∨ x = (2, 1) := by
        rcases hxLocation with h | h
        · exact Or.inl h
        · change adjacent 5 5 (2, 2) x at h
          rcases h with ⟨hrow, hcol | hcol⟩ | ⟨hcol, hrow | hrow⟩
          · right; right; left
            apply Prod.ext <;> apply Fin.ext <;> norm_num at hrow hcol ⊢ <;> omega
          · right; right; right; right
            apply Prod.ext <;> apply Fin.ext <;> norm_num at hrow hcol ⊢ <;> omega
          · right; right; right; left
            apply Prod.ext <;> apply Fin.ext <;> norm_num at hrow hcol ⊢ <;> omega
          · right; left
            apply Prod.ext <;> apply Fin.ext <;> norm_num at hrow hcol ⊢ <;> omega
      rcases hxCases with rfl | rfl | rfl | rfl | rfl
      · have hpos : 0 < ((gridGraph 5 5).induce
            (↑F : Set (GridVertex 5 5))).degree ⟨(2, 2), hxF⟩ := by
          rw [hdegree]
          norm_num
        obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
        have hxy : (gridGraph 5 5).Adj (2, 2) y.1 := by
          simpa [SimpleGraph.mem_neighborFinset] using hy
        have hyBoundary : y.1 ∈ boundary55 := by
          by_contra hyNotBoundary
          have hyOutside : y.1 ∈ F \ boundary55 :=
            Finset.mem_sdiff.mpr ⟨y.2, hyNotBoundary⟩
          have hySingleton : y.1 ∈ ({(2, 2)} : Finset (GridVertex 5 5)) := by
            rw [← hxOutside]
            exact hyOutside
          have hyCenter : y.1 = (2, 2) := by simpa using hySingleton
          exact (gridGraph 5 5).ne_of_adj hxy hyCenter.symm
        change adjacent 5 5 (2, 2) y.1 at hxy
        simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and] at hyBoundary
        rcases hxy with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
          rcases hyBoundary with h | h | h | h <;> norm_num at hr hc h <;> omega
      · exact final_profile_attachment_top_impossible F hxOutside hxF hacyc hPcard
          hcorners homit00 homit04 homit44 homit40 hruns hdegree
      · exact final_profile_attachment_right_impossible F hxOutside hxF hacyc hPcard
          hcorners homit00 homit40 hruns hdegree
      · exact final_profile_attachment_bottom_impossible F hxOutside hxF hacyc hPcard
          hcorners homit00 homit04 hruns hdegree
      · exact final_profile_attachment_left_impossible F hxOutside hxF hacyc hPcard
          hcorners homit04 homit44 hruns hdegree
  · exact forced_five_five_twelve_boundary_four_corners_impossible F
      hprofile.2.2.2 hprofile.2.2.1 hacyc

/-- The exact maximum number of preserved vertices in the `5 x 5` grid. -/
theorem _root_.GridGraphs.maxPreserved_five_five : maxPreserved 5 5 = 11 := by
  apply Nat.le_antisymm
  · apply maxPreserved_le_of_forall
    intro T _ hT
    let F : Finset (GridVertex 5 5) :=
      Finset.univ.filter fun v => isPreserved 5 5 T v
    have hacyc : (forcedEdgeGraph (gridGraph 5 5)
        (↑F : Set (GridVertex 5 5))).IsAcyclic := by
      apply forcedEdgeGraph_isAcyclic_of_preserves hT.isAcyclic
      intro v hv
      apply preservesIncidentEdges_of_le_of_degree_eq (gridGraph 5 5) T hT.le
      change v ∈ F at hv
      exact (Finset.mem_filter.mp hv).2
    simpa [F, numPreserved] using forced_five_five_card_le_eleven F hacyc
  · exact eleven_le_maxPreserved_five_five

end GridGraphs.SmallDiagonalProof
