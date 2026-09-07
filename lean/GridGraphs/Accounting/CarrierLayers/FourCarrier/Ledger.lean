import GridGraphs.Accounting.CarrierLayers.FourCarrier.OffsidePath
import GridGraphs.Accounting.CarrierLayers.CoveredGlobalMissingSides
import GridGraphs.Accounting.CarrierLayers.MissingSideSharp

/-! # Exact missing-side slack

The offside path count supplies the nonnegative weighted slack. Together with
the existing score and root-carrier bounds it forces three or four pure carriers.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- The open side partitions into roots and holes, including neither corner. -/
theorem side_holes_add_roots {n : Nat} (hn : 2 ≤ n)
    (F : Finset (GridVertex n n)) (s : Fin 4) :
    ((univ \ F).filter (OnOpenSide s)).card + (F.filter (OnOpenSide s)).card = n - 2 := by
  classical
  let S := univ.filter (OnOpenSide (n := n) s)
  have hSF : S ∩ F = F.filter (OnOpenSide s) := by ext v; simp [S, and_comm]
  have hSU : S \ F = (univ \ F).filter (OnOpenSide s) := by
    ext v
    simp [S, and_comm]
  have hpart := card_sdiff_add_card_inter S F
  rw [hSF, hSU] at hpart
  exact hpart.trans (openSide_card hn s)

/-- Weighted offside cost is at least `p-1`. This uses ordinary offside holes
only once; corner deficiency can only increase the available cost. -/
theorem pure_add_side_length_le_deficiency_add_roots_add_one {n : Nat} (hn : 2 ≤ n)
    (F : Finset (GridVertex n n)) (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    (pureBoundaryCarriers F).card + (n - 2) ≤
      boundaryDeficiencySum n n (univ \ F) + (F.filter (OnOpenSide s)).card + 1 := by
  have hp := pure_carriers_le_offside_holes_add_one hn F s hmissing
  have hside := side_holes_add_roots hn F s
  have hb := compl_boundary_card_le_boundaryDeficiencySum hn F
  let U := (univ \ F).filter IsGridBoundary
  have hpart := card_filter_add_card_filter_not (s := U) (p := OnOpenSide s)
  have hS : U.filter (OnOpenSide s) = (univ \ F).filter (OnOpenSide s) := by
    ext v
    simp only [U, mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩,
      fun h => ⟨⟨h.1, openSide_boundary h.2⟩, h.2⟩⟩
  have hO : U.filter (fun v => ¬ OnOpenSide s v) =
      (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) := by
    ext v
    simp [U, and_assoc]
  rw [hS, hO] at hpart
  change U.card ≤ _ at hb
  omega

/-- Exact natural slack for every missing-side counterexample, with no prior
upper bound on `p`. Here `W=b-(3k-q)` is the weighted offside cost. -/
theorem missing_side_exact_slack {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    let q := (F.filter (OnOpenSide s)).card
    let p := (pureBoundaryCarriers F).card
    let r := Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent
    let c := Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent
    let b := boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F)
    let W := b - (3 * k - q)
    F.card = 3 * k ^ 2 + 7 * k + 1 ∧
      ∃ z w gamma : Nat, r = q + p + z ∧ W = p - 1 + w ∧
        c = 1 + gamma ∧ z + w + gamma + 2 * p = 9 := by
  classical
  dsimp only
  have hq := missing_side_preserved_card_le (by omega) F hacyc s hmissing
  have hp := stable_counterexample_three_le_pure_carriers hk F hacyc hf
  have hr := missing_side_roots_add_pure_le_components F hacyc s hmissing
  have hb := pure_add_side_length_le_deficiency_add_roots_add_one (by omega) F s hmissing
  have hc : 1 ≤ Fintype.card (forcedEdgeGraph
      (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).connectedComponentMk (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hfe := Nat.le_antisymm
    (residueTwo_card_le_target_add_one_of_missing_side hk F hacyc ⟨s, hmissing⟩) hf
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  have hsum : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent +
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 3 * k + 9 := by
    nlinarith
  refine ⟨hfe,
    Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent -
      ((F.filter (OnOpenSide s)).card + (pureBoundaryCarriers F).card),
    boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) -
      (3 * k - (F.filter (OnOpenSide s)).card) - ((pureBoundaryCarriers F).card - 1),
    Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent - 1, ?_⟩
  omega

/-- Every missing-side counterexample has exactly three or four pure carriers. -/
theorem missing_side_pure_cases {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card) :
    (pureBoundaryCarriers F).card = 3 ∨ (pureBoundaryCarriers F).card = 4 := by
  obtain ⟨_, z, w, gamma, _, _, _, hslack⟩ :=
    missing_side_exact_slack hk F hacyc s hmissing hf
  have hp := stable_counterexample_three_le_pure_carriers hk F hacyc hf
  omega

/-- At four pure carriers exactly one slack unit remains, so `W` is three
or four. The three alternatives record which resource uses that unit. -/
theorem four_pure_missing_side_slack {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val)
    (hf : 3 * k ^ 2 + 7 * k + 1 ≤ F.card)
    (hp : (pureBoundaryCarriers F).card = 4) :
    let q := (F.filter (OnOpenSide s)).card
    let r := Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent
    let c := Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent
    let W := boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) - (3 * k - q)
    (r = q + 5 ∧ W = 3 ∧ c = 1) ∨
      (r = q + 4 ∧ W = 4 ∧ c = 1) ∨
      (r = q + 4 ∧ W = 3 ∧ c = 2) := by
  obtain ⟨_, z, w, gamma, hr, hW, hc, hslack⟩ :=
    missing_side_exact_slack hk F hacyc s hmissing hf
  dsimp only
  omega

end GridGraphs.CarrierLayers.FourCarrier
