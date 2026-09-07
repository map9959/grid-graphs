import GridGraphs.Accounting.CarrierLayers.FourCarrier.Capacity

/-! # Physical perimeter and deep deficits

`K` counts unused perimeter capacity and `D` counts unused deep capacity.
The exact identity keeps these losses separate from boundary deficiency.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Exact physical loss ledger, using natural subtraction only after proving
both capacities. The deep count is the actual number of preserved deep vertices. -/
theorem physical_deficit_identity {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    let B := (F.filter IsGridBoundary).card
    let E := (F.filter IsNextRing).card
    let Z := (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card
    let d := Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent -
      (pureBoundaryCarriers F).card - (nextRingCarriers F).card
    let K := (4 * n - 4) - (B + E)
    let D := (n - 4) * d - Z
    B + E ≤ 4 * n - 4 ∧ Z ≤ (n - 4) * d ∧
      F.card + K + D = 4 * n - 4 + (n - 4) * d := by
  classical
  dsimp only
  have hring (v : GridVertex n n) (hv : IsNextRing v) : ¬ IsGridBoundary v := by
    unfold IsNextRing at hv
    unfold IsGridBoundary
    omega
  have hpart := card_filter_add_card_filter_not (s := F) (p := IsGridBoundary)
  have hinner := card_filter_add_card_filter_not
    (s := F.filter (fun v => ¬ IsGridBoundary v)) (p := IsNextRing)
  have hE : (F.filter (fun v => ¬ IsGridBoundary v)).filter IsNextRing =
      F.filter IsNextRing := by
    ext v
    simp only [mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hring v h.2⟩, h.2⟩⟩
  have hZ : (F.filter (fun v => ¬ IsGridBoundary v)).filter (fun v => ¬ IsNextRing v) =
      F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v) := by
    ext v
    simp [and_assoc]
  rw [hE, hZ] at hinner
  have hcap := card_le_layers_without_nextRing_carriers (by omega) F hacyc
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

/-- Natural-number form of `f = T+6 + (3k-2)(d-(k-1)) - K-D`, avoiding
truncation when `d<k-1`. No missing-side or score hypothesis is needed. -/
theorem residueTwo_physical_deficit_identity {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) :
    let d := Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent -
      (pureBoundaryCarriers F).card - (nextRingCarriers F).card
    let K := 12 * k + 4 - ((F.filter IsGridBoundary).card + (F.filter IsNextRing).card)
    let D := (3 * k - 2) * d -
      (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card
    F.card + K + D + (3 * k - 2) * (k - 1) =
      3 * k ^ 2 + 7 * k + 6 + (3 * k - 2) * d := by
  have h := (physical_deficit_identity (by omega) F hacyc).2.2
  have hn : 3 * k + 2 - 4 = 3 * k - 2 := by omega
  have hper : 4 * (3 * k + 2) - 4 = 12 * k + 4 := by omega
  rw [hn, hper] at h
  have hk1 : k - 1 + 1 = k := by omega
  have hk2 : 3 * k - 2 + 2 = 3 * k := by omega
  dsimp only
  nlinarith

/-- At `h=0`, minimal nonpure count leaves at least `k+1` perimeter holes
unused by the fixed boundary injection. This is a physical `K` bound, not
an additional boundary-deficiency charge. -/
theorem missing_side_minimal_no_shallow_perimeter_loss {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val)
    (hzero : (nextRingCarriers F).card = 0)
    (hd : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent - (pureBoundaryCarriers F).card = k - 1) :
    k + 1 ≤ 12 * k + 4 -
      ((F.filter IsGridBoundary).card + (F.filter IsNextRing).card) := by
  have hq := missing_side_preserved_card_le (by omega) F hacyc s hmissing
  have hholes := side_holes_add_roots (by omega) F s
  have himage := layers_add_side_holes_le_perimeter_add_nonpure (by omega) F hacyc hzero s
  rw [hd] at himage
  omega

/-- At the minimal deep count `d=k-1`, any one-excess configuration has
`K+D=5`. Thus six physical loss units close this branch. -/
theorem minimal_deep_one_excess_deficit {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : F.card = 3 * k ^ 2 + 7 * k + 1)
    (hd : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent -
      (pureBoundaryCarriers F).card - (nextRingCarriers F).card = k - 1) :
    (12 * k + 4 - ((F.filter IsGridBoundary).card + (F.filter IsNextRing).card)) +
      ((3 * k - 2) * (k - 1) -
        (F.filter (fun v => ¬ IsGridBoundary v ∧ ¬ IsNextRing v)).card) = 5 := by
  have h := (physical_deficit_identity (by omega) F hacyc).2.2
  rw [hd, hf] at h
  have hn : 3 * k + 2 - 4 = 3 * k - 2 := by omega
  have hper : 4 * (3 * k + 2) - 4 = 12 * k + 4 := by omega
  rw [hn, hper] at h
  have htotal : 12 * k + 4 + (3 * k - 2) * (k - 1) =
      3 * k ^ 2 + 7 * k + 6 := by
    have hk1 : k - 1 + 1 = k := by omega
    have hk2 : 3 * k - 2 + 2 = 3 * k := by omega
    nlinarith
  omega

/-- The paper's final image-loss certificate: for minimal deep count, an image
bound `K+J >= k+2` closes the target when `J<=1`, or when `J<=2` and `k>=6`.
At `k=5`, `J<=2` instead requires one actual deep deficit unit. The image bound
and the exceptional deep loss remain explicit geometric hypotheses. -/
theorem minimal_deep_loss_certificate {k K D J : Nat} (hk : 5 ≤ k)
    (hbudget : K + D = 5) (himage : k + 2 ≤ K + J)
    (hlocal : J ≤ 1 ∨ (J ≤ 2 ∧ 6 ≤ k) ∨ (J ≤ 2 ∧ 1 ≤ D)) : False := by
  omega

end GridGraphs.CarrierLayers.FourCarrier
