import GridGraphs.Geometry.GridLayers
import GridGraphs.Accounting.CarrierLayerBound
import GridGraphs.Constructions.BoundaryFive.BoundaryFiveConstruction

/-! # Global next-ring injection into the complementary boundary -/

namespace GridGraphs

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Clockwise diagonal assignment, with priority top, bottom, left, right. -/
def nextRingBoundaryMap {n : Nat} (hn : 5 ≤ n)
    (v : {v : GridVertex n n // IsNextRing v}) : GridVertex n n :=
  if v.val.1.val = 1 then
    (⟨0, by omega⟩, ⟨v.val.2.val - 1, by have := v.val.2.isLt; omega⟩)
  else if v.val.1.val = n - 2 then
    (⟨n - 1, by omega⟩, ⟨v.val.2.val + 1, by have := v.property; unfold IsNextRing at this; omega⟩)
  else if v.val.2.val = 1 then
    (⟨v.val.1.val + 1, by have := v.property; unfold IsNextRing at this; omega⟩, ⟨0, by omega⟩)
  else
    (⟨v.val.1.val - 1, by have := v.val.1.isLt; omega⟩, ⟨n - 1, by omega⟩)

theorem nextRingBoundaryMap_boundary {n : Nat} (hn : 5 ≤ n)
    (v : {v : GridVertex n n // IsNextRing v}) :
    IsGridBoundary (nextRingBoundaryMap hn v) := by
  unfold nextRingBoundaryMap
  split_ifs <;> unfold IsGridBoundary <;> dsimp <;> omega

theorem nextRingBoundaryMap_injective {n : Nat} (hn : 5 ≤ n) :
    Function.Injective (nextRingBoundaryMap hn) := by
  intro v w he
  have hv := v.property
  have hw := w.property
  unfold IsNextRing at hv hw
  have hr := congrArg (fun x : GridVertex n n => x.1.val) he
  have hc := congrArg (fun x : GridVertex n n => x.2.val) he
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  all_goals
    unfold nextRingBoundaryMap at hr hc
    split_ifs at hr hc <;> dsimp at hr hc <;> omega

/-- Opposite vertices of a unit cell cannot both be preserved. -/
theorem nextRingBoundaryMap_notMem {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (v : {v : GridVertex n n // IsNextRing v}) (hvF : v.val ∈ F) :
    nextRingBoundaryMap hn v ∉ F := by
  have hv := v.property
  unfold IsNextRing at hv
  have diagonal (r c : Fin (n - 1)) :
      (cell00 r c ∉ F ∨ cell11 r c ∉ F) ∧
      (cell01 r c ∉ F ∨ cell10 r c ∉ F) := by
    rcases grid_cell_has_unforced_edge r c hacyc with h | h | h | h
    · exact ⟨Or.inl h.1, Or.inl h.2⟩
    · exact ⟨Or.inr h.2, Or.inl h.1⟩
    · exact ⟨Or.inr h.1, Or.inr h.2⟩
    · exact ⟨Or.inl h.2, Or.inr h.1⟩
  let r : Fin (n - 1) := ⟨v.val.1.val, by omega⟩
  let c : Fin (n - 1) := ⟨v.val.2.val, by omega⟩
  let rm : Fin (n - 1) := ⟨v.val.1.val - 1, by omega⟩
  let cm : Fin (n - 1) := ⟨v.val.2.val - 1, by omega⟩
  have eqv11 : cell11 rm cm = v.val := by
    apply Prod.ext <;> apply Fin.ext <;> simp [cell11, rm, cm] <;> omega
  have eqv00 : cell00 r c = v.val := by rfl
  have eqv01 : cell01 r cm = v.val := by
    apply Prod.ext <;> apply Fin.ext <;> simp [cell01, r, cm]
    omega
  have eqv10 : cell10 rm c = v.val := by
    apply Prod.ext <;> apply Fin.ext <;> simp [cell10, rm, c]
    omega
  unfold nextRingBoundaryMap
  split_ifs with ht hb hl
  · have he : (⟨0, by omega⟩, ⟨v.val.2.val - 1, by omega⟩) = cell00 rm cm := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell00, rm, cm]
      omega
    rw [he]
    exact (diagonal rm cm).1.resolve_right (by simpa [eqv11] using hvF)
  · have he : (⟨n - 1, by omega⟩, ⟨v.val.2.val + 1, by omega⟩) = cell11 r c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell11, r, c]
      omega
    rw [he]
    exact (diagonal r c).1.resolve_left (by simpa [eqv00] using hvF)
  · have he : (⟨v.val.1.val + 1, by omega⟩, ⟨0, by omega⟩) = cell10 r cm := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell10, r, cm]
      omega
    rw [he]
    exact (diagonal r cm).2.resolve_left (by simpa [eqv01] using hvF)
  · have he : (⟨v.val.1.val - 1, by omega⟩, ⟨n - 1, by omega⟩) = cell01 rm c := by
      apply Prod.ext <;> apply Fin.ext <;> simp [cell01, rm, c]
      omega
    rw [he]
    exact (diagonal rm c).2.resolve_right (by simpa [eqv10] using hvF)

/-- Global unweighted injection bound; no boundary budget is prescribed. -/
theorem forced_nextRing_card_le_compl_boundary_card {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (F.filter IsNextRing).card ≤ ((univ \ F).filter IsGridBoundary).card := by
  classical
  apply card_le_card_of_injOn (fun v => if h : IsNextRing v then
    nextRingBoundaryMap hn ⟨v, h⟩ else v)
  · intro v hv
    obtain ⟨hvF, hvr⟩ := mem_filter.mp hv
    dsimp only
    rw [dif_pos hvr]
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,
      nextRingBoundaryMap_notMem hn F hacyc ⟨v, hvr⟩ hvF⟩,
      nextRingBoundaryMap_boundary hn ⟨v, hvr⟩⟩
  · intro v hv w hw he
    have hvr := (mem_filter.mp hv).2
    have hwr := (mem_filter.mp hw).2
    simp only [dif_pos hvr, dif_pos hwr] at he
    exact congrArg Subtype.val (nextRingBoundaryMap_injective hn he)

theorem compl_boundary_card_le_boundaryDeficiencySum {n : Nat} (hn : 2 ≤ n)
    (F : Finset (GridVertex n n)) :
    ((univ \ F).filter IsGridBoundary).card ≤ boundaryDeficiencySum n n (univ \ F) := by
  calc
    _ = ∑ _v ∈ (univ \ F).filter IsGridBoundary, 1 := by simp
    _ ≤ ∑ v ∈ (univ \ F).filter IsGridBoundary, gridBoundaryDeficiency n n v :=
      sum_le_sum (fun v hv => one_le_gridBoundaryDeficiency_of_boundary hn hn v
        (mem_filter.mp hv).2)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)

/-- The global perimeter inequality in terms of pure carriers and deficiency. -/
theorem perimeter_le_pureBoundaryCarriers_add_twice_boundaryDeficiency {n : Nat}
    (hn : 7 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    4 * n - 4 ≤ n * (pureBoundaryCarriers F).card +
      2 * boundaryDeficiencySum n n (univ \ F) := by
  classical
  have hB := forced_boundary_card_le_pureBoundaryCarriers_add_nextRing (by omega) F hacyc
  have hE := forced_nextRing_card_le_compl_boundary_card (by omega) F hacyc
  have hU := compl_boundary_card_le_boundaryDeficiencySum (by omega) F
  have hsplit : (F.filter IsGridBoundary).card +
      ((univ \ F).filter IsGridBoundary).card = 4 * n - 4 := by
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
  omega

end GridGraphs
