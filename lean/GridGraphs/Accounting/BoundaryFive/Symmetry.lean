import GridGraphs.Accounting.BoundaryFive.GapPosition

/-! # Positioning only the boundary-five gap

Pull back the preserved set by one of the eight square symmetries. Only its
cardinality and forced acyclicity are transported; no other holes are normalized.
-/

namespace GridGraphs.BoundaryFive

open Finset SimpleGraph

private def frame {n : Nat} (r c s : Bool) (v : GridVertex n n) : GridVertex n n :=
  let x := if s then v.2 else v.1
  let y := if s then v.1 else v.2
  (if r then x.rev else x, if c then y.rev else y)

private theorem frame_injective {n : Nat} (r c s : Bool) :
    Function.Injective (frame (n := n) r c s) := by
  intro x y h
  cases r <;> cases c <;> cases s <;>
    simp [frame, Prod.ext_iff, Fin.ext_iff] at * <;> omega

private theorem frame_adj {n : Nat} (r c s : Bool) {x y : GridVertex n n}
    (h : (gridGraph n n).Adj x y) :
    (gridGraph n n).Adj (frame r c s x) (frame r c s y) := by
  cases r <;> cases c <;> cases s <;>
    simp [frame, gridGraph, adjacent, Fin.ext_iff] at * <;> omega

private theorem orient_second_near {n : Nat} (hn : 9 ≤ n)
    (u q : GridVertex n n) (hu : BoundarySix.Second u) (hq : BoundarySix.Near q)
    (hadj : (gridGraph n n).Adj u q) :
    ∃ r c s : Bool,
      frame r c s (⟨0, by omega⟩, ⟨1, by omega⟩) = q ∧
      frame r c s (⟨0, by omega⟩, ⟨2, by omega⟩) = u := by
  simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
  unfold BoundarySix.Near at hq
  rcases hu with ⟨hr | hr, hc | hc⟩ | ⟨hc | hc, hr | hr⟩
  · refine ⟨false, false, false, ?_, ?_⟩
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp [frame] <;> omega
  · refine ⟨false, true, false, ?_, ?_⟩
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp [frame] <;> omega
  · refine ⟨true, false, false, ?_, ?_⟩
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp [frame] <;> omega
  · refine ⟨true, true, false, ?_, ?_⟩
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp [frame] <;> omega
  · refine ⟨false, false, true, ?_, ?_⟩
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp [frame] <;> omega
  · refine ⟨true, false, true, ?_, ?_⟩
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp [frame] <;> omega
  · refine ⟨false, true, true, ?_, ?_⟩
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp [frame] <;> omega
  · refine ⟨true, true, true, ?_, ?_⟩
    all_goals apply Prod.ext <;> apply Fin.ext <;> simp [frame] <;> omega

/-- Every boundary-five feasible set has an equally large feasible pullback
whose two gap holes are `(0,1)` and `(0,2)`. No component or deficiency
transport is needed to apply an endpoint profile to the pullback. -/
theorem exists_top_gap_pullback {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5) :
    ∃ F' : Finset (GridVertex n n), F'.card = F.card ∧
      (forcedEdgeGraph (gridGraph n n) (↑F' : Set _)).IsAcyclic ∧
      (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F' ∧
      (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F' := by
  classical
  obtain ⟨Q, u, _, _, hholes, hnear, hu, q, hq, hadj⟩ :=
    holes_eq_insert_second hn F hacyc hb
  have huF : u ∉ F := by
    have hm : u ∈ (univ \ F).filter IsGridBoundary := by rw [hholes]; simp
    exact (mem_sdiff.mp (mem_filter.mp hm).1).2
  have hqF : q ∉ F := by
    have hm : q ∈ (univ \ F).filter IsGridBoundary := by rw [hholes]; simp [hq]
    exact (mem_sdiff.mp (mem_filter.mp hm).1).2
  obtain ⟨r, c, s, heq, heu⟩ := orient_second_near hn u q hu (hnear q hq) hadj
  let F' := univ.filter (fun v => frame r c s v ∈ F)
  have hmem (v : GridVertex n n) : v ∈ F' ↔ frame r c s v ∈ F := by simp [F']
  have hcard : F'.card = F.card := by
    apply card_bij (fun v _ => frame r c s v)
    · intro v hv
      exact (hmem v).mp hv
    · intro v _ w _ h
      exact frame_injective r c s h
    · intro v hv
      obtain ⟨w, hw⟩ := (Finite.surjective_of_injective (frame_injective r c s)) v
      exact ⟨w, (hmem w).mpr (hw ▸ hv), hw⟩
  have hac : (forcedEdgeGraph (gridGraph n n) (↑F' : Set _)).IsAcyclic := by
    let f : forcedEdgeGraph (gridGraph n n) (↑F' : Set _) →g
        forcedEdgeGraph (gridGraph n n) (↑F : Set _) :=
      { toFun := frame r c s
        map_rel' := fun h => ⟨frame_adj r c s h.1,
          h.2.elim (fun h => Or.inl ((hmem _).mp h))
            (fun h => Or.inr ((hmem _).mp h))⟩ }
    exact hacyc.comap f (frame_injective r c s)
  refine ⟨F', hcard, hac, ?_, ?_⟩
  · rw [hmem, heq]
    exact hqF
  · rw [hmem, heu]
    exact huF

end GridGraphs.BoundaryFive
