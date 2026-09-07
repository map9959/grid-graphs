import GridGraphs.Constructions.ResidueTwo.RailRepair.Forest

/-! # Exact score and lower bound of the single terminal-rail repair

This is a parity repair, not an accumulating target pump.
-/

namespace GridGraphs.RailRepair

open Finset BoundaryFiveConstruction
open ResidueTwoStaircase (Vertex interval mem_interval)

noncomputable section
attribute [local instance] Classical.propDecidable

theorem right_card {s : ℕ} (hs : 2 ≤ s) (j : Fin s) :
    (right s j).card + (if j.val + 1 = s then 3 else 0) =
      (ResidueTwoStaircase.R s j).card := by
  rw [right, ResidueTwoStaircase.interval_card (by have := j.isLt; omega) (by omega),
    ResidueTwoStaircase.R_card]
  split_ifs <;> have := j.isLt <;> omega

theorem right_sum_card {s : ℕ} (hs : 2 ≤ s) :
    (∑ j : Fin s, (right s j).card) + 3 =
      ∑ j : Fin s, (ResidueTwoStaircase.R s j).card := by
  have he := sum_congr (s₁ := (univ : Finset (Fin s))) rfl (fun j _ => right_card hs j)
  rw [sum_add_distrib] at he
  have hi : (∑ j : Fin s, if j.val + 1 = s then 3 else 0) = 3 := by
    let last : Fin s := ⟨s - 1, by omega⟩
    have hiff (j : Fin s) : j.val + 1 = s ↔ j = last := by
      simp only [Fin.ext_iff, last]
      have := j.isLt
      omega
    simp only [hiff]
    simp
  rwa [hi] at he

theorem basePiece_disjoint {s : ℕ} (hs : 2 ≤ s) :
    Pairwise (fun i j => Disjoint (basePiece s i) (basePiece s j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro v hi hj
  rcases i with u | p | p <;> rcases j with w | k | k <;>
    simp only [basePiece, right, ResidueTwoStaircase.L, mem_interval] at hi hj
  all_goals simp only [ne_eq, Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff] at hij
  all_goals first | exact hij trivial | (try split_ifs at *) <;> omega

theorem base_card {s : ℕ} (hs : 2 ≤ s) : (base s).card + 3 = 3 * s ^ 2 := by
  rw [base, card_biUnion (fun i _ j _ hij => basePiece_disjoint hs hij)]
  have hz : (interval s 2 2 2).card = 1 := by
    rw [ResidueTwoStaircase.interval_card (by omega) (by omega)]
  simp only [BaseIndex, Fintype.sum_sum_type, basePiece, Fintype.sum_unique, hz]
  have hr := right_sum_card hs
  have hb := ResidueTwoStaircase.baseline_card hs
  omega

theorem newPiece_card {s : ℕ} (hs : 2 ≤ s) (i : NewIndex s) :
    (newPiece s i).card = (match i with | .inr (.inl _) => 3 | _ => 1) := by
  rcases i with u | u | u | t <;>
    simp only [newPiece] <;>
    rw [ResidueTwoStaircase.interval_card (by omega) (by omega)] <;> omega

theorem newPiece_disjoint {s : ℕ} (hs : 2 ≤ s) :
    Pairwise (fun i j => Disjoint (newPiece s i) (newPiece s j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro v hi hj
  have footprint_of_mem (k : NewIndex s) (hk : v ∈ newPiece s k) :
      v ∈ newFootprint s k := by
    change newFootprint s k v
    rcases k with u | u | u | t <;>
      simp only [newPiece, mem_interval] at hk <;>
      simp only [newFootprint, ResidueTwoStaircase.Footprint] <;> omega
  exact Set.disjoint_left.mp (new_footprints_disjoint hs hij)
    (footprint_of_mem i hi) (footprint_of_mem j hj)

theorem new_card {s : ℕ} (hs : 2 ≤ s) :
    (univ.biUnion (newPiece s)).card = 5 + (s - 2) / 2 := by
  rw [card_biUnion (fun i _ j _ hij => newPiece_disjoint hs hij)]
  simp [NewIndex, Fintype.sum_sum_type, newPiece_card hs]
  omega

theorem base_new_disjoint {s : ℕ} (hs : 2 ≤ s) :
    Disjoint (base s) (univ.biUnion (newPiece s)) := by
  apply disjoint_left.mpr
  intro v hb hn
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hb
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp hn
  rcases i with u | i | i <;> rcases j with w | w | w | t <;>
    simp only [basePiece, right, ResidueTwoStaircase.L, newPiece, mem_interval] at hi hj
  all_goals (try split_ifs at *) <;> omega

theorem repaired_card {s : ℕ} (hs : 2 ≤ s) :
    (repaired s).card = 3 * s ^ 2 + 1 + s / 2 := by
  rw [repaired, card_union_of_disjoint (base_new_disjoint hs), new_card hs]
  have hb := base_card hs
  omega

/-- The score formula, not an optimum or a target-pump invariant. -/
def score (s : ℕ) : ℕ := 3 * s ^ 2 + 12 * s + 12 + s / 2

theorem Ffull_card {s : ℕ} (hs : 2 ≤ s) : (Ffull (repaired s)).card = score s := by
  rw [BoundaryFiveConstruction.Ffull_card (by omega) (repaired_subset_Deep hs),
    repaired_card hs]
  unfold score
  omega

/-- Unconditional uniform lower bound witnessed by the repaired coordinates. -/
theorem score_le_maxPreserved {s : ℕ} (hs : 2 ≤ s) :
    score s ≤ maxPreserved (3 * s + 5) (3 * s + 5) := by
  rw [← Ffull_card hs, maxPreserved_eq_maxForcedAcyclic (by omega) (by omega)]
  exact Finset.le_sup (f := Finset.card) (mem_acyclicForcedSets.mpr (Ffull_isAcyclic hs))

theorem score_even_gain {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 0) :
    score s = (Ffull (ResidueTwoStaircase.A s)).card + 1 := by
  rw [ResidueTwoStaircase.Ffull_card hs]
  unfold score
  omega

theorem score_odd_gain {s : ℕ} (hs : 2 ≤ s) (he : s % 2 = 1) :
    score s = (Ffull (ResidueTwoStaircase.A s)).card := by
  rw [ResidueTwoStaircase.Ffull_card hs]
  unfold score
  omega

/-- Six-width gain is 37 above the linear term, not the target 38. -/
theorem score_step_two (s : ℕ) : score (s + 2) = score s + 12 * s + 37 := by
  have hd : (s + 2) / 2 = s / 2 + 1 := by omega
  simp only [score, hd]
  ring

theorem score_k_conversion {k : ℕ} (hk : 3 ≤ k) :
    score (k - 1) = 3 * k ^ 2 + 6 * k + 3 + (k - 1) / 2 := by
  unfold score
  have h : k - 1 + 1 = k := by omega
  nlinarith

theorem residueTwo_le_maxPreserved {k : ℕ} (hk : 3 ≤ k) :
    3 * k ^ 2 + 6 * k + 3 + (k - 1) / 2 ≤ maxPreserved (3 * k + 2) (3 * k + 2) := by
  have h := score_le_maxPreserved (s := k - 1) (by omega)
  rw [score_k_conversion hk] at h
  have hn : 3 * (k - 1) + 5 = 3 * k + 2 := by omega
  rwa [hn] at h

end
end GridGraphs.RailRepair
