import GridGraphs.Accounting.BoundaryFive.Symmetry
import GridGraphs.Accounting.BoundaryFive.TopSingleton

/-! # Unconditional residue-two upper bound from the boundary-five singleton

The old endpoint profile supplies boundary deficiency five. A square symmetry
positions only the unique gap, preserving size and feasibility. The oriented
singleton then excludes that endpoint, saving one when `k = 2 mod 3`.
-/

namespace GridGraphs.BoundaryFive

open Finset SimpleGraph

/-- No feasible set reaches the old global endpoint when `k = 2 mod 3`.
There is no boundary-budget, connectivity, or normalization hypothesis. -/
theorem old_upper_endpoint_false {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 2)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 2) / 3 ≤ F.card) : False := by
  have hb := (CarrierLayers.residueTwo_old_upper_endpoint_profile hk hmod F hacyc hf).2.2.2
  obtain ⟨F', hcard, hac, ha, hb'⟩ := exists_top_gap_pullback (by omega) F hacyc hb
  exact top_gap_old_upper_endpoint_false hk hmod F' hac (by rw [hcard]; exact hf) ha hb'

/-- Every feasible residue-two square set satisfies the improved bound,
for all `k >= 5` and all boundary budgets. -/
theorem forced_card_le_residueTwo_bound {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) :
    F.card ≤ 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 := by
  have hupper := forced_card_le_boundary_six_residueTwo_bound hk F hacyc
  by_cases hmod : k % 3 = 2
  · by_contra h
    exact old_upper_endpoint_false hk hmod F hacyc (by omega)
  · have hcases : k % 3 = 0 ∨ k % 3 = 1 := by omega
    rcases hcases with hzero | hone <;> omega

/-- Unconditional improved square-grid maximum for every `k >= 5`. -/
theorem maxPreserved_residueTwo_le {k : Nat} (hk : 5 ≤ k) :
    maxPreserved (3 * k + 2) (3 * k + 2) ≤
      3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 := by
  classical
  rw [maxPreserved_eq_maxForcedAcyclic (by omega) (by omega)]
  unfold maxForcedAcyclic
  apply Finset.sup_le
  intro F hF
  exact forced_card_le_residueTwo_bound hk F (mem_acyclicForcedSets.mp hF)

end GridGraphs.BoundaryFive
