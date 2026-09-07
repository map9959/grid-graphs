import GridGraphs.Accounting.BoundaryFive.CornerPacket.Upper
import GridGraphs.Accounting.BoundaryFive.Rootless.AmbientEndpoint
import GridGraphs.Accounting.BoundarySix.Connected.Upper

/-! # Global upper refinement after excluding the three endpoint profiles

The low-boundary exclusions remove the old endpoint when k = 1 modulo 3.
In the other two parameter classes the old and new floor bounds coincide.
This is an unconditional improvement, not the sharp stable target.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- Every feasible stable residue-two set obeys the refined endpoint bound. -/
theorem forced_card_le_endpoint_refinement {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic) :
    F.card ≤ 3 * k ^ 2 + 7 * k + (2 * k) / 3 := by
  have hupper := BoundaryFive.forced_card_le_residueTwo_bound hk F hacyc
  by_cases hmod : k % 3 = 1
  · by_contra h
    have hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card := by omega
    obtain ⟨hcard, hcases⟩ :=
      BoundaryFive.CornerPacket.current_upper_endpoint_two_profiles hk hmod F hacyc hf
    rcases hcases with ⟨hr, hc, hb⟩ | ⟨_, _, hb⟩
    · exact BoundaryFive.Rootless.boundary_five_two_component_endpoint_false
        hk hmod F hacyc hb hc hr hcard
    · exact BoundarySix.Connected.boundary_six_current_endpoint_false hk hmod F hacyc hb hf
  · have hcases : k % 3 = 0 ∨ k % 3 = 2 := by omega
    rcases hcases with hzero | htwo <;> omega

/-- Unconditional upper bound for every stable residue-two square. -/
theorem maxPreserved_residueTwo_le_endpoint_refinement {k : Nat} (hk : 5 ≤ k) :
    maxPreserved (3 * k + 2) (3 * k + 2) ≤
      3 * k ^ 2 + 7 * k + (2 * k) / 3 := by
  classical
  rw [maxPreserved_eq_maxForcedAcyclic (by omega) (by omega)]
  unfold maxForcedAcyclic
  apply Finset.sup_le
  intro F hF
  exact forced_card_le_endpoint_refinement hk F (mem_acyclicForcedSets.mp hF)

end GridGraphs
