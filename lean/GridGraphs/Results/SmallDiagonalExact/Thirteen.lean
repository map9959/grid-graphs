import GridGraphs.Results.SmallDiagonalExact.ThirteenAxes
import GridGraphs.Results.SmallDiagonalExact.ThirteenProfile
import GridGraphs.Results.CombLower

namespace GridGraphs

/-- The finite side-thirteen upper in the square-formula assembly interface. -/
theorem maxPreserved_thirteen_upper : maxPreserved 13 13 ≤ squareScore 13 := by
  classical
  rw [maxPreserved_eq_maxForcedAcyclic (by decide) (by decide)]
  unfold maxForcedAcyclic
  apply Finset.sup_le
  intro F hF
  have acy := mem_acyclicForcedSets.mp hF
  change F.card ≤ 68
  by_contra h
  obtain ⟨hc, he, hd, u, hu, hole⟩ := Thirteen.gap_profile F acy (by omega)
  exact Thirteen.three_axes_exclude_gap F acy hc he hd u hu hole

theorem maxPreserved_thirteen_thirteen : maxPreserved 13 13 = 68 :=
  Nat.le_antisymm maxPreserved_thirteen_upper (squareScore_lower_residue_one 4)

end GridGraphs
