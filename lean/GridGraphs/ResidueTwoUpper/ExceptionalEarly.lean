import GridGraphs.ResidueTwoUpper.OnlyOneGap
import GridGraphs.ResidueTwoUpper.OneGap.Short35
import GridGraphs.ResidueTwoUpper.OneGap.Short77
import GridGraphs.ResidueTwoUpper.OneGap.Short119
import GridGraphs.Results.ResidueTwoLowerAll

namespace GridGraphs.ResidueTwoUpper.Exceptional

theorem exclude_early {u : Nat} (hu : u < 3) :
    ¬ SquareMaskScore (35+42*u) (440+1020*u+588*u^2) := by
  rintro ⟨F, hf, score⟩
  have acy := mem_acyclicForcedSets.mp hf
  have one := one_gap_of_exceptional_score F acy score
  interval_cases u
  · exact OneGap.Short.exclude35 F acy one score
  · exact OneGap.Short.exclude77 F acy one score
  · exact OneGap.Short.exclude119 F acy one score

theorem maxPreserved_119_119 : maxPreserved 119 119 = 4831 := by
  have upper := exclude_early (u:=2) (by decide)
  change ¬ SquareMaskScore 119 4832 at upper
  rw [squareMaskScore_iff_le (by decide)] at upper
  have lower := squareScore_lower_residue_two 39
  change 4831 ≤ maxPreserved 119 119 at lower
  omega

end GridGraphs.ResidueTwoUpper.Exceptional
