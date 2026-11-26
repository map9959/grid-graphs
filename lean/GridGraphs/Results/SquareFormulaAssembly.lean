import GridGraphs.Results.ResidueOneExact
import GridGraphs.Results.ResidueTwoLowerAll
import GridGraphs.Results.SmallDiagonalExact.Eleven
import GridGraphs.ResidueTwoUpper.Eight
import GridGraphs.ResidueTwoUpper.Remaining
import GridGraphs.ResidueZero.Exact

/-! Integration interface for the three independent residue proofs.
The conclusions refer to the physical spanning-tree maximum. -/
namespace GridGraphs
open PitchCut ResidueTwoLower

theorem exactSquareFormula_of_remaining_bounds
    (exceptional : ∀ u : Nat, ¬SquareMaskScore (35+42*u) (440+1020*u+588*u^2)) :
    ExactSquareFormula := by
  intro n hn
  by_cases small : n≤5
  · exact exactSquareFormula_through_five hn small
  let k := n/3
  have rem : n=3*k ∨ n=3*k+1 ∨ n=3*k+2 := by dsimp [k]; omega
  rcases rem with h|h|h <;> rw [h]
  · rw [squareScore_three_mul]; exact ResidueZero.maxPreserved_three_mul (by omega)
  · exact maxPreserved_residue_one k
  · by_cases eight : k=2
    · rw [eight]; exact ResidueTwoUpper.Eight.maximum_eq
    apply Nat.le_antisymm (ResidueTwoUpper.Stencil.upper_of_remaining maxPreserved_eleven_upper exceptional k (by omega))
    exact squareScore_lower_residue_two k

end GridGraphs
