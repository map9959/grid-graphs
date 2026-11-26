import GridGraphs.FiniteOne.Exact
import GridGraphs.FiniteOne.FortyThree
import GridGraphs.Results.ResidueOneTailExact
import GridGraphs.Results.SmallDiagonalExact.Thirteen
import GridGraphs.Results.SmallDiagonalExact.Nineteen
import GridGraphs.NoPitch.FiniteRows.Exact22
import GridGraphs.NoPitch.FiniteRows.Exact25
import GridGraphs.NoPitch.FiniteRows.Exact52

namespace GridGraphs
open PitchCut

/-- The ten remaining finite cases, independent of any no-pitch assumption. -/
theorem finite_one_last {k : Nat} (lo : 5≤k) (hi : k<19) (not52 : k≠17) (owned : k=5 ∨ 9≤k) :
    maxPreserved (3*k+1) (3*k+1)=squareScore (3*k+1) := by
  have cases : k=5 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 ∨ k=16 ∨ k=18 := by omega
  rcases cases with e|e|e|e|e|e|e|e|e|e <;> subst k
  exacts [FiniteOne.exact16,FiniteOne.exact28,FiniteOne.exact31,FiniteOne.exact34,FiniteOne.exact37,
    FiniteOne.exact40,FiniteOne.exact43,FiniteOne.exact46,FiniteOne.exact49,FiniteOne.exact55]

/-- All positive residue-one sides, including the exceptional small boards. -/
theorem maxPreserved_residue_one (k : Nat) :
    maxPreserved (3*k+1) (3*k+1)=squareScore (3*k+1) := by
  by_cases tail : 19≤k
  · exact maxPreserved_residue_one_tail tail
  by_cases small : k≤8
  · interval_cases k
    exacts [exactSquareFormula_through_five (by decide) (by decide),
      exactSquareFormula_through_five (by decide) (by decide),exactSquareFormula_seven,exactSquareFormula_ten,
      le_antisymm maxPreserved_thirteen_upper (squareScore_lower_residue_one 4),FiniteOne.exact16,
      maxPreserved_nineteen_nineteen,maxPreserved_22_22,maxPreserved_25_25]
  by_cases e : k=17
  · subst k; exact maxPreserved_52_52
  exact finite_one_last (by omega) (by omega) e (by omega)

end GridGraphs
