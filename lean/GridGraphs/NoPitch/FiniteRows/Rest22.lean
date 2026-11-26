import GridGraphs.NoPitch.FiniteRows.Assembly
import GridGraphs.NoPitch.FiniteRows.Book22
namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Budget GridGraphs.NoPitch.Dual TailRows
attribute [local irreducible] chart22
def scheme22 : Scheme := ⟨inc22,fl22⟩
theorem columnChecks22 : checkClean chart22 7 ∧ fixedStarOnly chart22 ∧ checkCorner chart22 22 ∧ residualOK chart22 := by native_decide
theorem partition22 : partitionOK chart22 scheme22 (supportMasks chart22) := by native_decide
theorem norm22 : normCheck chart22 7 inc22.start := by native_decide
theorem flow22 : certified chart22 7 (byTag (supportMasks chart22) 8) := by native_decide
theorem letters22 : certLetters chart22 7 (byTag (supportMasks chart22) 9) := by native_decide
end GridGraphs.NoPitch.FiniteRows
