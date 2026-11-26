import GridGraphs.NoPitch.FiniteRows.FastNormalization
import GridGraphs.NoPitch.FiniteRows.Assembly
import GridGraphs.NoPitch.FiniteRows.Book25
namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Budget GridGraphs.NoPitch.Dual TailRows
attribute [local irreducible] chart25
def scheme25 : Scheme := ⟨inc25,fl25⟩
theorem columnChecks25 : checkClean chart25 8 ∧ fixedStarOnly chart25 ∧ checkCorner chart25 25 ∧ residualOK chart25 := by native_decide
theorem partition25 : partitionOK chart25 scheme25 (supportMasks chart25) := by native_decide
theorem norm25 : normCheck chart25 8 inc25.start := Fast.norm_sound _ _ _ (by native_decide)
theorem flow25 : certified chart25 8 (byTag (supportMasks chart25) 8) := by native_decide
theorem letters25 : certLetters chart25 8 (byTag (supportMasks chart25) 9) := by native_decide
end GridGraphs.NoPitch.FiniteRows
