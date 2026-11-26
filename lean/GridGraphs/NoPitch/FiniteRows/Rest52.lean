import GridGraphs.NoPitch.FiniteRows.FastNormalization
import GridGraphs.NoPitch.FiniteRows.Assembly
import GridGraphs.NoPitch.FiniteRows.Book52
namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Budget GridGraphs.NoPitch.Dual TailRows
attribute [local irreducible] chart52
def scheme52 : Scheme := ⟨inc52,fl52⟩
theorem columnChecks52 : checkClean chart52 17 ∧ fixedStarOnly chart52 ∧ checkCorner chart52 52 ∧ residualOK chart52 := by native_decide
theorem partition52 : partitionOK chart52 scheme52 (supportMasks chart52) := by native_decide
theorem norm52 : normCheck chart52 17 inc52.start := Fast.norm_sound _ _ _ (by native_decide)
theorem flow52 : certified chart52 17 (byTag (supportMasks chart52) 8) := by native_decide
theorem letters52 : certLetters chart52 17 (byTag (supportMasks chart52) 9) := by native_decide
end GridGraphs.NoPitch.FiniteRows
