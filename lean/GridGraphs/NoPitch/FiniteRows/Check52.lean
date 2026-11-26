import GridGraphs.NoPitch.FiniteRows.Book52
import GridGraphs.NoPitch.FiniteRows.FastIncidence
namespace GridGraphs.NoPitch.FiniteRows
open TailRows GridGraphs.NoPitch.Dual
attribute [local irreducible] chart52
theorem fp52 : FacePatch.cert chart52 17 := FacePatch.fast_sound _ _ (by native_decide)
theorem faceLine52 : FaceLine.cert chart52 fl52 17 := by native_decide
theorem incidence52 : Incidence.cert chart52 inc52 17 := Fast.sound _ _ _ (by native_decide)
end GridGraphs.NoPitch.FiniteRows
