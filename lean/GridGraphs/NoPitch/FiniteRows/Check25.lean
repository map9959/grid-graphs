import GridGraphs.NoPitch.FiniteRows.Book25
import GridGraphs.NoPitch.FiniteRows.FastIncidence
namespace GridGraphs.NoPitch.FiniteRows
open TailRows GridGraphs.NoPitch.Dual
attribute [local irreducible] chart25
theorem fp25 : FacePatch.cert chart25 8 := FacePatch.fast_sound _ _ (by native_decide)
theorem faceLine25 : FaceLine.cert chart25 fl25 8 := by native_decide
theorem incidence25 : Incidence.cert chart25 inc25 8 := Fast.sound _ _ _ (by native_decide)
end GridGraphs.NoPitch.FiniteRows
