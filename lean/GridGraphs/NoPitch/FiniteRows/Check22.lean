import GridGraphs.NoPitch.FiniteRows.Book22
import GridGraphs.NoPitch.FiniteRows.FastIncidence
namespace GridGraphs.NoPitch.FiniteRows
open TailRows GridGraphs.NoPitch.Dual
attribute [local irreducible] chart22
theorem fp22 : FacePatch.cert chart22 7 := FacePatch.fast_sound _ _ (by native_decide)
theorem faceLine22 : FaceLine.cert chart22 fl22 7 := by native_decide
theorem incidence22 : Incidence.cert chart22 inc22 7 := Fast.sound _ _ _ (by native_decide)
end GridGraphs.NoPitch.FiniteRows
