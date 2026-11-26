import GridGraphs.ResidueTwoUpper.OneGap.ShortBoard
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open L7
@[noinline] def sites35 (A : Board) :=
  decide (∀ (q : Fin 5) (w : View), reject 33 (planted 35 (2*q.val+1) w A) 100)
theorem replay35 : sites35 (localBoard 35) := by native_decide
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
