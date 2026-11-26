import GridGraphs.ResidueTwoUpper.OneGap.ShortFiveNorth

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
open ResidueZero Stencil L7 FanSlab FanBoot

def sevenTest (w : View) (A : Board) :=
  let G := Kernel.prune 48 15 (crop w 4 (planted 161 7 w A))
  (List.range 4).all fun j => (List.range 4).all fun i =>
    let t := target w (3*(j+1)+1) (3*(i+12)+1)
    (atRC G t.1 t.2).all fun z => encode (Fin.ofNat 512 z.1) w==73

@[noinline] private def viewsPass (A : Board) := decide (∀ w : View, sevenTest w A)
theorem seven_checked : ∀ w : View, sevenTest w (cached 3 chart) := by
  apply of_decide_eq_true
  change viewsPass (cached 3 chart)=true
  native_decide

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
