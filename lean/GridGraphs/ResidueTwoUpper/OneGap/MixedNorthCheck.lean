import GridGraphs.ResidueTwoUpper.OneGap.ShortNineNorth

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
open L7

def mixedTest (w : View) (A : Board) :=
  let G := Kernel.prune 48 15 (crop w 6 (planted 161 9 w A))
  (List.range 4).all fun j => (List.range 8).all fun i =>
    let t := target w (3*(j+1)+1) (3*(i+8)+1)
    (atRC G t.1 t.2).all fun z =>
      let m := encode (Fin.ofNat 512 z.1) w
      m==73 || (j==3 && i==0 && m==9)

@[noinline] private def viewsPass (A : Board) := decide (∀ w : View, mixedTest w A)
theorem mixed_checked : ∀ w : View, mixedTest w (cached 3 chart) := by
  apply of_decide_eq_true
  change viewsPass (cached 3 chart)=true
  native_decide

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
