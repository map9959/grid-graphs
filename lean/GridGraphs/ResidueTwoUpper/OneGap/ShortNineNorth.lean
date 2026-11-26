import GridGraphs.ResidueTwoUpper.OneGap.ShortCropFront

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
open ResidueZero Stencil L7 FanSlab FanBoot

/-- Starting at column six puts the isolate and columns 16–21 inside
the same 48-site window. -/
def nineTest (w : View) (A : Board) :=
  let G := Kernel.prune 48 15 (crop w 6 (planted 161 9 w A))
  (List.range 4).all fun j => (List.range 6).all fun i =>
    let t := target w (3*(j+1)+1) (3*(i+10)+1)
    (atRC G t.1 t.2).all fun z => encode (Fin.ofNat 512 z.1) w==73

@[noinline] private def viewsPass (A : Board) := decide (∀ w : View, nineTest w A)
theorem nine_checked : ∀ w : View, nineTest w (cached 3 chart) := by
  apply of_decide_eq_true
  change viewsPass (cached 3 chart)=true
  native_decide

theorem nine_front {F P w} (S : Seed (u:=3) F P w 9) (acy : (Bonds F).IsAcyclic) :
    Front F w 9 53 4 16 := by
  apply front_of_plateau S (by decide)
  intro j jl jh i il ih
  by_cases old : 22 ≤ i
  · exact plateau S acy (by decide) j jl jh i old ih
  · have ok := List.all_eq_true.mp (List.all_eq_true.mp (nine_checked w) (j-1)
        (List.mem_range.mpr (by omega))) (i-16) (List.mem_range.mpr (by omega))
    have m := crop_read S acy 6 15 _ _ 73 (by decide) (by omega) (by omega) ok
    simpa only [show 3*(j-1+1)+1=1+3*j by omega,
      show 3*6+(3*(i-16+10)+1)=1+3*i by omega] using m

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
