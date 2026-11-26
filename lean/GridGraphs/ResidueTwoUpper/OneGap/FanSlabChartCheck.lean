import GridGraphs.ResidueTwoUpper.OneGap.FanSlabData

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSlab
open ResidueZero Stencil L7

def small (t : Nat) := if t<8 then 1+t else 19+t
def inspect (w : View) (r t m : Nat) :=
  let a := 6+(1+r)%3; let b := small t
  let p := L7.view w 33 a b; let center := p+(1,1)
  !maskOK m || words[13*r+t]!.testBit (encode (Fin.ofNat 512 m) w) ||
    twoOrbitPatch 35 p m != 0 || (List.range 5).all fun o =>
      !starOK 35 center (bit m 4) (PatchFilter.cnb m) o || twoOrbitStar 35 center (bit m 4) (PatchFilter.cnb m) o != 0
theorem lookup : ∀ (w : View) (r : Fin 3) (t : Fin 13) (m : Fin 512), inspect w r t m := by native_decide

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSlab
