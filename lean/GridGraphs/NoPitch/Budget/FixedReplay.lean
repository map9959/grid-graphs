import GridGraphs.NoPitch.Budget.DecodedPaths19

namespace GridGraphs.NoPitch.Budget
open PitchCut Keys GridGraphs.NoPitch.Dual
attribute [local irreducible] chart19 chart58 chart61

def cleanKey (D : Chart) (m : Index) (key : Nat) :=
  !((locate D m key).any fun j => D.cols[j].fixed)
def checkClean (D : Chart) (k : Nat) :=
  let m := index D
  decide (∀ (x : Site k) (bits : Fin 4 → Bool) (f : Bool) (o : Option (Fin 4)),
    (o.isNone → oldBit x f bits → isJoint x) →
    cleanKey D m (8*starCode (N k) x.1.val x.2.val (sampled x bits) o+f.toNat))
def fixedStarOnly (D : Chart) := D.cols.all fun c => !c.fixed || c.key%8<2

theorem clean19 : checkClean chart19 6 := by native_decide
theorem clean58 : checkClean chart58 19 := by native_decide
theorem clean61 : checkClean chart61 20 := by native_decide
theorem fixed19 : fixedStarOnly chart19 := by native_decide
theorem fixed58 : fixedStarOnly chart58 := by native_decide
theorem fixed61 : fixedStarOnly chart61 := by native_decide

end GridGraphs.NoPitch.Budget
