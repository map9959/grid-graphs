import GridGraphs.ResidueTwoUpper.OneGap.DepthSixCheck

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep.Wide
open L7

def axis (n k v : Nat) (far : Bool) (i : Nat) :=
  (if far then 3*k-n-3*v else 3*v)+i
def loc (n k v : Nat) (w : View) (r c : Nat) :=
  (axis n k (if w.swap then v else 0) w.rowFar r,
   axis n k (if w.swap then 0 else v) w.colFar c)
def target (n : Nat) (w : View) (r c : Nat) :=
  (if w.rowFar then n-1-(if w.swap then c else r) else if w.swap then c else r,
   if w.colFar then n-1-(if w.swap then r else c) else if w.swap then r else c)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep.Wide
