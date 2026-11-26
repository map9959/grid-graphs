import Mathlib

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap

abbrev Word := Nat × Nat × Nat × Nat

/-- Additional row-major plaquettes for the other closed SE corner.
The two indices are row tag and column tag (in that order). A row of
the base catalogue uses the producer's NW, NE, SW, SE ordering. -/
def extra (r c : Nat) : List Word :=
  if (r,c)=(10,11) then
    [(6,48,6,33),(6,48,7,33),(7,48,7,33),(16,48,7,33),
     (288,128,292,32),(292,128,292,32),(384,192,288,32),(448,192,288,32)]
  else if (r,c)=(10,12) then
    [(48,24,33,24),(128,24,32,24),(192,24,32,24)]
  else []

def widened (bank : Nat → Nat → Word → Prop) (r c : Nat) (w : Word) : Prop :=
  bank r c w ∨ w∈extra r c

theorem extra_count :
    ((List.range 7).flatMap fun r => (List.range 7).flatMap fun c => extra (r+6) (c+6)).length=11 := by decide

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
