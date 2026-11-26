import GridGraphs.ResidueTwoUpper.OneGap.GuardedSchedules

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Guarded.Diagnosis
open SouthCap.Strip.GridScan

/-- Counterfactuals for the previous window sizes only. Search from the
same collision rows and stop at the same trimmed physical cap. -/
private def oldPath (k q : Nat) (width tips : Bool) : Nat → Nat → Nat → Bool
  | 0,h,f => decide (14≤h ∧ f-1+topWidth h≤k)
  | n+1,h,f => decide (14≤h ∧ f-1+topWidth h≤k) || [1,2,3,4,5,6,7].any fun a =>
      let W := 3*a+1; let D := 7*a+5
      let E := if a=7 then 27 else coneCost (D-1)
      decide (D+8≤h ∧ f+W+8≤k ∧ (tips=true → f+W≤q) ∧ (width=true → f+E+8≤k)) &&
        oldPath k q width tips n (h-(7*a-1)) (f+W)

private def old (u q : Nat) (width tips : Bool) :=
  let k := 11+14*u; let Y := (q-15)/6
  (List.range (CollisionWide.reach (q-6*Y)-1)).any fun j =>
    oldPath k q width tips (k/6) (k-(Y+(j+2))) (q-3*Y+3)

theorem constraint_check : [(4,57),(5,65),(5,67),(5,71),(5,73),(5,75),
    (6,89),(6,93),(7,107)].all (fun (u,q) =>
      !old u q true true && old u q false true &&
      (old u q true false == decide (u=5 ∧ (q=65 ∨ q=67))) &&
      Guarded.fits (11+14*u) q) := by native_decide
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Guarded.Diagnosis
