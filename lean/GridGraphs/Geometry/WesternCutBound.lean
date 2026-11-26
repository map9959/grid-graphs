import Mathlib

namespace GridGraphs.WesternCutBound

/-- After seven cuts west the suffix must have advanced; plateau capacity
counts the remaining bulk columns. At an arbitrary north isolate there
may additionally be two columns at start 1. -/
theorem position {i s j extra : Int}
    (advance : j ≤ s - 7) (capacity : i - 7 - 5 ≤ 3*(j-1) + extra) :
    i ≤ 3*s - 12 + extra := by omega

/-- Arithmetic application to the unadjusted diagonal interface. This
does not assert that an optimal tree contains the interface. -/
theorem diagonal_impossible (t : Int) (ht : 9 ≤ t) :
    let k := 39 + 14*t
    let groups := (k-12) / 16
    let i := k - 12*groups
    let s := k - 16*groups
    ¬ i ≤ 3*s - 12 := by
  dsimp
  have hr : t % 8 < 8 := Int.emod_lt_of_pos t (by decide)
  have hl : 0 ≤ t % 8 := Int.emod_nonneg t (by decide)
  interval_cases h : t % 8 <;> omega

/-- The six-unit cost and the exact whole-square deficit force many
bulk columns outside the opposing-arm case. -/
theorem missing_arms (t good : Nat) (budget : 6*good ≤ 198+72*t) :
    2*t-13 ≤ (39+14*t)-19-good := by omega

end GridGraphs.WesternCutBound
