import GridGraphs.ResidueTwoUpper.OneGap.DefectSites
import GridGraphs.ResidueTwoUpper.OneGap.SpeedCover

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap

/-- Measured from the coordinate-zero end of its side, the phase-five
isolate is at `2+3q` with odd `q`. The last possible site is `n-6`.
On sides at least 623 this lands either in the small-index cases or in
the proved odd-speed arithmetic cover. -/
theorem index_of_arm (t : Nat) (a ell : Nat) (loc : arm (623+42*(t:Int)) a ell) :
    ∃ q : Nat, ell=2+3*q ∧ q%2=1 ∧ q+2≤207+14*t ∧
      (q≤55 ∨ Speed.Reaches (207+14*t) q (Speed.start (207+14*t) q)) := by
  let q := (ell-2)/3
  unfold arm at loc
  have eq : ell=2+3*q := by dsimp [q]; omega
  have odd : q%2=1 := by omega
  have hi : q+2≤207+14*t := by omega
  exact ⟨q,eq,odd,hi,by
    by_cases small : q≤55
    · exact Or.inl small
    · exact Or.inr (Speed.cover t q (by omega) hi odd)⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
