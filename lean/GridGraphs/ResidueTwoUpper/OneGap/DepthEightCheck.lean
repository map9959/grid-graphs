import GridGraphs.ResidueTwoUpper.OneGap.DepthSevenCheck

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open L7

private def rowEight (A : Board) (w : View) (d : Nat) :=
  let G := profileGrid A w 6 d
  (List.range (d+2)).any (bigFixed G w 8)
@[noinline] private def checks (A : Board) :=
  decide (∀ w : View, (rowEight A w 21 || rowEight A w 22)=true)
private theorem checked : checks (cached 3 chart) := by native_decide

theorem eight_new_row (w : View) : ∃ d b, (d=21 ∨ d=22) ∧ b≤d+1 ∧
    bigFixed (profileGrid (cached 3 chart) w 6 d) w 8 b := by
  rcases Bool.or_eq_true_iff.mp (of_decide_eq_true checked w) with l|r
  · obtain ⟨b,h,m⟩ := List.any_eq_true.mp l
    exact ⟨21,b,.inl rfl,by have := List.mem_range.mp h; omega,m⟩
  · obtain ⟨b,h,m⟩ := List.any_eq_true.mp r
    exact ⟨22,b,.inr rfl,by have := List.mem_range.mp h; omega,m⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
