import GridGraphs.ResidueTwoUpper.OneGap.DepthSixCheck

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open L7

def profileGrid (A : Board) (w : View) (v d : Nat) :=
  let B := planted 161 (v+d) w A
  Kernel.prune 72 18 (build 72 fun r c => let a := loc72 53 v w r c; atRC B a.1 a.2)

private def trial (A : Board) (w : View) :=
  (List.range 20).any (bigFixed (bigGrid A w) w 7) &&
    (let G := profileGrid A w 0 17
     (List.range 6).all fun j => (List.range 17).any fun b => bigFixed G w (j+2) (b+2))
@[noinline] private def checks (A : Board) := decide (∀ w : View, trial A w)
private theorem checked : checks (cached 3 chart) := by native_decide

theorem seven_interior (w : View) {j} (lo : 2≤j) (hi : j≤7) :
    ∃ b<20, bigFixed (profileGrid (cached 3 chart) w 6 18) w j b := by
  by_cases old : j≤6
  · exact six_rays w lo old
  · obtain ⟨b,hb,m⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp (of_decide_eq_true checked w)).1
    exact ⟨b,List.mem_range.mp hb,by rwa [show j=7 by omega]⟩

theorem seven_wall (w : View) {j} (lo : 2≤j) (hi : j≤7) :
    ∃ b, 2≤b ∧ b≤18 ∧ bigFixed (profileGrid (cached 3 chart) w 0 17) w j b := by
  have a := (Bool.and_eq_true_iff.mp (of_decide_eq_true checked w)).2
  have hit := List.all_eq_true.mp a (j-2) (List.mem_range.mpr (by omega))
  obtain ⟨b,hb,m⟩ := List.any_eq_true.mp hit
  exact ⟨b+2,by omega,by have := List.mem_range.mp hb; omega,by rwa [show j-2+2=j by omega] at m⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
