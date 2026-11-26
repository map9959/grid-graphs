import GridGraphs.ResidueTwoUpper.OneGap.FanCollisionWideScan

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.CollisionWide
open Short

def reach (l : Nat) := if l=15 then 8 else if l=17 then 7 else 10
theorem reach_bounds (l : Nat) : 6≤reach l ∧ reach l≤10 := by unfold reach; split_ifs <;> decide

private def testReach (l : Nat) :=
  let G := Short.prune size 40 (chart l)
  (List.range (reach l-1)).all fun j => (List.range 2).all fun b =>
    (atRC G (3*(j+2)) (3*(l-1+b))).all fun x => member4 x.1
private theorem checked : [15,17,19].all testReach := by native_decide

theorem reach_read {l} (ok : l∈[15,17,19]) (X : Nat → Nat → Label) (agree : Agree size X)
    (live : Kept size X (chart l)) {z b : Nat} (zl : 2≤z) (zh : z≤reach l) (bh : b<2) :
    member4 (X (3*z) (3*(l-1+b))).1 := by
  have lim : l≤19 := by simp at ok; omega
  have bound := reach_bounds l
  have p := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp checked _ ok)
    (z-2) (List.mem_range.mpr (by omega))) b (List.mem_range.mpr bh)
  rw [show z-2+2=z by omega] at p
  exact List.all_eq_true.mp p _ (Short.prune_kept live agree 40 _ (by dsimp [size]; omega)
    _ (by dsimp [size]; omega))
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.CollisionWide
