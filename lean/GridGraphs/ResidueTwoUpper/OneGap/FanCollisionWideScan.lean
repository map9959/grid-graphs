import GridGraphs.ResidueTwoUpper.OneGap.FanShrink
import GridGraphs.ResidueTwoUpper.OneGap.FanHalo
import GridGraphs.ResidueTwoUpper.OneGap.ShortScan

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.CollisionWide
open L7 FanSlab Short Port.Halo

-- The 64 complete patch centers in each direction read 66 physical sites.
-- Only the aligned tiles in the two incoming rows are planted. The open
-- window stops three plateau tiles to the east of the first stripe tile.
def size := 64
def seeds (l j i : Nat) := transpose (actual (42+l) (7+j) (23+i))
def chart (l : Nat) : Board := build size fun r c =>
  ((List.range 512).filter fun m =>
    accepts (5+(r+1)%3) (5+(c+1)%3) m &&
       (r>3 || r%3 != 0 || c%3 != 0 || m==seeds l (r/3) (c/3))).flatMap fun m =>
    ((List.range 4).filter (active m)).map (m, ·)

abbrev board := chart 19
def output := Short.prune size 40 board

/-- Restrict the first eastern stripe column through the four missing rows. -/
theorem replay : ∀ j ∈ [2,3,4,5,6], (atRC output (3*j) 57).all fun z => z.1==73 := by
  native_decide

theorem forced (X : Nat → Nat → Label) (agree : Agree size X) (live : Kept size X board)
    (j : Nat) (lo : 2≤j) (hi : j≤6) : (X (3*j) 57).1=73 := by
  have hk : 3*j<size := by unfold size; omega
  have z := Short.prune_kept live agree 40 _ hk 57 (by decide)
  have hj : j∈[2,3,4,5,6] := by interval_cases j <;> decide
  exact beq_iff_eq.mp (List.all_eq_true.mp (replay j hj) _ z)

def member4 (m : Nat) := [3,7,9,73].contains m
private def fourTest (l : Nat) :=
  let G := Short.prune size 16 (chart l)
  (List.range 5).all fun z => (List.range 4).all fun b =>
    (atRC G (3*(z+2)) (3*(l-1+b))).all fun x => member4 x.1
private theorem fourChecks : [15,17,19].all fourTest=true := by native_decide

theorem four_read {l} (ok : l∈[15,17,19]) (X : Nat → Nat → Label) (agree : Agree size X)
    (live : Kept size X (chart l)) {z b : Nat} (zl : 2≤z) (zh : z≤6) (bh : b<4) :
    member4 (X (3*z) (3*(l-1+b))).1 := by
  have lim : l≤19 := by simp at ok; omega
  have p := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp fourChecks _ ok)
    (z-2) (List.mem_range.mpr (by omega))) b (List.mem_range.mpr bh)
  rw [show z-2+2=z by omega] at p
  exact List.all_eq_true.mp p _ (Short.prune_kept live agree 16 _ (by dsimp [size]; omega)
    _ (by dsimp [size]; omega))
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.CollisionWide
