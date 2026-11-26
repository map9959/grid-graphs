import GridGraphs.ResidueTwoUpper.OneGap.FanBootData
import GridGraphs.ResidueTwoUpper.OneGap.FanSweep
import GridGraphs.ResidueTwoUpper.OneGap.FanStep
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSlab FanSweep

-- h is the base eastern margin (2,4,6,8); in the last chart the
-- east can be extended as well. Each loop is strictly in a plateau.
def box (h : Nat) : Box := ⟨27,3*(57+h)-3,if h=8 then [81,180] else [81]⟩
def colTag (h c : Nat) := if c<5 then c else if (box h).cols-4≤c then 8+(c-((box h).cols-4)) else 5+(c+1)%3
def startOK (r c m : Nat) := if r==0 && c%3==0 then
  if c<171 then lane m 4==1 else m==(if c=171 then 64 else 72) else true
def base (h : Nat) := build (box h) fun r c => (List.range 512).filter fun m =>
  ((r==0 && c==171) || accepts (rowTag r) (colTag h c) m) && startOK r c m
-- Base word with (a,c,r)=(16,19,16+h) and its next row.
def goal (h : Nat) (G : Grid) := (List.range 2).all fun y => (List.range (57+h)).all fun k =>
  (cell G (18+3*y) (3*k)).all fun m => m==transpose (fan y k)
private theorem checked : ∀ h∈[2,4,6,8], check (box h) (goal h) 32 (base h) := by native_decide

theorem output (h : Nat) (hh : h∈[2,4,6,8]) (T : Path (box h)) (init : Kept T (base h))
    (j y k : Nat) (hj : j≤T.last) (hy : y<2) (hk : k<57+h) (label : T.col j=3*k) :
    T.M (18+3*y) j=transpose (fan y k) := by
  obtain ⟨G,end',live⟩ := sound T (goal h) 32 _ init (checked h hh)
  have z := live (18+3*y) (by change 18+3*y≤27; omega) j hj
  rw [label] at z
  exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp end' y (List.mem_range.mpr hy)) k (List.mem_range.mpr hk)) _ z)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
