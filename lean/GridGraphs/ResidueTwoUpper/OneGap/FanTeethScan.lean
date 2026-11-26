import GridGraphs.ResidueTwoUpper.OneGap.FanBootData
import GridGraphs.ResidueTwoUpper.OneGap.FanSweep

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Teeth
open L7 FanSweep FanSlab

/-- The preBox ends one tile beyond the first missing center; the very
last patch can be the physical isolate tile instead of a zero star. -/
def preBox (b : Nat) : Box := ⟨6,3*b+3,if b=4 then [6] else []⟩
def prefixOK (b r c m : Nat) :=
  let d := if c<5 then c else 5+(1+c)%3
  (accepts (rowTag r) d m || (3*b+2≤c && accepts (rowTag r) (8+(c-(3*b+2))) m) ||
    (r==0 && c==3*b+3 && m==64)) &&
    (r != 0 || c%3 != 0 || c>3*b || lane m 4==(decide (c<3*b)).toNat)
def preBase (b : Nat) := build (preBox b) fun r c => (List.range 512).filter (prefixOK b r c)
private theorem pre_test : ∀ b∈[2,3,4], check (preBox b) (fun G => (cell G 0 0).isEmpty) 14 (preBase b) := by native_decide

def sideBox : Box := ⟨6,30,[9]⟩
def sideOK (r c m : Nat) := accepts (rowTag r) (realTag 0 c) m &&
    (r != 0 || ((c != 0 && c != 3 && c != 6 && c != 9) || lane m 4==1) && (c != 30 || lane m 4==0))
def sideBase := build sideBox fun r c => (List.range 512).filter (sideOK r c)
private theorem side_test : check sideBox (fun G => (cell G 0 0).isEmpty) 30 sideBase := by native_decide

private theorem nope {B : Box} (T : Path B) {G : Grid} {k : Nat} (h : Kept T G)
    (test : check B (fun A => (cell A 0 0).isEmpty) k G) : False := by
  obtain ⟨A,e,ok⟩ := sound T _ k G h test
  have v := ok 0 (by omega) 0 (by omega)
  rw [T.start] at v
  simp only [List.isEmpty_iff] at e; simp [e] at v

theorem pre_false (b : Nat) (hb : b∈[2,3,4]) (T : Path (preBox b)) (init : Kept T (preBase b)) : False :=
  nope T init (pre_test b hb)
theorem side_false (T : Path sideBox) (init : Kept T sideBase) : False := nope T init side_test
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Teeth
