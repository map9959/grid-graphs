import GridGraphs.ResidueTwoUpper.OneGap.FanSouthData
import GridGraphs.ResidueTwoUpper.OneGap.ShortKernelProof

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.South
open L7 FanSlab Short

def width (h : Nat) := 3*h/4+3
def sides (r c : Nat) : Option Bool := if min r c=1 then some false else
  if min r c=0 && max r c != 1 then some true else none
-- At a south-facing corner the last tile's column is 3, and the already
-- rooted line sends away from this corner at the middle of the input row.
def plantedAt (h r c : Nat) : Option Bool := if 3*h-2≤r && r≤3*h && 1≤c && c≤3*(width h) then some (c%3==0) else sides r c

def admit (h r c : Nat) (z : Label) := let m := z.1; let o := z.2
  adm (tag r) (tag c) m && ((List.finRange 9).all fun i => (plantedAt h (r+i.val/3) (c+i.val%3)).all fun b => lane m i==b.toNat) &&
  (if o=4 then m &&& 186==0 else decide (contact m o)) &&
  (r != 0 || (o==3)==decide (contact m 3)) && (c != 0 || (o==2)==decide (contact m 2)) &&
  (r != 3*h-2 || c != 2 || o==1)
private def raw (r c : Nat) := ((List.range 512).filter (adm r c)).flatMap fun m => (List.range 5).map fun o => (m,o)
private def table := Array.ofFn fun r : Fin 9 => Array.ofFn fun c : Fin 9 => raw r c
private def bank (r c : Nat) := (table[tag r]!)[tag c]!
def board (h : Nat) := build (3*h+1) fun r c => (bank r c).filter (admit h r c)
theorem member {h r c m o : Nat} (hr : r<3*h+1) (hc : c<3*h+1) (hm : m<512) (ho : o<5) (ok : admit h r c (m,o)) : (m,o)∈atRC (board h) r c := by
  have yes : adm (tag r) (tag c) m := by unfold admit at ok; simp only [Bool.and_eq_true] at ok; tauto
  have small (x : Nat) : tag x<9 := by unfold tag; split <;> omega
  rw [board,at_build hr hc]; apply List.mem_filter.mpr; refine ⟨?_,ok⟩
  simp [bank,table,small,raw,yes,hm,ho]

def run (h : Nat) := Kernel.run (3*h+1) 2 (Kernel.prune (3*h+1) 32 (board h))
theorem sound (h : Nat) (ok : run h) (X : Nat → Nat → Label) (agree : Agree (3*h+1) X) (kept : Kept (3*h+1) X (board h)) : False := kernel_excludes ok agree kept
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.South
