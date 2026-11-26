import GridGraphs.ResidueTwoUpper.OneGap.DeepNorthCheck

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open L7

def axis72 (k v : Nat) (far : Bool) (i : Nat) :=
  (if far then 3*k-72-3*v else 3*v)+i
def loc72 (k v : Nat) (w : View) (r c : Nat) :=
  (axis72 k (if w.swap then v else 0) w.rowFar r,
   axis72 k (if w.swap then 0 else v) w.colFar c)
def target72 (w : View) (r c : Nat) :=
  (if w.rowFar then 71-(if w.swap then c else r) else if w.swap then c else r,
   if w.colFar then 71-(if w.swap then r else c) else if w.swap then r else c)
def bigGrid (A : Board) (w : View) :=
  let B := planted 161 24 w A
  Kernel.prune 72 18 (build 72 fun r c => let a := loc72 53 6 w r c; atRC B a.1 a.2)
def bigFixed (G : Board) (w : View) (j i : Nat) :=
  let t := target72 w (3*j+1) (3*i+1)
  (atRC G t.1 t.2).all fun z => encode (Fin.ofNat 512 z.1) w==73
private def trial (A : Board) (w : View) :=
  let G := bigGrid A w
  (List.range 5).all fun j => (List.range 20).any fun i => bigFixed G w (j+2) i
@[noinline] private def allTrials (A : Board) := decide (∀ w : View, trial A w)
private theorem ready : allTrials (cached 3 chart) := by native_decide

theorem six_rays (w : View) {j : Nat} (lo : 2≤j) (hi : j≤6) :
    ∃ b<20, bigFixed (bigGrid (cached 3 chart) w) w j b := by
  have yes := List.all_eq_true.mp (of_decide_eq_true ready w) (j-2) (List.mem_range.mpr (by omega))
  obtain ⟨b,h,m⟩ := List.any_eq_true.mp yes
  exact ⟨b,List.mem_range.mp h,by rwa [show j-2+2=j by omega] at m⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
