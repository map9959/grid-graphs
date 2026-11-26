import GridGraphs.ResidueTwoUpper.OneGap.DepthEightCheck

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open L7

def axisWide (n k v : Nat) (far : Bool) (i : Nat) :=
  (if far then 3*k-n-3*v else 3*v)+i
def locWide (n k v : Nat) (w : View) (r c : Nat) :=
  (axisWide n k (if w.swap then v else 0) w.rowFar r,
   axisWide n k (if w.swap then 0 else v) w.colFar c)
def targetWide (n : Nat) (w : View) (r c : Nat) :=
  (if w.rowFar then n-1-(if w.swap then c else r) else if w.swap then c else r,
   if w.colFar then n-1-(if w.swap then r else c) else if w.swap then r else c)
def wideGrid (A : Board) (w : View) (n s d : Nat) :=
  let B := planted 161 (s+d) w A
  Kernel.prune n 18 (build n fun r c => let a := locWide n 53 s w r c; atRC B a.1 a.2)
def wideFixed (n : Nat) (G : Board) (w : View) (j i : Nat) :=
  let t := targetWide n w (3*j+1) (3*i+1)
  (atRC G t.1 t.2).all fun z => encode (Fin.ofNat 512 z.1) w==73

private def ninth (A : Board) (w : View) (d : Nat) :=
  let G := wideGrid A w 96 6 d
  (List.range (d+2)).any (wideFixed 96 G w 9)
private def trial (A : Board) (w : View) :=
  (ninth A w 25 || ninth A w 26 || ninth A w 24) &&
  (let G := profileGrid A w 0 19
   (List.range 8).all fun j => (List.range 19).any fun i => bigFixed G w (j+2) (i+2))
@[noinline] private def checks (A : Board) := decide (∀ w : View, trial A w)
private theorem checked : checks (cached 3 chart) := by native_decide

theorem nine_interior (w : View) : ∃ d b, 24≤d ∧ d≤26 ∧ b≤d+1 ∧
    wideFixed 96 (wideGrid (cached 3 chart) w 96 6 d) w 9 b := by
  have h := (Bool.and_eq_true_iff.mp (of_decide_eq_true checked w)).1
  simp only [Bool.or_eq_true] at h
  rcases h with (h|h)|h <;> obtain ⟨b,bh,m⟩ := List.any_eq_true.mp h <;>
    exact ⟨_,b,by decide,by decide,by have := List.mem_range.mp bh; omega,m⟩

theorem nine_wall (w : View) {j} (lo : 2≤j) (hi : j≤9) :
    ∃ b, 2≤b ∧ b≤20 ∧ bigFixed (profileGrid (cached 3 chart) w 0 19) w j b := by
  have h := (Bool.and_eq_true_iff.mp (of_decide_eq_true checked w)).2
  obtain ⟨b,bh,m⟩ := List.any_eq_true.mp (List.all_eq_true.mp h (j-2) (List.mem_range.mpr (by omega)))
  exact ⟨b+2,by omega,by have := List.mem_range.mp bh; omega,by rwa [show j-2+2=j by omega] at m⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
