import GridGraphs.ResidueTwoUpper.OneGap.TranslatedNorth

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open L7

def grid (w : View) (A : Board) (d : Nat) :=
  Kernel.prune 48 15 (crop w 6 (planted 161 (6+d) w A))
def fixed73 (G : Board) (w : View) (j i : Nat) :=
  let t := target w (3*j+1) (3*i+1)
  (atRC G t.1 t.2).all fun z => encode (Fin.ofNat 512 z.1) w==73

/-- For each row, a *single* 73 at or west of the proposed suffix suffices:
`east_step` grows it to every later column in the same physical row. -/
def rays (G : Board) (w : View) (y b : Nat) :=
  (List.range (y-1)).all fun j => (List.range (b+1)).any fun i => fixed73 G w (j+2) i

def profile (d y e : Nat) : Prop :=
  (d=9 ∧ y=5 ∧ e=3) ∨ (d=12 ∧ y=5 ∧ e=1) ∨ (d=12 ∧ y=6 ∧ e=2)

private def checkView (w : View) (A : Board) :=
  let small := grid w A 3
  let wide := grid w A 12
  ((List.range 4).all fun a => fixed73 small w 1 (4+a)) &&
    rays (grid w A 9) w 5 12 && rays wide w 5 13 && rays wide w 6 14
@[noinline] private def checks (A : Board) := decide (∀ w : View, checkView w A)
private theorem checked : checks (cached 3 chart) := by native_decide

theorem first (w : View) (a : Nat) (ha : a<4) :
    fixed73 (grid w (cached 3 chart) 3) w 1 (4+a) := by
  have h := of_decide_eq_true checked w
  simp only [checkView,Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.1.1 _ (List.mem_range.mpr ha)

theorem starts (w : View) {d y e} (p : profile d y e) {j} (jl : 2≤j) (jh : j≤y) :
    ∃ i≤d+e, fixed73 (grid w (cached 3 chart) d) w j i := by
  have h := of_decide_eq_true checked w
  simp only [checkView,Bool.and_eq_true] at h
  have ready : rays (grid w (cached 3 chart) d) w y (d+e) := by
    rcases p with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
    · exact h.1.1.2
    · exact h.1.2
    · exact h.2
  obtain ⟨i,hi,ok⟩ := List.any_eq_true.mp (List.all_eq_true.mp ready (j-2) (List.mem_range.mpr (by omega)))
  exact ⟨i,by have := List.mem_range.mp hi; omega,by rwa [show j-2+2=j by omega] at ok⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
