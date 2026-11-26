import GridGraphs.ResidueTwoUpper.OneGap.SpeedCover

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short

private theorem rooted_repeat (k q f h t : Nat) (rooted : q<f)
    (height : 17 ≤ h ∧ h≤20)
    (width : f+3*t+3*h/4+3≤k) :
    Speed.Reaches k q (h+4*t,f) := by
  induction t generalizing f with
  | zero =>
    apply Speed.Reaches.capEnd
    simp only [Nat.mul_zero,Nat.add_zero,Speed.cap] at *
    omega
  | succ t ih =>
    have xeq : Speed.x Speed.root q f=f := by
      simp [Speed.x,Speed.root,Nat.max_eq_left (by omega : q+1≤f)]
    apply Speed.Reaches.via (m := Speed.root)
    · simp [Speed.moves]
    · unfold Speed.fits
      rw [show (h+4*(t+1),f).2=f by rfl,xeq]
      dsimp [Speed.root]
      refine ⟨by omega,fun h => Bool.noConfusion h,by omega⟩
    · unfold Speed.next
      rw [show (h+4*(t+1),f).2=f by rfl,xeq]
      dsimp [Speed.root]
      rw [show h+4*(t+1)-4=h+4*t by omega]
      exact ih (f+3) (by omega) (by omega)

/-- Pure arithmetic: a rooted suffix at row four can be moved to a cap
with 17–20 rows left, provided its initial starting column fits. -/
theorem short_schedule (k q f : Nat) (rooted : q<f) (room : 4*f≤k+3) (large : 21≤k) :
    Speed.Reaches k q (k-4,f) := by
  let t := (k-21)/4
  let h := k-4-4*t
  have sum : k-4=h+4*t := by dsimp [h,t]; omega
  have height : 17 ≤ h ∧ h≤20 := by dsimp [h,t]; omega
  have width : f+3*t+3*h/4+3≤k := by omega
  rw [sum]
  exact rooted_repeat k q f h t rooted height width

theorem short_seed_schedule (u q : Nat) (hu : 19≤u) (short : q<57) :
    Speed.Reaches (11+14*u) q (11+14*u-4,max 3 (q+1)+12) :=
  short_schedule _ _ _ (by omega) (by omega) (by omega)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
