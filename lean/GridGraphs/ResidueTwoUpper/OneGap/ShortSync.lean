import GridGraphs.ResidueTwoUpper.OneGap.ShortFold

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
/-! Synchronized shortening for the 4-row/3-column move. One block
removes 168 sites (four steps of the exceptional side progression).
The western column pad increases by nine each time the folded row
traverses a twelve-site loop. The eastern pad gets the remainder. -/
def syncBase (u : Nat) := if u<5 then u else 5+(u-5)%4
def pad (u : Nat) := 42*(u-syncBase u)
def ry := 72
def lx := 24
def ex := 180
def fold12 (d r : Nat) :=
  if r<ry then r else if r<ry+d+12 then ry+(r-ry)%12 else r-d
def westPad (d r : Nat) := 9*min ((r-ry)/12) (d/12)
def syncCol (d r c : Nat) :=
  let a := westPad d r
  foldAt ex (d-a) (foldAt lx a c)
def syncPos (u r c : Nat) := (fold12 (pad u) r,syncCol (pad u) r c)

theorem sync_sizes (u : Nat) :
    33+42*u=33+42*syncBase u+pad u ∧ pad u%168=0 ∧
    (pad u=0 ∨ 5 ≤ syncBase u ∧ syncBase u≤8) := by
  unfold pad syncBase; split <;> omega
theorem sync_room (u r c : Nat) (hr : r<33+42*u) (hc : c<33+42*u) :
    (syncPos u r c).1<33+42*syncBase u ∧ (syncPos u r c).2<33+42*syncBase u := by
  obtain ⟨width,phase,deep⟩ := sync_sizes u
  have A : westPad (pad u) r≤pad u := by unfold westPad; omega
  constructor
  · change fold12 (pad u) r<_; unfold fold12 ry; split_ifs <;> omega
  · change syncCol (pad u) r c<_; dsimp [syncCol,foldAt,lx,ex]; split_ifs <;> omega
theorem westPad_step (d r : Nat) : westPad d (r+1)=westPad d r ∨
    ((r+1-ry)%12=0 ∧ westPad d (r+1)=westPad d r+9 ∧
      fold12 d r=ry+11 ∧ fold12 d (r+1)=ry) := by
  unfold westPad fold12 ry; split_ifs <;> omega

theorem sync_phase (u r c : Nat) :
    (syncPos u r c).1%3=r%3 ∧ (syncPos u r c).2%3=c%3 := by
  obtain ⟨width,ph,deep⟩ := sync_sizes u
  have A : westPad (pad u) r≤pad u ∧ westPad (pad u) r%3=0 := by unfold westPad; omega
  constructor
  · change fold12 (pad u) r%3=_; unfold fold12 ry; split_ifs <;> omega
  · change syncCol (pad u) r c%3=_; dsimp [syncCol,foldAt,lx,ex]; split_ifs <;> omega

/-- Before the row insertion starts there is no western insertion;
in particular no short seed occurrence is moved across its isolate. -/
theorem sync_seed (u r c q : Nat) (short : q<57) :
    let t := syncPos u r c
    (t.1=1 ↔ r=1) ∧ (r=1 →
      (t.2<1+3*q ↔ c<1+3*q) ∧ (t.2=1+3*q ↔ c=1+3*q)) := by
  have H := sync_sizes u
  dsimp [syncPos]
  constructor
  · unfold fold12 ry; split_ifs <;> omega
  · rintro rfl
    have W : westPad (pad u) 1=0 := by simp [westPad,ry]
    have F : foldAt lx 0 c=c := by unfold foldAt; split_ifs <;> omega
    simp only [syncCol,W,F,Nat.sub_zero]; unfold foldAt ex; split_ifs <;> omega
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
