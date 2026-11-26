import GridGraphs.ResidueTwoUpper.OneGap.FanHistory
import GridGraphs.ResidueTwoUpper.OneGap.SpeedCover

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSlab FanSeed BoundarySix.Connected

/-- Store actual vertical edges, including the one touching the particular
north foot. In particular the path to the cut lies entirely above it. -/
def RootLine {n} (F : Finset (GridVertex n n)) (w : View) (t Y : Nat) := ∀ r, r<1+3*Y →
  marked F (L7.view w n r (1+3*t:Nat)) || marked F (L7.view w n (r+1:Nat) (1+3*t:Nat))
def Seal {n} (F : Finset (GridVertex n n)) (w : View) (q t Y : Nat) :=
  let c : Int := 1+3*(t:Int); let d : Int := 1+3*(Y:Int)
  clear F w ((q:Int)-t+3) d c ∧ ∀ v∈F, (coordinates w v).1=d+1 → |(coordinates w v).2-c|≤1 → (coordinates w v).2=c

def Front {n} (F : Finset (GridVertex n n)) (w : View) (q k y f : Nat) :=
  Plateau F w y y f k ∧ (∀ t, f≤t → t< k → t≤q → Seal F w q t y) ∧ (∀ t, f≤t → t< k → q< t → RootLine F w t y)

private theorem right_mask (q j t : Nat) (h : q< t) (jpos : 1≤j) (hm : 6*j+2≤q) : history q j t=7 := by
  unfold history actual word; split_ifs <;> first | rfl | omega

private theorem marked_root {n q t j : Nat} (F : Finset (GridVertex n n)) (w : View)
    (lt : q< t) (hi : 1+3*t<n-1) (jm : 6*j+2≤q) (r : Nat) (rpos : 2≤r) (eq : j=(r-1)/3) (read : Read n q j F w) :
    marked F (L7.view w n r (1+3*t:Nat)) := by
  let b := (r-1)%3; have h := read t 0 b (by omega) (by decide) (by dsimp [b]; omega)
  rw [show 1+3*j+b=r by dsimp [b]; omega] at h
  by_cases z : j=0
  · rw [z] at h; have phase : b=1 ∨ b=2 := by dsimp [b]; omega
    rcases phase with a|a <;> simpa [a,history,seedWord,show t≠0 by omega,show ¬t+1<q by omega,show ¬t<q by omega,show t≠q by omega,lane] using h
  · rw [right_mask _ _ _ lt (by omega) jm] at h
    have tab : ∀ b : Fin 3, lane 7 b=1 := by decide
    simpa [tab ⟨b,by dsimp [b]; omega⟩] using h

theorem rooted_at_handoff {n q Y t : Nat} (F : Finset (GridVertex n n)) (w : View) (s f : Bool) (side : rim F w s f)
    (lt : q< t) (fit : 4+3*t<n) (big : 57≤q) (room : 6*Y+15≤q) (read : ∀ j≤Y+1, Read n q j F w) : RootLine F w t (Y+1) := by
  intro r hr
  by_cases base : r=0
  · subst r; apply Bool.or_eq_true_iff.mpr; left
    exact side 0 (1+3*t) (by omega) (by omega) true (by cases s <;> simp [preset,show t≠0 by omega,show 1+3*t≠2 by omega,show 1+3*t+2≠n by omega])
  · apply Bool.or_eq_true_iff.mpr; right
    exact marked_root F w lt (by omega) (by omega : 6*(r/3)+2≤q) _ (by omega) (by omega) (read _ (by omega))

private theorem extend_root {n q k t y e f : Nat} {F : Finset (GridVertex n n)} {w : View}
    (le : y≤e) (col : f≤t ∧ t< k) (pl : Plateau F w y e f k) (old : RootLine F w t y) : RootLine F w t e := by
  intro r hr; by_cases lo : r<1+3*y
  · exact old r lo
  apply Bool.or_eq_true_iff.mpr; left
  have z := plateau_bit (pl ((r-1)/3) (by omega) (by omega) t col.1 col.2) 0 ⟨(r-1)%3,by omega⟩
  change (marked F (L7.view w _ (1+3*((r-1)/3)+(r-1)%3:Nat) (1+3*t+0:Nat))).toNat=1 at z
  rw [show 1+3*((r-1)/3)+(r-1)%3=r by omega] at z; simpa using z

/-- Exact speed-window interface. The rectangle's surviving buffer may
be discarded after extending all histories through the new cut. -/
theorem advance_front {n q k y e f b g : Nat} (F : Finset (GridVertex n n)) (w : View)
    (le : y≤e) (lose : f≤g) (buf : b≤g) (safe : ∀ t, g≤t → t≤q → b< t ∧ (q:Int)-t+3≤1+3*(y:Int))
    (old : Front F w q k y f) (rect : Plateau F w y e b k) : Front F w q k e g := by
  refine ⟨fun j lo hi i st en => rect j (by omega) hi i (by omega) en,?_,?_⟩
  · intro t st en dang; obtain ⟨pad,birth⟩ := safe t st dang
    simpa only [Seal,show 1+3*(e:Int)+1=2+3*(e:Int) by ring] using plateau_transport F w y e b k t le ⟨pad,en⟩ rect _ birth (old.2.1 t (by omega) en dang).1
  · intro t st en root
    exact extend_root (q:=q) le ⟨by omega,en⟩ rect (old.2.2 t (by omega) en root)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
