import GridGraphs.ResidueTwoUpper.OneGap.FanBootRows

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSlab

def word (a d i : Nat) := if i<a then 448 else if i<a+3 then [384,264,24][i-a]!
  else if i<a+3+d then 56 else if i<a+6+d then [24,12,6][i-(a+3+d)]! else 7

def actual (q y i : Nat) := word (3*y-2) (q-6*y-2) i
set_option maxHeartbeats 2500000 in
private theorem fold_word (x b z c y : Nat) (hy : y≤2) :
    fan y (collapse x b z c/3)=word (16+3*y+x) (19-6*y+b) (c/3) := by
  have map' : ∀ y, y≤2 → ∀ i, fan y i=word (16+3*y) (19-6*y) i := by intros; rfl
  rw [map' _ hy]; unfold collapse
  interval_cases y <;> split_ifs <;> unfold word <;> split_ifs <;> first | rfl | omega | (congr 1 <;> omega)

def Known (u q y : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u))) (w : View) :=
  ∀ a<3, ∀ c<33+42*u, (marked F (L7.view w (35+42*u:Nat) (1+3*y+a:Nat) (1+c:Nat))).toNat=
    lane (actual q y (c/3)) (3*(c%3)+a)

private theorem third (u q y : Nat) (lo : 6≤y) (hm : 6*y+21≤q) (fits : q+2≤11+14*u)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p))
    (clean : ∀ a, patchSlack F a=0) (w : View)
    (zero : ∀ p, coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (prev : Known u q y F w) (next : Known u q (y+1) F w) : Known u q (y+2) F w := by
  let x := 3*y-18; let b := q-6*y-21; let z := 11+14*u-57-x-b
  have W : 11+14*u=57+x+b+z := by dsimp [x,b,z]; omega
  have rule (s c : Nat) (hs : s≤2) : fan s (collapse x b z c/3)=actual q (y+s) (c/3) := by
    rw [fold_word _ _ _ _ _ hs]; unfold actual; congr 1 <;> dsimp [x,b] <;> omega
  have out := physical_step u (1+3*y) x b z W (by omega) (by omega) (by omega) F acy P step clean w (by
    intro r hr c hc p hp; apply zero; rw [hp]; intro E
    cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [L7.view,reflect] at E <;> omega) (by
    intro r hr c hc; rw [rule _ _ (by omega)]
    by_cases small : r<3
    · simpa [show r/3=0 by omega,show r%3=r by omega] using prev r small c hc
    · have v := next (r-3) (by omega) c hc
      simpa only [show r/3=1 by omega,show r%3=r-3 by omega,show 1+3*(y+1)+(r-3)=1+3*y+r by omega] using v)
  intro a ha c hc
  let k := c/3; let i : Fin 9 := ⟨3*a+c%3,by omega⟩
  have h := out k (by dsimp [k]; omega)
  have extract := (unpack (fun t : Fin 9 => marked F (L7.view w (35+42*u:Nat) (1+3*y+6+t.val/3:Nat) (1+3*k+t.val%3:Nat)))).2 i
  change lane (square F w _ _) i=_ at extract
  rw [h,rule 2 _ (by decide)] at extract
  have small (a d i : Nat) : word a d i<512 := by
    have b1 : ∀ k : Fin 3, [384,264,24][k.val]!<512 := by decide
    have b2 : ∀ k : Fin 3, [24,12,6][k.val]!<512 := by decide
    unfold word; split_ifs <;> first | decide | exact b1 ⟨_,by omega⟩ | exact b2 ⟨_,by omega⟩
  have flip : ∀ m : Fin 512, ∀ i : Fin 9, lane (transpose m) i=lane m (3*(i.val%3)+i.val/3) := by native_decide
  have f := flip ⟨actual q (y+2) (3*k/3),small _ _ _⟩ i
  change lane (transpose (actual q (y+2) (3*k/3))) i=lane (actual q (y+2) (3*k/3)) _ at f
  rw [f] at extract
  have A : 1+3*y+6+i.val/3=1+3*(y+2)+a := by dsimp [i]; omega
  have B : 1+3*k+i.val%3=1+c := by dsimp [i,k]; omega
  rw [A,B] at extract
  simpa only [show 3*k/3=c/3 by dsimp [k]; omega,show 3*(i.val%3)+i.val/3=3*(c%3)+a by dsimp [i]; omega] using extract.symm

/-- Starting with the north seed, all fan rows through the two-row
handoff in the odd-speed argument are words of the *same marked set*. -/
theorem through_handoff (u q : Nat) (big : 57≤q) (fits : q+2≤11+14*u)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p))
    (clean : ∀ a,patchSlack F a=0) (w : View)
    (zero : ∀ p, coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (seed : Rows u q F w) : ∀ y, 6≤y → y≤(q-15)/6 → Known u q y F w ∧ Known u q (y+1) F w := by
  have base (y : Nat) (hy : y≤1) : Known u q (6+y) F w := by
    intro a ha c hc
    have e := seed (3*y+a) (by omega) c hc
    rw [show (3*y+a)/3=y by omega,fold_word _ _ _ _ _ (by omega)] at e
    unfold actual; simpa only [show 19+(3*y+a)=1+3*(6+y)+a by omega,show (3*y+a)%3=a by omega,
      show 16+3*y+0=3*(6+y)-2 by omega,show 19-6*y+(q-57)=q-6*(6+y)-2 by omega] using e
  intro y lo lim
  induction y,lo using Nat.le_induction with
  | base => exact ⟨base 0 (by decide),base 1 (by decide)⟩
  | succ y h ih =>
    obtain ⟨a,b⟩ := ih (by omega)
    exact ⟨b,third u q y h (by omega) fits F acy P step clean w zero a b⟩
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
