import GridGraphs.ResidueTwoUpper.OneGap.FanEast

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open L7 FanSlab FanSweep FanSeed ResidueZero Stencil

private def B : Box := ⟨11,45,[]⟩
private def localWord (j i : Nat) := if i<9-3*j then 56 else if i<12-3*j then [24,12,6][i-(9-3*j)]! else 7
private def start := build B fun r c => (List.range 512).filter fun m =>
  accepts (5+(r+1)%3) (5+(c+1)%3) m && (r%3 != 0 || r>3 || c%3 != 0 || m==transpose (localWord (r/3) (c/3)))
private def collisionGoal (G : Grid) := (cell G 6 36).all (· == 73)
private theorem replay : check B collisionGoal 20 start := by native_decide

theorem align {n} (F : Finset (GridVertex n n)) (w : View) (j i m : Nat) (hm : m<512)
    (h : ∀ a b : Fin 3, (marked F (L7.view w n (1+3*j+b.val:Nat) (1+3*i+a.val:Nat))).toNat=lane m (3*a.val+b.val)) :
    square F w (1+3*j) (1+3*i)=transpose m := by
  have tab : ∀ m : Fin 512, bits (fun t : Fin 9 => decide (lane m (3*(t.val%3)+t.val/3)=1))=transpose m := by native_decide
  apply Eq.trans _ (tab ⟨m,hm⟩); unfold square; apply congrArg bits; funext t
  have e := h ⟨t.val%3,by omega⟩ ⟨t.val/3,by have := t.isLt; omega⟩
  change (marked F _).toNat=lane m (3*(t.val%3)+t.val/3) at e
  rw [←e]; cases marked F _ <;> rfl

/-- The first new row after the two-row odd-fan handoff. A physical
16-tile rectangle with open sides suffices regardless of the center parity. -/
theorem first_collision (u q Y : Nat) (hy : 6≤Y) (room : 6*Y+15≤q ∧ q≤6*Y+20) (fit : q+2≤11+14*u)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (k0 : Known u q Y F w) (k1 : Known u q (Y+1) F w) : Plateau F w (Y+1) (Y+2) (q-3*Y+2) (11+14*u) := by
  let left := q-3*Y-10
  let M (r c : Nat) := square F w (1+3*Y+r) (1+3*left+c)
  have rel (s i : Nat) (hs : s≤1) : actual q (Y+s) (left+i)=localWord s i := by
    unfold actual word left localWord; split_ifs <;> first | rfl | omega | (congr 1 <;> omega)
  have aligned (s i : Nat) (hs : s≤1) (hi : i≤15) : M (3*s) (3*i)=transpose (localWord s i) := by
    have kn : Known u q (Y+s) F w := by interval_cases s <;> assumption
    have h := align F w (Y+s) (left+i) (actual q (Y+s) (left+i)) (by
      rw [rel _ _ hs]; have tt : ∀ s : Fin 2, ∀ i : Fin 16, localWord s i<512 := by native_decide
      exact tt ⟨_,by omega⟩ ⟨_,by omega⟩) (by
      intro a b; have v := kn b.val b.isLt (3*(left+i)+a.val) (by dsimp [left]; omega)
      simpa only [show (3*(left+i)+a.val)/3=left+i by omega,show (3*(left+i)+a.val)%3=a.val by omega,show 1+(3*(left+i)+a.val)=1+3*(left+i)+a.val by omega] using v)
    simpa only [M,show 1+3*(Y+s)=1+3*Y+3*s by omega,show 1+3*(left+i)=1+3*left+3*i by omega,rel _ _ hs] using h
  let T : Path B := {last:=45,col:=id,M:=M,start:=rfl,stop:=rfl,bound:=fun _ h => h,
                      next:=fun j _ => by simp [pred,B],
                      across:=fun r _ c _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+3*Y+r) (1+3*left+c) false,
                      down:=fun r _ c _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+3*Y+r) (1+3*left+c) true}
  have init : Kept T start := by
    intro r hr c hc; change r≤11 at hr; change c≤45 at hc
    have v : accepts (5+(r+1)%3) (5+(c+1)%3) (M r c) := by
      have z := accept_bulk u (3*Y+r) (3*left+c) (by omega) (by dsimp [left]; omega) F acy P step w clean (by
        intro p hp; apply zero; rw [hp]; intro E; cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [L7.view,reflect] at E <;> omega)
      simpa only [M,show 1+(3*Y+r)=1+3*Y+r by omega,show 1+(3*left+c)=1+3*left+c by omega,
        show rowTag (3*Y+r)=5+(r+1)%3 by unfold rowTag; split_ifs <;> omega,
        show realTag u (3*left+c)=5+(c+1)%3 by unfold realTag left; split_ifs <;> omega] using z
    have pin : r%3 != 0 || r>3 || c%3 != 0 || M r c==transpose (localWord (r/3) (c/3)) := by
      simp only [Bool.or_eq_true,bne_iff_ne,decide_eq_true_eq,beq_iff_eq]; by_contra! no
      have e := aligned (r/3) (c/3) (by omega) (by omega); apply no.2; convert e using 2 <;> omega
    have bd : M r c<512 := (unpack _).1
    simpa [start,build,T,B,cell,show r<12 by omega,show c<46 by omega,bd,v] using pin
  obtain ⟨G,pass,live⟩ := sound T _ 20 _ init replay
  have m := beq_iff_eq.mp (List.all_eq_true.mp pass _ (live 6 (by decide) 36 (by change 36≤45; decide)))
  have m1 := aligned 1 12 (by decide) (by decide)
  have start' (j : Nat) (lo : Y+1≤j) (hi : j≤Y+2) : square F w (1+3*j) (1+3*(q-3*Y+2))=73 := by
    have E : 1+3*(q-3*Y+2)=1+3*left+36 := by dsimp [left]; omega
    rcases (show j=Y+1 ∨ j=Y+2 by omega) with e|e
    · rw [E,show 1+3*j=1+3*Y+3 by omega]; exact m1.trans (by decide)
    · rw [E,show 1+3*j=1+3*Y+6 by omega]; exact m
  intro j lo hi i le lt
  induction i,le using Nat.le_induction with
  | base => exact start' _ lo hi
  | succ i h ih => exact east_step u q j i (by omega) (by omega) (by omega) F acy w P step clean zero (ih (by omega))
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
