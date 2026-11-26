import GridGraphs.ResidueTwoUpper.OneGap.FanPortTile
import GridGraphs.ResidueTwoUpper.OneGap.FanTips
import GridGraphs.ResidueTwoUpper.OneGap.FanPortMoves

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSlab FanSeed Camera Port

/-- Collision output needed by the dangling speeds. Coordinates in this
predicate are physical aligned tile indices, not folded chart labels. -/
def Straight {u} (F : Finset (GridVertex (N u) (N u))) (w : View) (y f W H : Nat) := ∀ j≤H, ∀ i≤ W,
    square F w (1+3*(y+j)) (1+3*(f+i))∈shapes

set_option maxHeartbeats 1000000 in
theorem physical_dangling_step_rect (u q y f W H d s k : Nat) (pass : test W H d s k true)
    (size : s<H ∧ d<W) (room : 3≤y ∧ y+H+6≤11+14*u ∧ 3≤f ∧ f+W+6≤11+14*u) (dang : f+W≤q)
    (birth : 2≤(q:Int)-(f+W)+3 ∧ (q:Int)-f+3≤3*(y:Int))
    (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (N u) (N u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (Q : Flow F) (straight : Straight F w y f W H) (front : Front F w q (11+14*u) y f) :
    Front F w q (11+14*u) (y+s) (f+d+1) ∧ Plateau F w y (y+s) (f+d) (11+14*u) := by
  let R := 1+3*y; let C := 1+3*f
  let M (b a : Nat) := bitAt F w ((R+b:Nat),(C+a:Nat))
  let D (b a : Nat) := arrow Q.parent w ((R+b:Nat),(C+a:Nat))
  let A (b a : Nat) : Fin 4 := Fin.ofNat 4 (D b a)
  have price := prices_of_seed u q F acy w P step clean zero
  have bound (r c : Nat) (hr : r<3*(H+1)) (hc : c<3*(W+1)) : D r c<4 := dir_lt F w Q price _ _ (by dsimp [R]; omega) (by dsimp [C]; omega)
  have norm (b a : Nat) (hb : b<3*(H+1)) (ha : a<3*(W+1)) (d : Fin 4) : (A b a==d)=(D b a==d.val) := by
    simp only [A,beq_eq_decide,Fin.ext_iff,Fin.ofNat,Nat.mod_eq_of_lt (bound b a hb ha)]
  have read (r c : Nat) : bits (ink M r c)=square F w (R+r) (C+c) := by unfold ink M bitAt square; simp only [Nat.add_assoc]
  have tile' (j i : Nat) : bits (ink M (3*j) (3*i))=square F w (1+3*(y+j)) (1+3*(f+i)) := by rw [read]; congr 1 <;> dsimp [R,C] <;> omega
  have I : Inputs W H true M A := by
    constructor
    · intro r hr c hc
      have eq : shift ((R+r:Nat),(C+c:Nat)) 0=(((R+r:Nat):Int),((C+(c+1):Nat):Int)) := by ext <;> simp [shift]; ring
      have cr := Camera.cross (w:=w) Q.step Q.covers 0 (p:=((R+r:Nat),(C+c:Nat))) (by dsimp [In,R,C,N]; omega) (by change In _ (shift _ 0); rw [eq]; dsimp [In,R,C,N]; omega)
      change Own (D r c==0) (arrow Q.parent w (shift ((R+r:Nat),(C+c:Nat)) 0)==2) (M r c) (bitAt F w (shift ((R+r:Nat),(C+c:Nat)) 0)) at cr
      rw [eq] at cr; unfold Across; rw [norm _ _ hr (by omega),norm _ _ hr hc]; exact cr
    · intro r hr c hc
      have eq : shift ((R+r:Nat),(C+c:Nat)) 1=(((R+(r+1):Nat):Int),((C+c:Nat):Int)) := by ext <;> simp [shift]; ring
      have cr := Camera.cross (w:=w) Q.step Q.covers 1 (p:=((R+r:Nat),(C+c:Nat))) (by dsimp [In,R,C,N]; omega) (by change In _ (shift _ 1); rw [eq]; dsimp [In,R,C,N]; omega)
      change Own (D r c==1) (arrow Q.parent w (shift ((R+r:Nat),(C+c:Nat)) 1)==3) (M r c) (bitAt F w (shift ((R+r:Nat),(C+c:Nat)) 1)) at cr
      rw [eq] at cr; unfold Down; rw [norm _ _ (by omega) hc,norm _ _ hr hc]; exact cr
    · intro j hj i hi; rw [tile']; exact straight j hj i hi
    · intro j hj i hi b hb a ha; rw [read]
      have p := price (R+(3*j+b)) (C+(3*i+a)) (by dsimp [R]; omega) (by dsimp [R]; omega) (by dsimp [C]; omega) (by dsimp [C]; omega)
      simpa only [show (R+(3*j+b))%3=(b+1)%3 by dsimp [R]; omega,show (C+(3*i+a))%3=(a+1)%3 by dsimp [C]; omega] using p
    · intro j hj i hi seed; simp only [tile'] at seed ⊢; rw [show f+(i+1)=(f+i)+1 by omega]
      exact east_step u q (y+j) (f+i) (by omega) (by omega) (by omega) F acy w P step clean zero seed
    · intro i hi; have src := front.1 y le_rfl le_rfl (f+i) (by omega) (by omega)
      refine ⟨by change bits (ink M (3*0) (3*i))=_; rw [tile',Nat.add_zero]; exact src,?_⟩
      intro a; have ar : D 0 (3*i+a.val)≠3 := by
        by_cases e : a.val=0
        · have h := dangling_tip F w Q q y (f+i) (by dsimp [N]; omega) (by dsimp [N]; omega) (by push_cast at *; omega)
            (front.2.1 _ (by omega) (by omega) (by omega)) src
          simpa [D,R,C,e,Nat.cast_add,Nat.cast_mul,Int.mul_add,add_assoc] using h
        let pt : Pos := ((R:Int),(C+(3*i+a.val):Nat)); have h0 : In (N u) pt := by dsimp [pt,In,N,R,C]; omega
        have h1 : In (N u) (shift pt 3) := by change In _ ((R:Int)-1,(C+(3*i+a.val):Nat)); dsimp [In,N,R,C]; omega
        have m0 := plateau_bit src a (0:Fin 3)
        -- The site above may be marked in a pre-plateau row. Use the
        -- sealed collar for that upper cut rather than assuming it blank.
        have collar :=  (front.2.1 (f+i) (by omega) (by omega) (by omega)).1
        intro north; have par := (going (w:=w) Q.step 3 h0 h1).mp north
        change Q.parent (point u w pt)=point u w (shift pt 3) at par
        have ne : Q.parent (point u w pt)≠point u w pt := by
          intro same; rw [same] at par; have E := congrArg (fun x => (coordinates w x).1) par
          change (coordinates w (point u w pt)).1=(coordinates w (point u w (shift pt 3))).1 at E
          rw [coords_point h0,coords_point h1] at E; change (R:Int)=(R:Int)-1 at E; omega
        have adj := Q.step _ ne; rw [par] at adj
        have colEq : (C+(3*i+a.val):Nat)=1+3*(f+i)+a.val := by dsimp [C]; omega
        have hblank : point u w pt∉F := by
          have B := coord_point (w:=w) h0
          apply decide_eq_false_iff_not.mp; rw [←marked_at,B]; change marked F (L7.view w _ (R:Nat) (C+(3*i+a.val):Nat))=false
          rw [colEq]; simpa [R,e] using m0
        have markedN := adj.2.resolve_left hblank
        let z := point u w (shift pt 3); have co := coords_point (w:=w) h1
        have z1 : (coordinates w z).1=1+3*(y:Int)-1 := by change (coordinates w (point u w _)).1=_; rw [co]; dsimp [pt,R,shift]; push_cast; ring
        have z2 : (coordinates w z).2=1+3*((f+i:Nat):Int)+a.val := by change (coordinates w (point u w _)).2=_; rw [co]; dsimp [pt,C,shift]; push_cast; ring
        -- a=2 is one site west of the *next* line, but two sites
        -- east of this one, still in its collar at the preceding row.
        have ad : (q:Int)-(f+i:Nat)+3≤1+3*(y:Int)-1 := by push_cast at *; omega
        have on := collar z markedN (by rw [z1]; omega) ⟨_,ad,by omega,by rw [z1,z2]; simp; omega⟩
        dsimp [onLine] at on; rw [z2] at on; omega
      rw [norm _ _ (by omega) (by have := a.isLt; omega)]; exact Bool.eq_false_iff.mpr (fun h => ar (beq_iff_eq.mp h))
  have res := replay_window (d:=d) (s:=s) (k:=k) M A I pass size
  have rectangle : Plateau F w y (y+s) (f+d) (11+14*u) := by
    intro j lo hi i le lt
    induction i,le using Nat.le_induction with
    | base => have z := res (j-y) (by omega); rwa [tile',show y+(j-y)=j by omega] at z
    | succ i h ih => exact east_step u q j i (by omega) (by omega) (by omega) F acy w P step clean zero (ih (by omega))
  exact ⟨advance_front F w (by omega) (by omega) (by omega) (fun t ht rt => by push_cast at *; omega) front rectangle,rectangle⟩

theorem physical_dangling_step (u q y f W H d s k : Nat) (pass : test W H d s k true)
    (size : s<H ∧ d<W) (room : 3≤y ∧ y+H+6≤11+14*u ∧ 3≤f ∧ f+W+6≤11+14*u) (dang : f+W≤q)
    (birth : 2≤(q:Int)-(f+W)+3 ∧ (q:Int)-f+3≤3*(y:Int))
    (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (N u) (N u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (Q : Flow F) (straight : Straight F w y f W H) (front : Front F w q (11+14*u) y f) :
    Front F w q (11+14*u) (y+s) (f+d+1) :=
  (physical_dangling_step_rect u q y f W H d s k pass size room dang birth F acy w P step clean zero Q straight front).1
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
