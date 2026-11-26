import GridGraphs.ResidueTwoUpper.OneGap.FanCameraPatch
import GridGraphs.ResidueTwoUpper.OneGap.FanPhysicalSpeed
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open L7 FanSlab FanSeed Camera Port Halo ResidueZero Stencil

set_option maxHeartbeats 700000 in
/-- `y` is the true top tile row. The rooted window uses a three-site
halo for the three exceptional plaquettes, but no top seal. -/
theorem physical_root_step_rect (u q y g : Nat) (f : Nat) (root : q<f) (lose : g≤f)
    (room : 4≤y ∧ y+16≤11+14*u ∧ 4≤f ∧ f+16≤11+14*u)
    (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (N u) (N u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (Q : Flow F) (straight : Straight F w y f 9 9) (front : Front F w q (11+14*u) y g) :
    Front F w q (11+14*u) (y+4) (f+3) ∧ Plateau F w y (y+4) (f+3) (11+14*u) := by
  let R := 1+3*y; let C := 1+3*f; let M := marksAt F w R C; let A := dirsAt Q w R C
  have price := prices_of_seed u q F acy w P step clean zero
  obtain ⟨h,v,active⟩ := rect F Q w price R C 30 30 (by dsimp [R]; omega) (by dsimp [C]; omega)
  have read (r c : Nat) : bits (ink M r c)=square F w (R+r) (C+c) := by unfold ink M marksAt bitAt square; simp only [Nat.add_assoc]
  have tile' (j i : Nat) : bits (ink M (3*j) (3*i))=square F w (1+3*(y+j)) (1+3*(f+i)) := by rw [read]; congr 1 <;> dsimp [R,C] <;> omega
  have I : Inputs 9 9 false M A := by
    refine ⟨h,v,?_,?_,?_,?_⟩
    · intro j hj i hi; rw [tile']; exact straight j hj i hi
    · intro j hj i hi b hb a ha; rw [read]; have pr := price (R+(3*j+b)) (C+(3*i+a)) (by dsimp [R]; omega) (by dsimp [R]; omega) (by dsimp [C]; omega) (by dsimp [C]; omega)
      simpa only [show (R+(3*j+b))%3=(b+1)%3 by dsimp [R]; omega,show (C+(3*i+a))%3=(a+1)%3 by dsimp [C]; omega] using pr
    · intro j hj i hi seed; simp only [tile'] at seed ⊢; rw [show f+(i+1)=(f+i)+1 by omega]; exact east_step u q (y+j) (f+i) (by omega) (by omega) (by omega) F acy w P step clean zero seed
    · intro i hi; have src := front.1 y le_rfl le_rfl (f+i) (by omega) (by omega)
      refine ⟨by change bits (ink M (3*0) (3*i))=_; rw [tile',Nat.add_zero]; exact src,?_⟩
      intro a; let pt : ResidueZero.Pos := (1+3*(y:Int),1+3*((f+i:Nat):Int)+a.val)
      have pos : (((R+0:Nat):Int),((C+(3*i+a.val):Nat):Int))=pt := by ext <;> dsimp [R,C,pt]; push_cast <;> ring
      have bd := dir_lt F w Q price (R+0) (C+(3*i+a.val)) (by dsimp [R]; omega) (by dsimp [C]; have := a.isLt; omega)
      change (Fin.ofNat 4 (arrow Q.parent w _) == (3:Fin 4))=(a==0)
      rw [pos] at bd; simp only [beq_eq_decide,Fin.ext_iff,Fin.ofNat,pos,Nat.mod_eq_of_lt bd]; change decide (arrow Q.parent w pt=3)=decide (a.val=0)
      by_cases a0 : a.val=0
      · have z := root_tip F w Q y (f+i) (by dsimp [N]; omega) (by dsimp [N]; omega) (front.2.2 _ (by omega) (by omega) (by omega)); simp [pt,a0]; simpa using z
      · have nz := off_tip F w Q price y (f+i) (by omega) (by omega) src (front.1 _ le_rfl le_rfl (f+i+1) (by omega) (by omega)) a a0; simp [pt,a0]; simpa using nz
  have exclude' (j i : Nat) (hj : j<9) (hi : i<9) := avoids F Q w price (1+3*(y+j)) (1+3*(f+i)) (by omega) (by omega)
  have output := replay_extra (fun a b c d => !banned.contains (a,b,c,d)) (d:=3) (s:=4) (k:=5) M A I (by
    intro j hj i hi; simp only [tile',Bool.not_eq_true']; apply Bool.eq_false_iff.mpr; intro h; have h := List.contains_iff_mem.mp h; apply False.elim; apply (show _ ∉ banned from ?_) h
    simpa only [quadAt,show 1+3*(y+j)+3=1+3*(y+(j+1)) by omega,show 1+3*(f+i)+3=1+3*(f+(i+1)) by omega] using exclude' _ _ hj hi) root_test (by decide)
  have rect' : Plateau F w y (y+4) (f+3) (11+14*u) := by
    intro j lo hi i le lt; induction i,le using Nat.le_induction with
    | base => have z := output (j-y) (by omega); rwa [tile',show y+(j-y)=j by omega] at z
    | succ i h ih => exact east_step u q j i (by omega) (by omega) (by omega) F acy w P step clean zero (ih (by omega))
  exact ⟨advance_front F w (by omega) (by omega) le_rfl (fun _ _ _ => by omega) front rect',rect'⟩

theorem physical_root_step (u q y g : Nat) (f : Nat) (root : q<f) (lose : g≤f)
    (room : 4≤y ∧ y+16≤11+14*u ∧ 4≤f ∧ f+16≤11+14*u)
    (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (N u) (N u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (Q : Flow F) (straight : Straight F w y f 9 9) (front : Front F w q (11+14*u) y g) :
    Front F w q (11+14*u) (y+4) (f+3) :=
  (physical_root_step_rect u q y g f root lose room F acy w P step clean zero Q straight front).1
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
