import GridGraphs.ResidueTwoUpper.OneGap.FanCollisionWideScan
import GridGraphs.ResidueTwoUpper.OneGap.FanCollision
import GridGraphs.ResidueTwoUpper.OneGap.FanCameraPatch

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.CollisionWide
open ResidueZero Stencil L7 FanSlab Camera Port Port.Halo Short

private theorem ports (x z : Short.Label) (d e : Nat) (ovEq : ov d x.1=ov e z.1)
    (force : decide (Short.contact x.1 d)=decide (Short.contact z.1 e))
    (own : Own (x.2==d) (z.2==e) (decide (Short.contact x.1 d)) false) :
    Short.port true d x=Short.port false e z ∧ Short.port true e z=Short.port false d x := by
  unfold Short.port
  rw [ovEq,force]
  have rule : ∀ a b m : Bool, Own a b m false →
      xor m a=b ∧ xor m b=a := by decide
  obtain ⟨h₁,h₂⟩ := rule _ _ _ own
  rw [force] at h₁ h₂
  simp only [Bool.true_and,Bool.false_and,Bool.false_xor,h₁,h₂,and_self]

private theorem contact_bits : ∀ (f : Ink) (d : Fin 4),
    decide (Short.contact (bits f) d)= (f 4 || f (⟨[5,7,3,1][d.val]!,by fin_cases d <;> decide⟩ : Fin 9)) := by
  native_decide

private theorem own_fold : ∀ a b m n : Bool, Own a b m n → Own a b (m || n) false := by decide
private theorem beq_val : ∀ a b : Fin 4, (a.val==b.val)=(a==b) := by decide

set_option maxHeartbeats 2500000 in
theorem owner_chart {u w} {F : Finset (GridVertex (N u) (N u))} (Q : Flow F) (price : Prices F w) (R C n : Nat)
    (rr : 8≤R ∧ R+(n+2)+6≤33+42*u) (cc : 8≤C ∧ C+(n+2)+6≤33+42*u) :
    ∃ X : Nat → Nat → Short.Label, Short.Agree n X ∧
      (∀ r<n, ∀ c<n, active (X r c).1 (X r c).2) ∧
      (∀ r c, (X r c).1=square F w (R+r) (C+c)) ∧
      (∀ r c, (X r c).2=((dirsAt Q w R C (r+1) (c+1)).val)) := by
  let M := marksAt F w R C
  let A := dirsAt Q w R C
  let m (r c : Nat) := bits (ink M r c)
  let X (r c : Nat) : Short.Label := (m r c,(A (r+1) (c+1)).val)
  obtain ⟨east,south,active⟩ := rect F Q w price R C (n+2) (n+2) rr cc
  have sq (r c : Nat) : m r c=square F w (R+r) (C+c) := by
    unfold m ink M marksAt bitAt square
    simp only [Nat.add_assoc]
  have contacts (r c : Nat) (v : Bool) :
      let d : Fin 4 := if v then 1 else 0
      let e : Fin 4 := if v then 3 else 2
      let rr := r+v.toNat
      let cc := c+(!v).toNat
      decide (Short.contact (m r c) d)= (M (r+1) (c+1) || M (rr+1) (cc+1)) ∧
      decide (Short.contact (m rr cc) e)= (M (rr+1) (cc+1) || M (r+1) (c+1)) := by
    cases v <;> dsimp only [m,Bool.toNat,Bool.not,if_false,if_true] <;>
      constructor <;> rw [contact_bits] <;> rfl
  have agree : Short.Agree n X := by
    intro r hr c hc
    have run (v : Bool) (room : if v then r+1<n else c+1<n) :
        let d := v.toNat
        let rr := r+d; let cc := c+(!v).toNat
        Short.port true d (X r c)=Short.port false (d+2) (X rr cc) ∧
        Short.port true (d+2) (X rr cc)=Short.port false d (X r c) := by
      dsimp only
      have eq := square_meet F w (R+r) (C+c) v
      have base := contacts r c v
      cases v
      · change Short.port true 0 (X r c)=Short.port false 2 (X r (c+1)) ∧
          Short.port true 2 (X r (c+1))=Short.port false 0 (X r c)
        have h := own_fold _ _ _ _ (east (r+1) (by omega) (c+1) (by omega))
        have e₀ : decide (Short.contact (m r c) 0)=(M (r+1) (c+1) || M (r+1) (c+1+1)) := base.1
        have e₂ : decide (Short.contact (m r (c+1)) 2)=(M (r+1) (c+1+1) || M (r+1) (c+1)) := base.2
        apply ports (X r c) (X r (c+1)) 0 2
        · change ov 0 (square F w (R+r) (C+c))=ov 2 (square F w (R+r) (C+(c+1))) at eq
          simpa only [X,sq] using eq
        · exact e₀.trans ((Bool.or_comm ..).trans e₂.symm)
        · simpa only [X,e₀,
            show ∀ a : Fin 4, (a.val==0)=(a==0) from fun a => beq_val a 0,
            show ∀ a : Fin 4, (a.val==2)=(a==2) from fun a => beq_val a 2] using h
      · change Short.port true 1 (X r c)=Short.port false 3 (X (r+1) c) ∧
          Short.port true 3 (X (r+1) c)=Short.port false 1 (X r c)
        have h := own_fold _ _ _ _ (south (r+1) (by omega) (c+1) (by omega))
        have e₁ : decide (Short.contact (m r c) 1)=(M (r+1) (c+1) || M (r+1+1) (c+1)) := base.1
        have e₃ : decide (Short.contact (m (r+1) c) 3)=(M (r+1+1) (c+1) || M (r+1) (c+1)) := base.2
        apply ports (X r c) (X (r+1) c) 1 3
        · change ov 1 (square F w (R+r) (C+c))=ov 3 (square F w (R+(r+1)) (C+c)) at eq
          simpa only [X,sq] using eq
        · exact e₁.trans ((Bool.or_comm ..).trans e₃.symm)
        · simpa only [X,e₁,
            show ∀ a : Fin 4, (a.val==1)=(a==1) from fun a => beq_val a 1,
            show ∀ a : Fin 4, (a.val==3)=(a==3) from fun a => beq_val a 3] using h
    exact ⟨fun h => run false h, fun h => run true h⟩
  refine ⟨X,agree,?_,sq,fun _ _ => rfl⟩
  intro r hr c hc
  have act := active r (by omega) c (by omega)
  exact act

set_option maxHeartbeats 2500000 in
/-- One translated physical chart for all three odd collision shapes. -/
theorem physical_chart (u q Y l : Nat) (hy : 6≤Y) (len : l∈[15,17,19])
    (centerLen : q=6*Y+l) (fit : q+2≤11+14*u)
    (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (N u) (N u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p))
    (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (Q : Flow F) (first : Known u q Y F w) (second : Known u q (Y+1) F w) :
    ∃ X : Nat → Nat → Short.Label, Short.Agree size X ∧ Short.Kept size X (CollisionWide.chart l) ∧
      ∀ r c, (X r c).1=square F w (1+3*Y+r) (1+3*(3*Y+2)+c) := by
  have lb : 15≤l ∧ l≤19 := by simp at len; omega
  let left := 3*Y+2
  let R := 1+3*Y
  let C := 1+3*left
  have price := prices_of_seed u q F acy w P step clean zero
  obtain ⟨X,agree,actX,sq,dirs⟩ := owner_chart Q price R C size
    (by dsimp [R,size]; omega) (by dsimp [C,left,size]; omega)
  let m := fun r c => (X r c).1
  change ∀ r c, m r c=square F w (R+r) (C+c) at sq
  have word_eq (s i : Nat) (hs : s≤1) : actual q (Y+s) (left+i)=actual (42+l) (7+s) (23+i) := by
    interval_cases s <;> unfold actual word left <;> split_ifs <;> first | rfl | omega | (congr 1 <;> omega)
  have planted (r c : Nat) (hr : r≤3) (h3 : r%3=0) (hc : c%3=0) (bound : c<64) : m r c=seeds l (r/3) (c/3) := by
    let s := r/3; let i := c/3
    have kn : Known u q (Y+s) F w := by
      have hs : s=0 ∨ s=1 := by dsimp [s]; omega
      rcases hs with h|h
      · simpa only [h,Nat.add_zero] using first
      · simpa only [h] using second
    have hm : actual q (Y+s) (left+i)<512 := by
      have finite : ∀ l∈[15,17,19], ∀ (s : Fin 2) (i : Fin 22),
          decide (actual (42+l) (7+s.val) (23+i.val)<512)=true := by decide
      rw [word_eq s i (by dsimp [s]; omega)]
      exact of_decide_eq_true (finite l len ⟨s,by dsimp [s]; omega⟩ ⟨i,by dsimp [i]; omega⟩)
    have z := FanBoot.align F w (Y+s) (left+i) _ hm (by
      intro a b
      have v := kn b.val b.isLt (3*(left+i)+a.val) (by dsimp [left,i]; omega)
      simpa only [show (3*(left+i)+a.val)/3=left+i by omega,show (3*(left+i)+a.val)%3=a.val by omega,
        show 1+(3*(left+i)+a.val)=1+3*(left+i)+a.val by omega] using v)
    rw [sq,show R+r=1+3*(Y+s) by dsimp [R,s]; omega,show C+c=1+3*(left+i) by dsimp [C,i]; omega,z]
    exact congrArg transpose (word_eq s i (by dsimp [s]; omega))
  have kept : Short.Kept size X (CollisionWide.chart l) := by
    intro r hr c hc
    change r<64 at hr; change c<64 at hc
    have pr := price (R+r) (C+c) (by dsimp [R]; omega) (by dsimp [R]; omega)
      (by dsimp [C,left]; omega) (by dsimp [C,left]; omega)
    rw [←sq,show (R+r)%3=(r+1)%3 by dsimp [R]; omega,
      show (C+c)%3=(c+1)%3 by dsimp [C]; omega] at pr
    have init : (decide (r>3) || r%3 != 0 || c%3 != 0 || m r c==seeds l (r/3) (c/3))=true := by
      by_cases h : 3<r
      · simp [h]
      by_cases e : r%3=0
      swap
      · simp [e]
      by_cases f : c%3=0
      swap
      · simp [f]
      rw [planted r c (by omega) e f hc]
      simp
    have act := actX r hr c hc
    have bd : m r c<512 := by rw [sq]; exact (unpack _).1
    have ar : (X r c).2<4 := (dirs r c) ▸ (dirsAt Q w R C (r+1) (c+1)).isLt
    rw [CollisionWide.chart,Short.at_build (show r<size from hr) (show c<size from hc)]
    apply List.mem_flatMap.mpr
    exact ⟨_,List.mem_filter.mpr ⟨List.mem_range.mpr bd,by simp only [pr,init,Bool.true_and]⟩,
       List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨List.mem_range.mpr ar,act⟩,rfl⟩⟩
  exact ⟨X,agree,kept,sq⟩

theorem plateau17 (u q Y : Nat) (hy : 6≤Y) (centerLen : q=6*Y+19) (fit : q+2≤11+14*u)
    (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (N u) (N u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p))
    (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (Q : Flow F) (first : Known u q Y F w) (second : Known u q (Y+1) F w) :
    Plateau F w (Y+2) (Y+6) (q-3*Y+2) (11+14*u) := by
  obtain ⟨X,agree,kept,sq⟩ := physical_chart u q Y 19 hy (by decide) centerLen fit F acy w P step clean zero Q first second
  intro j lo hi i le lt
  induction i,le using Nat.le_induction with
  | base =>
    have z := forced X agree kept (j-Y) (by omega) (by omega)
    rwa [sq,show 1+3*Y+3*(j-Y)=1+3*j by omega,show 1+3*(3*Y+2)+57=1+3*(q-3*Y+2) by omega] at z
  | succ i h ih => exact east_step u q j i (by omega) (by omega) (by omega) F acy w P step clean zero (ih (by omega))
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.CollisionWide
