import GridGraphs.ResidueTwoUpper.OneGap.FanCamera
import GridGraphs.ResidueTwoUpper.OneGap.FanStripe

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open L7 FanSlab FanSeed Stencil ResidueZero Camera

abbrev N (u : Nat) := 35+42*u
def Prices {u} (F : Finset (GridVertex (N u) (N u))) (w : View) := ∀ r c : Nat,
    6≤r → r+7≤33+42*u → 6≤c → c+7≤33+42*u →
      accepts (5+r%3) (5+c%3) (square F w r c)
theorem prices_of_seed (u q : Nat) (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (N u) (N u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0) : Prices F w := by
  intro r c hr lr hc lc
  have A := accept_bulk u (r-1) (c-1) (by omega) (by omega) F acy P step w clean (by
    intro p hp; apply zero; rw [hp]; intro E; cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [L7.view,reflect] at E <;> omega)
  simpa only [show 1+(r-1)=r by omega,show 1+(c-1)=c by omega,show rowTag (r-1)=5+r%3 by unfold rowTag; split_ifs <;> omega,
    show realTag u (c-1)=5+c%3 by unfold realTag; split_ifs <;> omega] using A

def strip (a b c r : Nat) := bits fun t : Fin 9 => (if t.val%3=0 then a else if t.val%3=1 then b else c).testBit (r+t.val/3)
private def band (r c a b d : Nat) := (List.range 3).all fun i => accepts (5+(r+i)%3) (5+c%3) (strip a b d i)
private theorem cover5 : ∀ r c : Fin 3, ∀ b m d : Fin 32, (strip b m d 1 &&& 186)=0 → band r (c+1) b m d →
    ∀ a : Fin 32, band r c a b m → ∀ e : Fin 32, band r (c+2) m d e → False := by native_decide

theorem bulk_active (u : Nat) (F : Finset (GridVertex (N u) (N u))) (w : View) (price : Prices F w) (r c : Nat)
    (rr : 8≤r ∧ r+7≤33+42*u) (cc : 8≤c ∧ c+7≤33+42*u) : ∃ z,(Bonds F).Adj (point u w (r,c)) z := by
  let R := r-2; let C := c-2
  let X (j : Nat) := encodeRow (fun b => marked F (L7.view w (N u) (R+b.val:Nat) (C+j:Nat)))
  have dec (s j : Nat) (hs : s≤2) : strip (X j) (X (j+1)) (X (j+2)) s=square F w (R+s) (C+j) := by
    unfold strip square; apply congrArg bits; funext a
    let t : Fin 5 := ⟨s+a.val/3,by have := a.isLt; omega⟩
    have test : ∀ m : Fin 32, ∀ k : Fin 5, m.val.testBit k.val=decide (bit m k=1) := by decide
    have same (b : Nat) : (X b).val.testBit t.val=marked F (L7.view w (N u) (R+t.val:Nat) (C+b:Nat)) := by
      rw [test]; unfold X; rw [row_bit]; cases marked F _ <;> rfl
    have rows : R+t.val=R+s+a.val/3 := by dsimp [t]; omega
    by_cases a0 : a.val%3=0
    · rw [if_pos a0,same _,rows,a0,Nat.add_zero]
    by_cases a1 : a.val%3=1
    · rw [if_neg a0,if_pos a1,same _,rows,a1]; simp [Nat.add_assoc]
    · rw [if_neg a0,if_neg a1,same _,rows,show a.val%3=2 by omega]; simp [Nat.add_assoc]
  have reg (j : Nat) (hj : j≤2) : band (R%3) (C%3+j) (X j) (X (j+1)) (X (j+2)) := by
    apply List.all_eq_true.mpr; intro s hs; have hs := List.mem_range.mp hs; rw [dec _ _ (by omega)]
    simpa only [show (R%3+s)%3=(R+s)%3 by omega,show (C%3+j)%3=(C+j)%3 by omega] using price (R+s) (C+j) (by dsimp [R]; omega) (by dsimp [R]; omega) (by dsimp [C]; omega) (by dsimp [C]; omega)
  by_contra! no
  apply cover5 ⟨R%3,by omega⟩ ⟨C%3,by omega⟩ (X 1) (X 2) (X 3) _ (reg 1 (by decide)) (X 0) (reg 0 (by decide)) (X 4) (reg 2 (by decide))
  have un (d : Fin 4) : bitAt F w (r,c)=false ∧ bitAt F w (shift (r,c) d)=false := by
    have inside0 : In (N u) (r,c) := by dsimp [In,N]; omega
    have inside1 : In (N u) (shift (r,c) d) := by fin_cases d <;> simp [In,shift,N] <;> omega
    have e : (gridGraph _ _).Adj (point u w (r,c)) (point u w (shift (r,c) d)) := by
      rw [adj_iff w,coords_point inside0,coords_point inside1]; fin_cases d <;> simp [shift]
    have a := no (point u w (shift (r,c) d)); change ¬(_ ∧ (_ ∨ _)) at a
    simpa only [bitAt,←coord_point (w:=w) inside0,←coord_point (w:=w) inside1,marked_at,decide_eq_false_iff_not,Finset.mem_coe] using not_or.mp (fun h => a ⟨e,h⟩)
  rw [dec _ _ (by decide)]
  have check : ∀ f : Fin 9 → Bool, (∀ k : Fin 9,k.val∈[1,3,4,5,7] → f k=false) → bits f &&& 186=0 := by native_decide
  apply check; intro k hk; have a := un 0; have b := un 1; have c' := un 2; have d := un 3
  have row (z : Nat) (hz : z<3) : ((R+1+z:Nat):Int)=(r:Int)-1+z := by dsimp [R]; omega
  have col (z : Nat) (hz : z<3) : ((C+1+z:Nat):Int)=(c:Int)-1+z := by dsimp [C]; omega
  change marked F (L7.view w (N u) (R+1+k.val/3:Nat) (C+1+k.val%3:Nat))=false
  rw [row _ (by have := k.isLt; omega),col _ (by omega)]
  simp only [bitAt,shift] at a b c' d
  fin_cases k <;> simp at hk <;> norm_num
  all_goals first | exact a.1 | exact a.2 | exact b.2 | exact c'.2 | exact d.2 | (rw [show (r:Int)-1+2=r+1 by ring]; exact b.2) | (rw [show (c:Int)-1+2=c+1 by ring]; exact a.2)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
