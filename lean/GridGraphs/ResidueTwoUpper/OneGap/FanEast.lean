import GridGraphs.ResidueTwoUpper.OneGap.FanLineFront
import GridGraphs.ResidueTwoUpper.OneGap.FanStripe

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSlab FanSeed

private def pack (a b d : Nat) (r : Nat) := bits fun j : Fin 9 =>
  ((if j.val%3=0 then a else if j.val%3=1 then b else d).testBit (r+j.val/3))
private def ok (c j a b d : Nat) := decide (30<c+j) || (List.range 3).all fun r => accepts (5+r) (realTag 0 (c+j)) (pack a b d r)
private def mid (a : Fin 4) := a.val%2+16*(a.val/2)
private theorem force : ∀ c∈[6,24,27], ∀ a b d : Fin 4, ok c 0 (14+mid a) (mid b) (mid d) →
    ∀ e : Fin 32, ok c 1 (mid b) (mid d) e → ∀ f : Fin 32, ok c 2 (mid d) e f →
    ∀ g : Fin 32, ok c 3 e f g → ∀ h : Fin 32, ok c 4 f g h → pack e f g 1=73 := by native_decide
private theorem pin : ∀ a b c : Fin 32, pack a b c 1=73 → ∃ A B C : Fin 4, a.val=14+mid A ∧ b.val=mid B ∧ c.val=mid C := by native_decide

set_option maxHeartbeats 700000 in
/-- Grow a 73 east, including the last aligned tile. The final fringe
chart leaves the out-of-catalogue seventh column open. -/
theorem east_step (u q y i : Nat) (lo : 2≤ i) (hi : i+2≤11+14*u) (row : 2≤y ∧ 3*y+10≤33+42*u)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (seed : square F w (1+3*y) (1+3*i)=73) : square F w (1+3*y) (1+3*(i+1))=73 := by
  let k := 11+14*u; let c := if i+2=k then 27 else if i+3=k then 24 else 6
  let X (j : Nat) := encodeRow (fun b => marked F (L7.view w (35+42*u:Nat) (3*y+b.val:Nat) (1+3*i+j:Nat)))
  have bit' : ∀ m : Fin 32, ∀ r : Fin 5, m.val.testBit r.val=decide (bit m r=1) := by decide
  have decode (r j : Nat) (hr : r≤2) : pack (X j) (X (j+1)) (X (j+2)) r=square F w (3*y+r) (1+3*i+j) := by
    unfold pack square; apply congrArg bits; funext a
    let t : Fin 5 := ⟨r+a.val/3,by have := a.isLt; omega⟩
    have same (b : Nat) : (X b).val.testBit t.val=marked F (L7.view w (35+42*u:Nat) (3*y+t.val:Nat) (1+3*i+b:Nat)) := by
      rw [bit']; unfold X; rw [row_bit]; cases marked F _ <;> rfl
    have rows : 3*y+t.val=3*y+r+a.val/3 := by dsimp [t]; omega
    by_cases a0 : a.val%3=0
    · rw [if_pos a0,same _]; rw [rows,a0,Nat.add_zero]
    by_cases a1 : a.val%3=1
    · rw [if_neg a0,if_pos a1,same _,rows,a1]; simp [Nat.add_assoc]
    · rw [if_neg a0,if_neg a1,same _,rows,show a.val%3=2 by omega]; simp [Nat.add_assoc]
  have legal (j : Nat) (hj : j≤4) : ok c j (X j) (X (j+1)) (X (j+2)) := by
    unfold ok; apply Bool.or_eq_true_iff.mpr; by_cases h : 30<c+j
    · left; simpa using h
    right; apply List.all_eq_true.mpr; intro r hr; have hr := List.mem_range.mp hr
    have A := accept_bulk u (3*y+r-1) (3*i+j) (by omega) (by dsimp [c,k] at h; split_ifs at h <;> omega) F acy P step w clean (by
      intro p hp; apply zero; rw [hp]; intro E; cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [L7.view,reflect] at E <;> omega)
    have col : realTag u (3*i+j)=realTag 0 (c+j) := by unfold realTag c k; split_ifs <;> omega
    rw [decode _ _ (by omega)]; simpa only [show rowTag (3*y+r-1)=5+r by unfold rowTag; split_ifs <;> omega,col,
      show 1+(3*y+r-1)=3*y+r by omega,show 1+(3*i+j)=1+3*i+j by omega] using A
  have h := decode 1 0 (by decide); simp only [show 3*y+1=1+3*y by omega,Nat.add_zero,seed] at h
  obtain ⟨a,b,d,ea,eb,ed⟩ := pin (X 0) (X 1) (X 2) h
  have ck := force c (by dsimp [c]; split_ifs <;> simp) a b d
  rw [←ea,←eb,←ed] at ck
  have out := ck (legal 0 (by decide)) _ (legal 1 (by decide)) _ (legal 2 (by decide)) _ (legal 3 (by decide)) _ (legal 4 (by decide))
  rw [decode 1 3 (by decide)] at out
  simpa only [show 3*y+1=1+3*y by omega,show 1+3*i+3=1+3*(i+1) by omega] using out
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
