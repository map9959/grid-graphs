import GridGraphs.ResidueTwoUpper.OneGap.FanLineFront

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSlab FanSweep FanSeed BoundarySix.Connected

abbrev NorthOutput := ∀ (h : Nat), h∈[2,4,6,8] → ∀ T : Path (box h), Kept T (base h) →
  ∀ j y k : Nat, j≤T.last → y<6 → k<57+h → T.col j=3*k → T.M (3*y) j=transpose (history 57 y k)

set_option maxHeartbeats 1800000 in
private theorem pad_history (q x z i y : Nat) (qx : q=57+x) (hy : y<6) :
    history 57 y (foldCol x z (3*i)/3)=history q y i := by
  by_cases top : y=0
  · subst y; unfold history seedWord foldCol; split_ifs <;> first | rfl | omega
  unfold history; simp only [if_neg top]; unfold actual word foldCol
  split_ifs <;> first | rfl | omega | (congr 1 <;> omega)

set_option maxHeartbeats 800000 in
theorem north_rows (scan : NorthOutput) (u q : Nat) (big : 57≤q) (fits : q+2≤11+14*u) (odd : q%2=1)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p))
    (clean : ∀ a,patchSlack F a=0) (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (west : WestTeeth u q F w) (core : tile F w 1 (1+3*q)=64) (east : ∀ i, q< i → i<11+14*u → tile F w 1 (1+3*i)=72) :
    ∀ j≤(q-15)/6+1, Read (35+42*u) q j F w := by
  have pair := through_handoff u q big fits F acy P step clean w zero (rows_from_teeth u q big fits odd F acy P step clean w zero west core east)
  intro j hj i a b hc ha hb
  by_cases low : j<6
  swap
  · have R : Known u q j F w := by
      by_cases e : j≤(q-15)/6
      · exact (pair j (by omega) e).1
      · simpa only [show (q-15)/6+1=j by omega] using (pair ((q-15)/6) (by omega) le_rfl).2
    have m := R b hb (3*i+a) (by omega)
    simpa only [history,if_neg (by omega : j≠0),show 1+(3*i+a)=1+3*i+a by omega,show (3*i+a)/3=i by omega,show (3*i+a)%3=a by omega] using m
  apply with_boot_chart u q big fits odd F acy P step clean w zero west core east
  intro h x z hh hz eqs T tl tc tm init
  let idx := foldCol x z (3*i)/3
  have jb : 3*i≤T.last := by omega
  have lab : T.col (3*i)=3*idx := by rw [tc]; unfold idx foldCol; split_ifs <;> omega
  have ib : idx<57+h := by have := T.bound _ jb; rw [lab] at this; dsimp [box] at this; omega
  have m := scan h (by simp; omega) T init _ _ _ jb low ib lab; rw [tm] at m
  change square F w (1+3*j) (1+3*i)=_ at m
  let k : Fin 9 := ⟨3*b+a,by omega⟩
  have dec := (unpack (fun t : Fin 9 => marked F (L7.view w (35+42*u:Nat) (1+3*j+t.val/3:Nat) (1+3*i+t.val%3:Nat)))).2 k
  change lane (square F w _ _) k=_ at dec; rw [m] at dec
  have tab : ∀ (j : Fin 6) (t : Fin 65) (a b : Fin 3), lane (transpose (history 57 j t)) (3*b.val+a.val)=lane (history 57 j t) (3*a.val+b.val) := by native_decide
  have bit := tab ⟨j,low⟩ ⟨idx,by omega⟩ ⟨a,ha⟩ ⟨b,hb⟩
  change lane (transpose (history 57 j idx)) k=lane (history 57 j idx) (3*a+b) at bit
  rw [bit,pad_history q x z i j eqs.1 low] at dec
  simpa only [k,show (3*b+a)/3=b by omega,show (3*b+a)%3=a by omega] using dec.symm
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
