import GridGraphs.ResidueTwoUpper.OneGap.FanShrink
import GridGraphs.ResidueTwoUpper.OneGap.FanTeeth
import GridGraphs.ResidueTwoUpper.OneGap.FanDangling

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSlab FanSeed BoundarySix.Connected

def WestTeeth (u q : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u))) (w : View) :=
  ∀ i<q, marked F (L7.view w (35+42*u:Nat) 2 (2+3*i:Nat))=true

set_option maxHeartbeats 700000 in
theorem handoff_of_score (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) :
    let n := 35+42*u
    ∃ (w : View) (p : GridVertex n n) (q : Nat), q%2=1 ∧ 1≤q ∧ q+2≤11+14*u ∧
      coord p=L7.view w n 2 (2+3*q:Nat) ∧ (Bonds F).IsIsolated p ∧
      WestTeeth u q F w ∧ (57≤q → Rows u q F w ∧
        ∀ y, 6≤y → y≤(q-15)/6 → Known u q y F w ∧ Known u q (y+1) F w) ∧
      (tile F (FanSeed.opposite w) 4 (31+42*u)=73 →
        ∃ r, 5≤r ∧ r<29+42*u ∧ marked F (L7.view w n r (31+42*u:Nat))=false ∧
          marked F (L7.view w n (r+1:Nat) (31+42*u:Nat))=false) := by
  obtain ⟨P,p,w,s,f,i,step,clean,zero,iso,side,pos,lo,hi,phase,core,east⟩ := scored_seed u F acy score one
  let q := (i-1)/3
  have qi : i=1+3*q := by dsimp [q]; omega
  have odd : q%2=1 := by omega
  have fits : q+2≤11+14*u := by omega
  have atStar : coord p=L7.view w (35+42*u:Nat) 2 (2+3*q:Nat) := by rw [pos]; congr 1; push_cast; omega
  have N : ((35+42*u:Nat):Int)=35+42*(u:Int) := by push_cast; ring
  have eq := atStar; rw [N] at eq
  have zs (t) (ne : coord t≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat)) : starSlack F P t=0 := zero t (fun e => ne (e ▸ eq))
  have paid : tile F w 1 (1+3*q)=64 := qi ▸ core
  have teeth := Teeth.west_teeth u q odd fits F acy score one w s f side P step clean zs
    (by rw [←tile_eq F w (by omega)]; exact paid)
  refine ⟨w,p,q,odd,by omega,fits,atStar,iso,teeth,?_,?_⟩
  · intro big
    have rows := rows_from_teeth u q big fits odd F acy P step clean w zs teeth paid
      (fun k lt hk => (east (1+3*k) (by omega) (by omega) (by omega)).1)
    exact ⟨rows,through_handoff u q big fits F acy P step clean w zs rows⟩
  · intro cap
    have last := east (31+42*u) (by omega) (by omega) (by omega)
    exact break_or_cap u F acy score one clean w s f side last.1 last.2.1 cap

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
