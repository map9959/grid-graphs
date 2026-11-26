import GridGraphs.ResidueTwoUpper.OneGap.FanNorthScan
import GridGraphs.ResidueTwoUpper.OneGap.FanPhysicalFront

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero L7 FanSeed Stencil BoundarySix.Connected

/-- Physical long-fan frontier; no additional input row, owner label,
root, or mark test is supplied by the caller. -/
theorem front_of_score (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) :
    let n := 35+42*u
    ∃ (P : GridVertex n n → GridVertex n n) (w : View) (p : GridVertex n n) (q : Nat),
      q%2=1 ∧ q+2≤11+14*u ∧ (Bonds F).IsIsolated p ∧ coord p=L7.view w n 2 (2+3*q:Nat) ∧
      (∀ t,P t≠t → (Bonds F).Adj t (P t)) ∧ (∀ a,patchSlack F a=0) ∧ (∀ t,t≠p → starSlack F P t=0) ∧
      (57≤q → let Y := (q-15)/6; Front F w q (11+14*u) (Y+2) (q-3*Y+3)) ∧
      (tile F (FanSeed.opposite w) 4 (31+42*u)=73 → ∃ r,5≤r ∧ r<29+42*u ∧
        marked F (L7.view w n r (31+42*u:Nat))=false ∧ marked F (L7.view w n (r+1:Nat) (31+42*u:Nat))=false) := by
  obtain ⟨P,w,p,q,odd,fit,iso,pos,step,clean,zero,front,cap⟩ :=
    front_rows_with_scan (show NorthOutput from north_output) u F acy score one
  exact ⟨P,w,p,q,odd,fit,iso,pos,step,clean,zero,fun big => (front big).1,cap⟩
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
