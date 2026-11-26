import GridGraphs.ResidueTwoUpper.OneGap.FanSpeedTail

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open L7 FanSeed FanSlab Camera Port ResidueZero Stencil BoundarySix.Connected

/-- Scored long-fan reduction to remaining-height data and a true south
window. All intermediate speed steps use the same mask set and real cuts. -/
theorem south_handoff_of_score (u : Nat) (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) :
    ∃ (w : View) (p : GridVertex (N u) (N u)) (q : Nat), q%2=1 ∧ q+2≤11+14*u ∧
      (Bonds F).IsIsolated p ∧ coord p=L7.view w (N u) 2 (2+3*q:Nat) ∧
      (57≤q → let Y := (q-15)/6
        Front F w q (11+14*u) (Y+2) (q-3*Y+3) ∧
        ((12≤u ∨ Speed.Reaches (11+14*u) q (Speed.start (11+14*u) q)) →
          Plateau F w (Y+2) (Y+6) (q-3*Y+2) (11+14*u) → DeepAfter F w (Y+6) → SouthEnd F w q)) ∧
      (RootLine F w (10+14*u) (9+14*u) → square F w (28+42*u) (31+42*u)≠73) := by
  obtain ⟨P,w,p,q,odd,fit,iso,coord',step,clean,zero,fr,cap⟩ := front_of_score u F acy score one
  obtain ⟨Q⟩ := flow_of_score u F acy score one
  refine ⟨w,p,q,odd,fit,iso,coord',?_,fun root m => last_line_cap u F w root m cap⟩
  intro big; dsimp only
  refine ⟨fr big,?_⟩
  intro schedule pl dp
  have sched := schedule.elim (fun h => Speed.long_schedule u q h big fit odd) id
  apply to_south_end u q big fit F acy w P step clean _ Q sched (fr big) pl dp
  intro v ne; apply zero; rintro rfl; apply ne; simpa [N] using coord'
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
