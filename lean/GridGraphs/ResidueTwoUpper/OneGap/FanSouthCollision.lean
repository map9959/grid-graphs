import GridGraphs.ResidueTwoUpper.OneGap.FanSpeedTail
import GridGraphs.ResidueTwoUpper.OneGap.FanCollisionWide

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open L7 FanSeed FanSlab ResidueZero Stencil BoundarySix.Connected

/-- For the length-17 center the collision plateau is derived from the
same scored witness. The other center lengths still require the plateau. -/
theorem south_handoff_with_collision_of_score (u : Nat) (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) :
    ∃ (w : View) (p : GridVertex (N u) (N u)) (q : Nat), q%2=1 ∧ q+2≤11+14*u ∧
      (Bonds F).IsIsolated p ∧ coord p=L7.view w (N u) 2 (2+3*q:Nat) ∧
      (57≤q → let Y := (q-15)/6
        Front F w q (11+14*u) (Y+2) (q-3*Y+3) ∧
        ((12≤u ∨ (6≤u ∧ q∉Speed.earlyExceptions u)) →
          (q=6*Y+19 ∨ Plateau F w (Y+2) (Y+6) (q-3*Y+2) (11+14*u)) →
          DeepAfter F w (Y+6) → SouthEnd F w q)) := by
  obtain ⟨P,w,p,q,odd,fit,iso,coord',step,clean,zero,fr,_⟩ :=
    front_rows_with_scan (show NorthOutput from north_output) u F acy score one
  obtain ⟨Q⟩ := flow_of_score u F acy score one
  refine ⟨w,p,q,odd,fit,iso,coord',?_⟩
  have zs : ∀ v, coord v≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P v=0 := by
    intro v ne; apply zero; rintro rfl; apply ne; simpa [N] using coord'
  intro big; dsimp only
  obtain ⟨front,first,second⟩ := fr big
  refine ⟨front,?_⟩
  intro schedule pl dp
  have sched := (Speed.schedule_iff u q big fit odd).mpr schedule
  apply to_south_end u q big fit F acy w P step clean zs Q sched front _ dp
  rcases pl with len | pl
  · exact CollisionWide.plateau17 u q ((q-15)/6) (by omega) len fit F acy w P step clean zs Q first second
  · exact pl
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
