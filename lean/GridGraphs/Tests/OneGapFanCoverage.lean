import GridGraphs.ResidueTwoUpper.OneGap.FanRoot
import GridGraphs.ResidueTwoUpper.OneGap.FanFringe
import GridGraphs.ResidueTwoUpper.OneGap.FanStep
import GridGraphs.ResidueTwoUpper.OneGap.FanBootScore

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
open BoundarySix.Connected ResidueZero

/-- Enumerate the actual longitudinal isolate offsets (the centered
site is i+1) for the two pre-119 sides, using the physical score seed. -/
theorem early_offsets (u : Nat) (hu : u≤1) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) :
    ∃ (p : GridVertex (35+42*u) (35+42*u)) (w : L7.View) (s f : Bool) (d : Nat),
      d∈(if u=0 then [5,11,17,23,29] else [5,11,17,23,29,35,41,47,53,59,65,71]) ∧
      (Bonds F).IsIsolated p ∧ L7.rim F w s f ∧ coord p=L7.view w (35+42*u:Nat) 2 d ∧ tile F w 1 (d-1)=64 := by
  obtain ⟨p,w,s,f,i,iso,rim,pos,lo,hi,phase,seed,_⟩ := seed_of_score u F acy score one
  refine ⟨p,w,s,f,i+1,?_,iso,rim,by exact_mod_cast pos,seed⟩
  split <;> simp <;> omega

#print axioms seed_of_score
#print axioms rooted_seed
#print axioms fringe_step
#print axioms cap_of_score
#print axioms early_offsets
#print axioms break_or_cap
#print axioms sealed
#print axioms FanBoot.handoff_of_score
#print axioms GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSlab.physical_step
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
