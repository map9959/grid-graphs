import GridGraphs.ResidueTwoUpper.ExceptionalPerimeter
import GridGraphs.ResidueTwoUpper.ExceptionalFrameReplay

namespace GridGraphs.ResidueTwoUpper.Exceptional.Frame
open ResidueZero Stencil BoundarySix.Connected

/-- Uniform necessary physical frame for the exceptional score. The same
orientation witnesses the corner/side rules, the sole charge and the exit. -/
theorem frame_of_score (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) :
    let n := 35+42*u
    ∃ (P : GridVertex n n → GridVertex n n) (d : occurrence n),
      (∀ x, P x≠x → (Bonds F).Adj x (P x)) ∧
      (∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) ∧
      weightAt F P d=full ∧ (∀ x, x≠d → weightAt F P x=0) ∧
      (∀ x, allGood F P x) ∧
      (((perimeterHoles F).card=1 ∧ exitSet P=∅) ∨
       ((perimeterHoles F).card=2 ∧ ∃ v : PerimeterVertex n, exitSet P={v} ∧ d=Sum.inl v.1)) := by
  obtain ⟨P,sink,step,arr,_,d,wd,zero⟩ := single_defect u F acy score
  have corners := corners_marked u F acy score
  have good := frame_checked stars_checked patches_checked u F P acy step corners (fun x => by
    by_cases eq : x=d
    · exact Or.inr (eq ▸ wd)
    · exact Or.inl (zero _ eq))
  exact ⟨P,d,step,arr,wd,zero,good,gap_split (by omega) F P ⟨nw u,Or.inl rfl⟩ corners
    (fun _ _ e => (all_active_reachable u F acy score e).1) sink step arr good d zero⟩

end GridGraphs.ResidueTwoUpper.Exceptional.Frame
