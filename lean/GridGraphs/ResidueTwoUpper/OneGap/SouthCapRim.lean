import GridGraphs.ResidueTwoUpper.OneGap.L7Rim
import GridGraphs.ResidueTwoUpper.ExceptionalGapReduction

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero Stencil GridGraphs.ResidueTwoUpper.Exceptional.Frame BoundarySix.Connected TwoGap.Words L7 Finset

/-- At a closed corner there are two possible words, not one. The
catalogue for the southern crop must handle both or justify fixing one. -/
theorem closed_word {n : Nat} (hn : 35≤n) (F : Finset (GridVertex n n)) (c : Corner)
    (word : physicalWord hn F c ∈ [3,7,12,13])
    (closed : ∀ b, (c,b)∉gaps hn F) :
    physicalWord hn F c=7 ∨ physicalWord hn F c=13 := by
  have a := closed false
  have b := closed true
  unfold physicalWord bits at word ⊢
  simp only [gaps,mem_filter,mem_univ,true_and] at a b
  by_cases p : (atArm hn (c,false) 1).1∈F <;> by_cases q : (atArm hn (c,false) 2).1∈F <;>
    by_cases r : (atArm hn (c,true) 1).1∈F <;> by_cases s : (atArm hn (c,true) 2).1∈F <;>
    simp_all

/-- The southeast corner opposite the origin of the normalized fan
is closed. Only the two missing rim bits and the one-gap count are used;
this result neither advances the fan nor constructs `SouthEnd`. -/
theorem southeast_closed {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (w : View) (s f : Bool) (frame : rim F w s f) :
    let hn : 35≤35+42*u := by omega
    let c : Corner := (!w.rowFar,!w.colFar)
    (∀ b, (c,b)∉gaps hn F) ∧ (physicalWord hn F c=7 ∨ physicalWord hn F c=13) := by
  dsimp only
  let hn : 35≤35+42*u := by omega
  obtain ⟨P,_,step,_,_,_,good,_⟩ := frame_of_score u F acy score
  rw [exact_holes hn F (corners_marked u F acy score) (fun x => (star_geometry hn F P step x (good (.inl x))).1),
    Finset.card_image_of_injective _ (gapEdge_inj hn)] at one
  let t := if s then !w.swap else w.swap
  have un (i : Fin 3) (hi : i.val=1 ∨ i.val=2) : (atArm hn (L7.corner w,t) i).1∉F := by
    have E : coord (atArm hn (L7.corner w,t) i).1=L7.view w (35+42*u:Nat)
        (if s then (i.val:Int) else 0) (if s then 0 else (i.val:Int)) := by
      cases w with | mk x y z => cases x <;> cases y <;> cases z <;> cases s <;>
        ext <;> simp [L7.corner,t,coord,atArm,loc,L7.view,reflect] <;> omega
    have Z : marked F (coord (atArm hn (L7.corner w,t) i).1)=false := by
      rw [E]; cases s
      · exact frame 0 i.val (by decide) (by omega) false (by simp [preset,hi])
      · exact frame i.val 0 (by omega) (by omega) false (by simp [preset,hi,show i.val≠0 by omega])
    simpa [marked_at] using Z
  have gap : (L7.corner w,t)∈gaps hn F :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,un 1 (.inl rfl),un 2 (.inr rfl)⟩
  have closed : ∀ b, ((!w.rowFar,!w.colFar),b)∉gaps hn F := by
    intro b h
    obtain ⟨a,e⟩ := Finset.card_eq_one.mp one
    rw [e,Finset.mem_singleton] at h gap
    have bad := congrArg (fun x : Arm => x.1.1) (h.trans gap.symm)
    change (!w.rowFar)=w.rowFar at bad
    exact (show ∀ b : Bool, (!b) ≠ b by decide) _ bad
  exact ⟨closed,closed_word hn F _ (physicalWord_ok hn F P good _) closed⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
