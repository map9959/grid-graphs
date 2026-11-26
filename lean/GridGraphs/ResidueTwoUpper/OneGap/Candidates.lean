import GridGraphs.ResidueTwoUpper.OneGap.PatchWindow
import GridGraphs.ResidueTwoUpper.OneGap.Crossing
import GridGraphs.ResidueTwoUpper.OneGap.Grounding
import GridGraphs.ResidueTwoUpper.OneGap.FanIndex

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
open ResidueZero Stencil BoundarySix.Connected

/-- Necessary one-gap interior alternatives, expressed only in terms of
the physical marks.  The origin-grid margin is eight. No choice of a
different orientation, patch mask, or location is made after selecting
the defect. -/
theorem candidates_of_score (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) :
    let n := 35+42*u
    ((∃ v : GridVertex n n, (Bonds F).IsIsolated v ∧
        (arm n (coord v).1 (coord v).2 ∨ arm n (coord v).2 (coord v).1)) ∧
      ∀ a : origins n, patchSlack F a=0) ∨
    (∃ a : origins n, patchSlack F a=full ∧ (∀ b, b≠a → patchSlack F b=0) ∧
      0<GridGraphs.ResidueTwoUpper.Exceptional.Frame.depthAt (n-2) (coord a) ∧
      ((8≤a.1.val ∧ a.1.val+9≤n-2) → (8≤a.2.val ∧ a.2.val+9≤n-2) →
        a.1.val%3=1 ∧ a.2.val%3=1 ∧ (a.1.val+a.2.val)%2=1 ∧
        (maskAt F a).val∈[1,4,64,256])) := by
  obtain ⟨P,st,_,_,h⟩ := defect_sites u F acy score one
  rcases h with ⟨v,iso,loc,_,zero⟩ | ⟨a,deep,site,w,zero⟩
  · exact Or.inl ⟨⟨v,iso,loc⟩,fun b => zero (.inr b) (by simp)⟩
  · refine Or.inr ⟨a,w,fun b hb => zero _ (fun eq => hb (Sum.inr.inj eq)),deep,?_⟩
    intro r c
    obtain ⟨h₁,h₂,mask⟩ := bulk_patch u F acy P st a w zero (by omega) (by omega)
    have odd := odd_bulk_origin u a (maskAt F a) (by omega) (by omega) ⟨h₁,h₂⟩ mask site
    exact ⟨h₁,h₂,odd,by simpa [PatchFilter.singletonCorner,Bool.or_eq_true,or_assoc] using mask⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
