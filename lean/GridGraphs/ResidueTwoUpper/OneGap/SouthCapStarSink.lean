import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStarRows

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero
open scoped Function

/-- An orientation owning every edge exactly once cannot have two sinks
in one connected component. Follow a walk backwards from its known sink. -/
private theorem walk_to_parent_root {V : Type} {G : SimpleGraph V} (P : V → V)
    (covers : ∀ x y, G.Adj x y → (P x=y ↔ P y≠x))
    {x root : V} (fix : P root=root) (w : G.Walk x root) :
    ∃ i : Nat, (P^[i]) x=root := by
  induction w with
  | nil => exact ⟨0,rfl⟩
  | @cons x y z edge w ih =>
    obtain ⟨i,hi⟩ := ih fix
    by_cases xy : P x=y
    · exact ⟨i+1,by rw [Function.iterate_succ_apply,xy,hi]⟩
    · have yx : P y=x := by
        by_contra ne
        exact xy ((covers x y edge).mpr ne)
      cases i with
      | zero =>
        change y=z at hi
        subst y
        exact (edge.ne (yx.symm.trans fix)).elim
      | succ i =>
        exact ⟨i,by simpa only [Function.iterate_succ_apply,yx] using hi⟩

theorem scored_se_marked {u F v}
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) : seSite u v∈F := by
  apply corners_marked u F acy score
  have eq : coord (seSite u v)=L7.view v (35+42*u:Nat) (34+42*u:Nat) (34+42*u:Nat) :=
    coord_onSite ..
  unfold Stencil.isCorner
  cases v with | mk a b s =>
    cases a <;> cases b <;> cases s <;>
      simp [coord,L7.view,L7.reflect,Prod.mk.injEq] at eq <;> omega

/-- For the scored forest every active vertex lies in the component
of the southeast root. A nonroot sink therefore has no forced edge. -/
theorem physical_nonroot_sink_isolated {u F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (x : Site u)
    (ne : x≠seSite u v) (sink : H.parent x=x) :
    (Bonds F).IsIsolated x := by
  intro y edge
  have fromRoot := all_marks_reachable u F acy score (seSite u v) (scored_se_marked acy score)
  have active := (all_active_reachable u F acy score edge).1
  obtain ⟨w⟩ := active.symm.trans fromRoot
  obtain ⟨i,hit⟩ := walk_to_parent_root H.parent H.covers H.root w
  exact ne ((Function.iterate_fixed sink i).symm.trans hit)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
