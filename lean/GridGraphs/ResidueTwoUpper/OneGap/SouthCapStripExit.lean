import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPhysicalStar
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripProjection

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7

/-- Either a walk reaches its goal in the retained graph or it first
crosses a cut at a vertex reachable entirely in that graph. -/
theorem reaches_or_crosses {V : Type} {G : SimpleGraph V} {S : Set V} {x root : V}
    (w : G.Walk x root) (hx : x∈S) :
    (∃ hr : root∈S, (G.induce S).Reachable ⟨x,hx⟩ ⟨root,hr⟩) ∨
    ∃ (a : S) (b : V), b∉S ∧ G.Adj a b ∧ (G.induce S).Reachable ⟨x,hx⟩ a := by
  induction w with
  | nil => exact .inl ⟨hx,.rfl⟩
  | @cons x y root edge suffix ih =>
    by_cases hy : y∈S
    · rcases ih hy with ⟨hr,reached⟩|⟨a,b,hb,ab,reached⟩
      · have next : (G.induce S).Adj ⟨x,hx⟩ ⟨y,hy⟩ := edge
        exact .inl ⟨hr,next.reachable.trans reached⟩
      · have next : (G.induce S).Adj ⟨x,hx⟩ ⟨y,hy⟩ := edge
        exact .inr ⟨a,b,hb,ab,next.reachable.trans reached⟩
    · exact .inr ⟨⟨x,hx⟩,y,hy,edge,.rfl⟩

theorem first_crossing {V : Type} {G : SimpleGraph V} {S : Set V} {x root : V}
    (w : G.Walk x root) (hx : x∈S) (hout : root∉S) :
    ∃ (a : S) (b : V), b∉S ∧ G.Adj a b ∧ (G.induce S).Reachable ⟨x,hx⟩ a :=
  (reaches_or_crosses w hx).resolve_left (fun ⟨h,_⟩ => hout h)

/-- In the scored forest, any marked component of a scan prefix whose
southeast root is outside the prefix has a genuine cut-crossing edge.
This is the graph-theoretic input to the frontier's closure test. -/
theorem scored_prefix_crossing {u F v} (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) (S : Set (Site u))
    (rootOut : seSite u v∉S) (x : S) (mark : x.val∈F) :
    ∃ (a : S) (b : Site u), b∉S ∧ (Bonds F).Adj a b ∧
      ((Bonds F).induce S).Reachable x a := by
  have fromRoot := all_marks_reachable u F acy score (seSite u v) (scored_se_marked acy score)
  have fromX := all_marks_reachable u F acy score x.val mark
  obtain ⟨p⟩ := fromX.symm.trans fromRoot
  exact first_crossing p x.2 rootOut

/-- Boundary classification is enough for the component-closure
condition: each marked component meets a frontier, an open side, or a
wired contact. The classification takes whole forced edges as input;
it need not assume that the endpoint on the cut is itself marked. -/
theorem scored_prefix_component_hit {u F v} (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) (S : Set (Site u))
    (frontier openSide wired : S → Prop)
    (rootOut : seSite u v∉S)
    (cut : ∀ (a : S) (b : Site u), b∉S → (Bonds F).Adj a b →
      frontier a ∨ openSide a ∨ wired a)
    (x : S) (mark : x.val∈F) :
    ∃ a : S, ((Bonds F).induce S).Reachable x a ∧ (frontier a ∨ openSide a ∨ wired a) := by
  obtain ⟨a,b,hb,e,p⟩ := scored_prefix_crossing acy score S rootOut x mark
  exact ⟨a,p,cut a b hb e⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
