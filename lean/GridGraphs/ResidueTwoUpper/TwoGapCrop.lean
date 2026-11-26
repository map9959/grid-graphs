import GridGraphs.ResidueTwoUpper.ExceptionalGapReduction

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap
open SimpleGraph

variable {V : Type*}

/-- Delete the perimeter and its incident edges. Keeping its vertices as
isolates avoids any casts in the endpoints of crop walks. -/
def crop (G : SimpleGraph V) (rim : V → Prop) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬rim a ∧ ¬rim b
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

def anchor (rim : V → Prop) (P : V → V) (x : V) := ¬rim x ∧ rim (P x)

theorem unique_anchor {G : SimpleGraph V} {P : V → V} {rim : V → Prop}
    (arr : ∀ a b, G.Adj a b → (P a=b ↔ P b≠a))
    {a b : V} (ha : anchor rim P a) (hb : anchor rim P b)
    (conn : (crop G rim).Reachable a b) : a=b := by
  classical
  let Q (x : V) := if rim (P x) then x else P x
  apply Frame.isolated_fixed Q (G:=crop G rim) _ (by simp [Q,ha.2]) conn (by simp [Q,hb.2])
  intro x y e
  have f : Q x=y ↔ P x=y := by
    unfold Q; split_ifs with h
    · exact iff_of_false e.1.ne (fun eq => e.2.2 (eq ▸ h))
    · rfl
  have g : Q y=x ↔ P y=x := by
    unfold Q; split_ifs with h
    · exact iff_of_false e.1.ne.symm (fun eq => e.2.1 (eq ▸ h))
    · rfl
  rw [f,ne_eq, g]; exact arr _ _ e.1

/-- Along a simple path away from the fixed root the next edge has to
point backwards. Remember only the last crossing into the crop. -/
theorem reaches_anchor {G : SimpleGraph V} {P : V → V} {rim : V → Prop}
    (arr : ∀ a b, G.Adj a b → (P a=b ↔ P b≠a)) {root x : V}
    (fix : P root=root) (bd : rim root) (conn : G.Reachable root x) (interior : ¬rim x) :
    ∃ a, anchor rim P a ∧ (crop G rim).Reachable a x := by
  classical
  let seen (y : V) := rim y ∨ ∃ a, anchor rim P a ∧ (crop G rim).Reachable a y
  have follow {s t : V} (p : G.Walk s t) : p.IsPath → seen s →
      (∀ z∈p.support, G.Adj s z → P s≠z) → seen t := by
    induction p with
    | nil => simp
    | @cons a b c ab tail ih =>
      intro path old blocked
      have back : P b=a := by
        by_contra no
        exact blocked _ (by simp [tail.start_mem_support]) ab ((arr _ _ ab).mpr no)
      apply ih path.of_cons
      · by_cases h : rim b
        · exact Or.inl h
        · right
          by_cases ra : rim a
          · exact ⟨b,⟨h,back ▸ ra⟩,.rfl⟩
          · obtain ⟨v,hv,hc⟩ := old.resolve_left ra
            exact ⟨v,hv,hc.trans (show (crop G rim).Adj a b from ⟨ab,ra,h⟩).reachable⟩
      · intro z hz _ bad
        exact (Walk.cons_isPath_iff ab tail).mp path |>.2 ((bad.symm.trans back) ▸ hz)
  obtain ⟨p,hp⟩ := conn.exists_isPath
  exact (follow p hp (Or.inl bd) (fun _ _ e => by rw [fix]; exact e.ne)).resolve_left interior

open ResidueZero Stencil BoundarySix.Connected

/-- Actual attachment rule at every exceptional width. Every active inner
component has exactly one outward attachment. Among all *physical forced*
rim-to-inner edges, exactly the edge `(v,P v)` is not an outward attachment.
No axis, frame normalization, or lower bound on the exit distance is assumed. -/
theorem crop_of_two_gaps (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) :
    let n := 35+42*u
    ∃ (P : GridVertex n n → GridVertex n n) (v : PerimeterVertex n),
      Frame.exitSet P={v} ∧ (∀ a, patchSlack F a=0) ∧
      (∀ y : PerimeterVertex n, ∀ x, ¬IsGridBoundary x → (Bonds F).Adj y.1 x →
        (P x≠y.1 ↔ y=v ∧ x=P v.1)) ∧
      (∀ x, ¬IsGridBoundary x → (Bonds F).Reachable (nw u) x →
        ∃! a, anchor IsGridBoundary P a ∧ (crop (Bonds F) IsGridBoundary).Reachable a x) := by
  classical
  obtain ⟨P,sink,step,arr,_,d,wd,zero⟩ := single_defect u F acy score
  have corners := corners_marked u F acy score
  have good := Frame.frame_checked Frame.stars_checked Frame.patches_checked u F P acy step corners
    (fun x => by by_cases e : x=d; exact Or.inr (e ▸ wd); exact Or.inl (zero _ e))
  have split := Frame.gap_split (by omega) F P ⟨nw u,Or.inl rfl⟩ corners
    (fun _ _ e => (all_active_reachable u F acy score e).1) sink step arr good d zero
  obtain ⟨_,v,ev,rfl⟩ := split.resolve_left (by omega)
  refine ⟨P,v,ev,fun a => zero (.inr a) (fun h => by cases h),?_,?_⟩
  · intro y x inner edge
    rw [←arr _ _ edge]
    constructor
    · intro e
      have mem : y∈Frame.exitSet P := Finset.mem_filter.mpr ⟨Finset.mem_univ _,e ▸ inner⟩
      have eq : y=v := by simpa [ev] using mem
      exact ⟨eq,eq ▸ e.symm⟩
    · rintro ⟨rfl,rfl⟩; rfl
  · intro x hx reach
    obtain ⟨a,ha,hc⟩ := reaches_anchor arr sink (show IsGridBoundary (nw u) from Or.inl rfl) reach hx
    exact ⟨a,⟨ha,hc⟩,fun b hb => unique_anchor arr hb.1 ha (hb.2.trans hc.symm)⟩

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap
