import GridGraphs.ResidueTwoUpper.OneGap.NestedDeparture

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open L7 FanSeed FanSlab Camera Port ResidueZero Stencil BoundarySix.Connected SouthCap
open SouthCap.Strip.GridScan

/-- Any number of nested transfers. Keep the extra plain column at
every handoff, so the terminal cap does not need a seal on that column. -/
def nestedRoom (k q : Nat) : Prop :=
  let Y := (q-15)/6; let y := Y+6; let f := q-3*Y+3
  let m := (k-(y+14))/48; let h := k-(y+48*m)
  57≤q ∧ 0 < m ∧ 14 ≤ h ∧ h≤43 ∧ f+22*(m-1)+35≤k ∧ f+22*m≤q ∧
    f+22*m-1+width h≤k
instance (k q) : Decidable (nestedRoom k q) := by unfold nestedRoom; infer_instance

theorem exclude_nested {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (feet : q+2≤11+14*u)
    (ok : nestedRoom (11+14*u) q) :
    let Y := (q-15)/6
    Front F v q (11+14*u) (Y+2) (q-3*Y+3) →
    Plateau F v (Y+2) (Y+6) (q-3*Y+2) (11+14*u) → False := by
  intro Y fr pl
  let k := 11+14*u; let f := q-3*Y+3; let y := Y+6
  let m := (k-(y+14))/48; let h := k-(y+48*m)
  change 57≤q ∧ 0 < m ∧ 14 ≤ h ∧ h≤43 ∧ f+22*(m-1)+35≤k ∧ f+22*m≤q ∧ f+22*m-1+width h≤k at ok
  obtain ⟨big,pos,lo,hi,space,tips,cap⟩ := ok
  have hk : 59≤k := by omega
  have base : Front F v q k y f := advance_front F v (by omega) le_rfl (by omega)
    (fun t st rt => by dsimp [f,y,Y] at *; omega) fr pl
  have yl : 4≤y := by dsimp [y]; omega
  have fl : 7≤f := by dsimp [f,Y]; omega
  have birth : (q:Int)-f+3≤3*(y:Int) := by dsimp [f,y,Y]; omega
  have height : y+48*m+14≤k := by dsimp [h] at lo; omega
  obtain ⟨Q⟩ := flow_of_score u F acy score one
  have go (t : Nat) (bound : t ≤ m) :
      Front F v q k (y+48*t) (f+22*t) ∧
      Plateau F v (y+48*t) (y+48*t) (f+22*t-1) k := by
    induction t with
    | zero =>
      exact ⟨base,fun r rl rh i il ih => pl r (by dsimp [y] at *; omega) rh i
        (by dsimp [f] at il; omega) ih⟩
    | succ t ih =>
      have cur := (ih (by omega)).1
      have born : (q:Int)-(f+22*t:Nat)+3≤3*((y+48*t:Nat):Int) := by push_cast; omega
      have st := nested_straight H acy one score hk Q feet cur (by omega) (by omega)
        (by omega) (by omega) (by omega) born
      have next := physical_dangling_step_rect u q (y+48*t) (f+22*t) 22 54 21 48 16
        extended_test (by decide) (by dsimp [k] at *; omega) (by omega) (by omega)
        F acy v H.parent H.step H.patches H.stars Q st cur
      rw [show y+48*(t+1)=y+48*t+48 by omega,show f+22*(t+1)=f+22*t+21+1 by omega]
      exact ⟨next.1,fun r rl rh i il ih => next.2 r (by omega) rh i il ih⟩
  obtain ⟨last,plain⟩ := go m le_rfl
  have endRow : k-h=y+48*m := by dsimp [h]; omega
  obtain ⟨rounds,rejected⟩ := eastRange_empty h lo hi
  apply east_empty_excludes H acy one score hk lo hi _ _ rounds rejected
  · change RootLine F v (k-1) (k-h); rw [endRow]
    exact last.2.2 _ (by omega) (by omega) (by omega)
  · intro i il ih; change square F v (1+3*(k-h)) (1+3*i)=73; rw [endRow]
    exact plain _ le_rfl le_rfl i (by omega) ih
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
