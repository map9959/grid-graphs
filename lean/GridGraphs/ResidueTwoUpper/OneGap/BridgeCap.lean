import GridGraphs.ResidueTwoUpper.OneGap.BridgeChecks
import GridGraphs.ResidueTwoUpper.OneGap.LargeScoredRoute
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEastAll

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open L7 FanSeed FanSlab Camera Port ResidueZero Stencil BoundarySix.Connected SouthCap
open SouthCap.Strip.GridScan

/-- Budgets for the 34, 48, 20 row route. At the cap the final plain
column is usable even though it cannot carry the next dangling seal. -/
def bridgeRoom (k q : Nat) : Prop :=
  let Y := (q-15)/6; let f := q-3*Y+3; let y := Y+6
  let h := k-(y+102)
  57≤q ∧ f+65≤k ∧ f+48≤q ∧ y+116≤k ∧ h≤43 ∧ f+47+width h≤k
instance (k q) : Decidable (bridgeRoom k q) := by unfold bridgeRoom; infer_instance

theorem exclude_bridge {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (feet : q+2≤11+14*u)
    (ok : bridgeRoom (11+14*u) q) :
    let Y := (q-15)/6
    Front F v q (11+14*u) (Y+2) (q-3*Y+3) →
    Plateau F v (Y+2) (Y+6) (q-3*Y+2) (11+14*u) → False := by
  intro Y fr pl
  let k := 11+14*u; let f := q-3*Y+3; let y := Y+6; let h := k-(y+102)
  change 57≤q ∧ f+65≤k ∧ f+48≤q ∧ y+116≤k ∧ h≤43 ∧ f+47+width h≤k at ok
  obtain ⟨big,xroom,dang,yroom,hi,space⟩ := ok
  have hk : 59≤k := by omega
  obtain ⟨Q⟩ := flow_of_score u F acy score one
  have price := prices_of_seed u q F acy v H.parent H.step H.patches H.stars
  have move {r a W D b s rounds : Nat} (pass : test W D b s rounds true)
      (bounds : s<D ∧ b<W) (row : 4≤r ∧ r+D+8≤k) (col : 7≤a ∧ a+W+8≤k)
      (wide : a+3*((D-1)/4)+(D-1)%4+8≤k) (tips : a+W≤q)
      (birth : (q:Int)-a+3≤3*(r:Int)) (front : Front F v q k r a) :=
    physical_dangling_step_rect u q r a W D b s rounds pass bounds (by dsimp [k] at *; omega)
      tips (by omega) F acy v H.parent H.step H.patches H.stars Q
      (Departure.straight_of_room H acy one score (by omega) Q price front le_rfl row.1 col.1
        row.2 col.2 wide feet) front
  have birth : (q:Int)-f+3≤3*(y:Int) := by dsimp [f,y,Y]; omega
  have yl : 4≤y := by dsimp [y]; omega
  have fl : 7≤f := by dsimp [f,Y]; omega
  have base : Front F v q k y f := advance_front F v (by omega) le_rfl (by omega)
    (fun t st rt => by dsimp [f,y,Y] at *; omega) fr pl
  have a := move bridge_test (by decide) (by omega) (by omega) (by omega) (by omega) birth base
  have b := move extended_test (by decide) (by omega) (by omega) (by omega) (by omega)
    (by push_cast; omega) a.1
  have c := move medium_test (by decide) (by omega) (by omega) (by omega) (by omega)
    (by push_cast; omega) b.1
  have lo : 14≤h := by dsimp [h]; omega
  have endRow : k-h=y+34+48+20 := by dsimp [h]; omega
  obtain ⟨rounds,rejected⟩ := eastRange_empty h lo hi
  apply east_empty_excludes H acy one score hk lo hi _ _ rounds rejected
  · change RootLine F v (k-1) (k-h); rw [endRow]
    exact c.1.2.2 _ (by omega) (by omega) (by omega)
  · intro i st en
    change square F v (1+3*(k-h)) (1+3*i)=73; rw [endRow]
    exact c.2 _ (by omega) le_rfl i (by omega) en
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
