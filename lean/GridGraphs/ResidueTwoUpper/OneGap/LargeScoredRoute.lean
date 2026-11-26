import GridGraphs.ResidueTwoUpper.OneGap.DepartureRim
import GridGraphs.ResidueTwoUpper.OneGap.FanSpeedTail
import GridGraphs.ResidueTwoUpper.OneGap.RoomyIndices
import GridGraphs.ResidueTwoUpper.OneGap.ExtendedDanglingMove

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open L7 FanSeed FanSlab Camera Port ResidueZero Stencil BoundarySix.Connected SouthCap

/-- Room on the schedule supplies the entire widened first-departure
test at every step, so there is no blocked-move premise here. -/
theorem roomy_south_end {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    (big : 57≤q) (feet : q+2≤11+14*u)
    (route : Speed.ExtendedRoute (11+14*u) q (Speed.start (11+14*u) q)) :
    let Y := (q-15)/6
    Front F v q (11+14*u) (Y+2) (q-3*Y+3) →
    Plateau F v (Y+2) (Y+6) (q-3*Y+2) (11+14*u) → SouthEnd F v q := by
  intro Y fr pl
  let k := 11+14*u
  let claim := fun p : Speed.State =>
    p.1≤k → 4≤k-p.1 → 7≤p.2 → (q:Int)-p.2+3≤3*((k-p.1:Nat):Int) →
      Front F v q k (k-p.1) p.2 → SouthEnd F v q
  obtain ⟨Q⟩ := flow_of_score u F acy score one
  have price := prices_of_seed u q F acy v H.parent H.step H.patches H.stars
  have go (p : Speed.State) (path : Speed.ExtendedRoute k q p) : claim p := by
    induction path with
    | capEnd p cap => intro _ _ _ _ front; exact ⟨_,_,cap,front⟩
    | via p m mem fit wide _ ih =>
      intro hp hy hf birth front
      let y := k-p.1; let x := Speed.x m q p.2
      have move : m.s ≤ m.height ∧ 1 ≤ m.width ∧ 1 ≤ m.height := by
        simp [Speed.moves] at mem; rcases mem with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      have left : p.2≤x := by dsimp [x,Speed.x]; split <;> omega
      have ww := fit.1; have hh := fit.2.2
      change x+m.width+7≤k at ww
      have straight := Departure.straight_of_room H acy one score (by omega) Q price front left hy hf
        (W:=m.width-1) (h:=m.height-1) (by omega) (by omega) wide feet
      have hand : Front F v q k (y+m.s) (x+m.d) := by
        rcases List.mem_cons.mp mem with rfl|old
        · change p.2+23+7≤k at ww
          change 55+7≤p.1 at hh
          have dang := fit.2.1 rfl
          change p.2+23≤q+1 at dang
          exact physical_dangling_step u q y p.2 22 54 21 48 16 extended_test
            (by decide) (by dsimp [y,k] at *; omega) (by omega) (by dsimp [y]; omega)
            F acy v H.parent H.step H.patches H.stars Q straight front
        · exact (advance_fitted acy v H.parent H.step H.patches H.stars Q old fit hp
            (by omega) hy birth front straight).1
      have row : k-(Speed.next m q p).1=y+m.s := by dsimp [Speed.next,y]; omega
      apply ih (by dsimp [Speed.next]; omega) (by rw [row]; dsimp [y]; omega) (by change 7≤x+m.d; omega)
      · change (q:Int)-(x+m.d:Nat)+3≤3*((k-(Speed.next m q p).1:Nat):Int); rw [row]
        dsimp [y]; omega
      · change Front F v q k (k-(Speed.next m q p).1) (x+m.d); rw [row]; exact hand
  have front := advance_front F v (by omega) le_rfl (by omega)
    (fun t st rt => by push_cast at *; omega) fr pl
  have start := go _ route
  dsimp only [claim,Speed.start] at start
  change k-(Y+6)≤k → 4≤k-(k-(Y+6)) → 7≤q-3*Y+3 →
    (q:Int)-(q-3*Y+3:Nat)+3≤3*((k-(k-(Y+6)):Nat):Int) →
    Front F v q k (k-(k-(Y+6))) (q-3*Y+3) → SouthEnd F v q at start
  rw [show k-(k-(Y+6))=Y+6 by dsimp [k,Y]; omega] at start
  exact start (by omega) (by omega) (by dsimp [Y]; omega) (by push_cast; dsimp [Y]; omega) front
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
