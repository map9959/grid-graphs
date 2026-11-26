import GridGraphs.ResidueTwoUpper.OneGap.MiddleDanglingMove
import GridGraphs.ResidueTwoUpper.OneGap.BridgeCap

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open L7 FanSeed FanSlab Camera Port ResidueZero Stencil BoundarySix.Connected SouthCap
open SouthCap.Strip.GridScan.Rooted

def coneCost (d : Nat) := 3*(d/4)+d%4

/-- For each possible first bad row, either the incoming tooth
survives directly, or an entirely earlier chart can restart its cone. -/
def RestartCover (L E h : Nat) : Prop := ∀ j, 1≤j → j≤h →
  coneCost (j-1)≤E ∨ ∃ W D b s rounds, test W D b s rounds true ∧
    s<D ∧ b<W ∧ D<j ∧ W≤L ∧ b+coneCost (j-1-s)≤E

set_option maxHeartbeats 800000 in
/-- Restart the cone above a putative first departure. Its earlier
straight rows certify an auxiliary move without any assumption on
the offending row. The cover fixes both the furthest tip used (`L`)
and the maximum lateral read (`E`). -/
theorem nested_window {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    (Q : Flow F) (feet : q+2≤11+14*u) {y f : Nat}
    (front : Front F v q (11+14*u) y f) (yl : 4≤y) (fl : 7≤f)
    {w h E L : Nat} (ht : y+h+8≤11+14*u) (space : f+E+7≤11+14*u) (dang : f+L≤q)
    (birth : (q:Int)-f+3≤3*(y:Int)) (we : w≤E) (aux : L≤E) (cover : RestartCover L E h) :
    Straight F v y f w h := by
  let k := 11+14*u
  have price := prices_of_seed u q F acy v H.parent H.step H.patches H.stars
  suffices all : Straight F v y f E h from fun j hj i hi => all j hj i (by omega)
  by_contra neg
  obtain ⟨j,i,bad⟩ := Departure.first_of_bad front le_rfl (by omega) neg
  have jl := bad.1; have jh := bad.2.1
  apply Departure.impossible_arrival H acy score (by omega) Q front le_rfl yl (by omega)
    (by omega) (by omega) bad
  have anchor {s b : Nat} (slt : s<j)
      (top : ∀ a, f+b≤a → a<k → SouthCap.Strip.GridScan.Rooted.tile F v (y+s) a=73)
      (line : RootLine F v (k-1) (y+s))
      (budget : b+3*((j-1-s)/4)+(j-1-s)%4≤E) :
      Departure.WestArrival Q v y f j i := by
    let z := j-1-s
    have mid := CornerCone.blocks H acy one score (by omega) (y:=y+s) (a:=f+b)
      (f:=k-1) (s:=z/4) (by omega) (by omega) (by dsimp [z]; omega)
      (by dsimp [z]; omega) (by dsimp [k,z]; omega) (by dsimp [k]; omega)
      top (fun a l h => by rwa [show a=k-1 by omega])
    have tail := CornerCone.cone H acy one score (by omega) (D:=z%4)
      (by omega) (by omega) (by dsimp [z]; omega) (by dsimp [z]; omega)
      (by dsimp [k,z]; omega) mid.1 mid.2 (by dsimp [k]; omega) (z%4) le_rfl
    rw [show y+s+4*(z/4)+z%4=y+(j-1) by dsimp [z]; omega] at tail
    exact Departure.covered H acy one score (by omega) Q price yl fl ht space bad
      (tail.1 _ (by dsimp [z]; omega) (by omega)) (tail.2 _ le_rfl (by omega))
  have prior {W D b s rounds} (ck : test W D b s rounds true)
      (dims : s<D ∧ b<W) (rows : D<j) (cols : W≤L)
      (budget : b+3*((j-1-s)/4)+(j-1-s)%4≤E) : Departure.WestArrival Q v y f j i := by
    have straight : Straight F v y f W D := fun d dh e eh => bad.2.2.2.2.1 d (by omega) e (by omega)
    have hand := physical_dangling_step_rect u q y f W D b s rounds ck dims (by omega)
      (by omega) (by omega) F acy v H.parent H.step H.patches H.stars Q straight front
    exact anchor (by omega) (hand.2 _ (by omega) le_rfl)
      (hand.1.2.2 _ (by dsimp [k]; omega) (by dsimp [k]; omega) (by dsimp [k]; omega)) budget
  rcases cover j jl jh with early|⟨W,D,b,s,rounds,ck,hs,hb,rows,cols,cost⟩
  · exact anchor (s:=0) (b:=0) (by omega) (front.1 _ le_rfl le_rfl)
      (front.2.2 _ (by dsimp [k]; omega) (by dsimp [k]; omega) (by dsimp [k]; omega))
      (by simpa only [Nat.zero_add,Nat.sub_zero,coneCost] using early)
  · exact prior ck ⟨hs,hb⟩ rows cols (by simpa only [coneCost,Nat.add_assoc] using cost)

theorem nested_straight {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u)
    (Q : Flow F) (feet : q+2≤11+14*u) {y f : Nat}
    (front : Front F v q (11+14*u) y f) (yl : 4≤y) (fl : 7≤f)
    (ht : y+62≤11+14*u) (space : f+35≤11+14*u) (dang : f+19≤q)
    (birth : (q:Int)-f+3≤3*(y:Int)) : Straight F v y f 22 54 := by
  apply nested_window H acy one score (by omega) Q feet front yl fl ht (E:=27) (by omega) dang birth (by decide) (by decide)
  intro j jl jh
  by_cases early : j≤36
  · left; dsimp [coneCost]; omega
  by_cases mid : j≤47
  · exact .inr ⟨_,_,_,_,_,long_test,by decide,by decide,by omega,by decide,by dsimp [coneCost]; omega⟩
  · exact .inr ⟨_,_,_,_,_,middle_test,by decide,by decide,by omega,by decide,by dsimp [coneCost]; omega⟩
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
