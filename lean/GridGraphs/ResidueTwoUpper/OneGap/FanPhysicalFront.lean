import GridGraphs.ResidueTwoUpper.OneGap.FanHistorySeed
import GridGraphs.ResidueTwoUpper.OneGap.FanCollision

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSlab FanSeed BoundarySix.Connected

/-- For the very same oriented witness used by the mask checks: propagate
all its north feet and sealed birth lines through the first collision row. -/
theorem front_rows_from_seed (scan : NorthOutput) (u q : Nat) (big : 57≤q) (fit : q+2≤11+14*u) (odd : q%2=1)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic) (w : View) (s f : Bool) (side : rim F w s f)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (west : WestTeeth u q F w) (core : tile F w 1 (1+3*q)=64) (east : ∀ i, q< i → i<11+14*u → tile F w 1 (1+3*i)=72) :
    let Y := (q-15)/6
    Front F w q (11+14*u) (Y+2) (q-3*Y+3) ∧ Known u q Y F w ∧ Known u q (Y+1) F w := by
  let Y := (q-15)/6; have room : 6*Y+15≤q ∧ q≤6*Y+20 := by dsimp [Y]; omega
  have hy : 6≤Y := by dsimp [Y]; omega
  have R := north_rows scan u q big fit odd F acy w P step clean zero west core east
  have pair := through_handoff u q big fit F acy P step clean w zero (rows_from_teeth u q big fit odd F acy P step clean w zero west core east) Y hy le_rfl
  have pl := first_collision u q Y hy room fit F acy w P step clean zero pair.1 pair.2
  let start := q-3*Y+3
  have h : Front F w q (11+14*u) (Y+1) start := by
    refine ⟨fun j lo hi i le lt => pl j lo (by omega) i (by dsimp [start] at le; omega) lt,?_,?_⟩
    · intro t st en rt; have D := dangling_at_handoff (35+42*u) q Y t hy room.1 (by omega) st rt F w R
      simpa only [Seal,Nat.cast_add,Nat.cast_one] using D
    · intro t st en rt; exact rooted_at_handoff F w s f side rt (by omega) big room.1 R
  exact ⟨advance_front F w (by omega) le_rfl (by omega)
    (fun t st rt => by push_cast; omega) h pl, pair⟩

/-- Separate the score normalization from the finite six-row history
replay; retain the parent field and all local charges for later windows. -/
theorem front_rows_with_scan (scan : NorthOutput) (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) :
    let n := 35+42*u
    ∃ (P : GridVertex n n → GridVertex n n) (w : View) (p : GridVertex n n) (q : Nat),
      q%2=1 ∧ q+2≤11+14*u ∧ (Bonds F).IsIsolated p ∧ coord p=L7.view w n 2 (2+3*q:Nat) ∧
      (∀ t,P t≠t → (Bonds F).Adj t (P t)) ∧ (∀ a,patchSlack F a=0) ∧ (∀ t,t≠p → starSlack F P t=0) ∧
      (57≤q → let Y := (q-15)/6
        Front F w q (11+14*u) (Y+2) (q-3*Y+3) ∧ Known u q Y F w ∧ Known u q (Y+1) F w) ∧
      (tile F (FanSeed.opposite w) 4 (31+42*u)=73 → ∃ r,5≤r ∧ r<29+42*u ∧
        marked F (L7.view w n r (31+42*u:Nat))=false ∧ marked F (L7.view w n (r+1:Nat) (31+42*u:Nat))=false) := by
  obtain ⟨P,p,w,s,f,i,step,clean,zero,iso,side,pos,lo,hi,phase,core,east⟩ := scored_seed u F acy score one
  let q := (i-1)/3; have qi : i=1+3*q := by dsimp [q]; omega
  have atStar : coord p=L7.view w (35+42*u:Nat) 2 (2+3*q:Nat) := by rw [pos]; congr 1; push_cast; omega
  refine ⟨P,w,p,q,by omega,by omega,iso,atStar,step,clean,zero,?_,?_⟩
  · intro big; have atStar' := atStar; push_cast at atStar'
    have zs (t) (ne : coord t≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat)) : starSlack F P t=0 := zero t (fun e => ne (by rw [e]; exact_mod_cast atStar))
    have paid : tile F w 1 (1+3*q)=64 := qi ▸ core
    have teeth := Teeth.west_teeth u q (by omega) (by omega) F acy score one w s f side P step clean zs
      (by rw [←tile_eq F w (by omega)]; exact paid)
    exact front_rows_from_seed scan u q big (by omega) (by omega) F acy w s f side P step clean zs teeth paid
      (fun j lt hj => (east (1+3*j) (by omega) (by omega) (by omega)).1)
  · intro cap; have last := east (31+42*u) (by omega) (by omega) (by omega)
    exact break_or_cap u F acy score one clean w s f side last.1 last.2.1 cap
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
