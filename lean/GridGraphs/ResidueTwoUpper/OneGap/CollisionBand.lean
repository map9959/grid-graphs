import GridGraphs.ResidueTwoUpper.OneGap.FanCollisionWide
import GridGraphs.ResidueTwoUpper.OneGap.CollisionReach
import GridGraphs.ResidueTwoUpper.OneGap.CornerCone
import GridGraphs.ResidueTwoUpper.OneGap.LatchedBand
import GridGraphs.ResidueTwoUpper.OneGap.ShortSeed

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.CollisionWide
open ResidueZero Stencil L7 FanSlab FanSeed Camera Short BoundarySix.Connected SouthCap
open SouthCap.Strip.GridScan.Rooted.Buffered
local notation "TILE" => SouthCap.Strip.GridScan.Rooted.tile

/-- The collision chart alone need not force 73. Its four-mask
readout joins the eastern catalogue band; a single actual north
line at its east end then forces the plateau, for every center length. -/
theorem plateau_with_guard {u F w q} (H : PhysicalHalo u F w q (fanDirection u w))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) {P} (S : Short.Seed F P w q) (big : 57≤q)
    (Y : Nat) (defY : Y=(q-15)/6) (Q : Flow F)
    (first : Known u q Y F w) (second : Known u q (Y+1) F w)
    (front : Front F w q (11+14*u) (Y+2) (q-3*Y+3)) :
    Plateau F w (Y+2) (Y+reach (q-6*Y)) (q-3*Y+2) (11+14*u) ∧ PriorCut F w (Y+6) (q-3*Y+3) := by
  let k := 11+14*u
  let g := q-3*Y+2
  let l := q-6*Y
  have rb := reach_bounds l
  have odd := S.odd
  have fit := S.room
  have len : l∈[15,17,19] := by simp; dsimp [l]; omega
  have mid : q=6*Y+l := by dsimp [l]; omega
  obtain ⟨X,agree,kept,sq⟩ := physical_chart u q Y l (by omega) len mid fit F acy w P S.step
    S.clean (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero) Q first second
  have localMasks (j i : Nat) (lo : Y+2≤j) (hi : j≤Y+reach l) (il : g-1 ≤ i) (ih : i≤g) :
      bandMask (TILE F w j i) := by
    let z := j-Y; let b := i-(g-1)
    have ck := reach_read len X agree kept (z:=z) (b:=b) (by dsimp [z]; omega)
      (by dsimp [z]; omega) (by dsimp [b,g] at *; omega)
    unfold member4 at ck
    rw [sq,show 1+3*Y+3*z=1+3*j by dsimp [z]; omega,
      show 1+3*(3*Y+2)+3*(l-1+b)=1+3*i by dsimp [b,g,l] at *; omega] at ck
    exact ck
  have base := first_collision u q Y (by omega) (by omega) fit F acy w P S.step S.clean
    (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero) first second
  have state (j : Nat) (lo : Y+2≤j) (hi : j≤Y+reach l) :
      (∀ i, g ≤ i → i<k → TILE F w j i=73) ∧ RootLine F w (k-1) j := by
    induction j,lo using Nat.le_induction with
    | base =>
      exact ⟨base _ (by omega) le_rfl,front.2.2 _ (by dsimp [k]; omega)
        (by dsimp [k]; omega) (by dsimp [k]; omega)⟩
    | succ j jl ih =>
      obtain ⟨old,path⟩ := ih (by omega)
      have last := old (k-1) (by dsimp [g,k]; omega) (by dsimp [k]; omega)
      have line : RootLine F w (k-1) (j+1) := by
        apply SouthCap.Strip.GridScan.Rooted.extend_line path
        · rw [last]; decide
        · left; rw [last]; decide
      have far := (CornerCone.step_head H acy one score (by omega) (by omega : 4≤j)
        (by dsimp [g]; omega : 5≤g) (by omega) (by dsimp [g]; omega) old path).2
      have masks (i : Nat) (lo : g-1 ≤ i) (en : i<k) : bandMask (TILE F w (j+1) i) := by
        by_cases west : i≤g
        · exact localMasks _ _ (by omega) hi lo west
        · rw [far i (by omega) en]; decide
      have row : BandRow (TILE F w) (j+1) (g-1) k := by
        intro i il ir
        exact physical_pair H acy score (by omega) (by omega) (by dsimp [g] at *; omega)
          (by omega) ir (masks _ il (by omega)) (masks _ (by omega) (by omega))
      refine ⟨?_,line⟩
      intro i il ir
      rcases rigid H acy one score (by omega) (by omega) (by omega)
          (by dsimp [g]; omega) (by dsimp [g]; omega) row line i (by omega) ir with m|⟨e,_⟩
      · exact m
      · dsimp [g] at *; omega
  have pl : Plateau F w (Y+2) (Y+reach l) g k := fun j lo hi => (state j lo hi).1
  refine ⟨pl,by omega,Y+2,by omega,by omega,(fun j lo hi i il h => pl j lo (by omega) i (by dsimp [g]; omega) h),?_⟩
  intro i l h
  refine ⟨?_,pl _ le_rfl (by omega) _ (by dsimp [g]; omega) (by dsimp [k]; omega)⟩
  by_cases inside : g ≤ i-2
  · rw [pl _ le_rfl (by omega) _ inside (by dsimp [k]; omega)]; decide
  · have m := localMasks (Y+2) (i-2) le_rfl (by omega) (by dsimp [g]; omega) (by omega)
    intro E; change TILE F w (Y+2) (i-2)=2 at E; rw [E] at m; contradiction

theorem plateau_all {u F w q} (H : PhysicalHalo u F w q (fanDirection u w))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) {P} (S : Short.Seed F P w q) (big : 57≤q)
    (Y : ℕ) (defY : Y=(q-15)/6) (Q : Flow F)
    (first : Known u q Y F w) (second : Known u q (Y+1) F w)
    (front : Front F w q (11+14*u) (Y+2) (q-3*Y+3)) :
    Plateau F w (Y+2) (Y+6) (q-3*Y+2) (11+14*u) := by
  have rb := reach_bounds (q-6*Y)
  exact fun j lo hi => (plateau_with_guard H acy one score S big Y defY Q first second front).1 j lo (by omega)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.CollisionWide
