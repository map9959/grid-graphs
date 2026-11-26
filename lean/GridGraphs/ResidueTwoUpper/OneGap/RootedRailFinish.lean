import GridGraphs.ResidueTwoUpper.OneGap.RootedRailAdvance
import GridGraphs.ResidueTwoUpper.OneGap.EastRailPhysical

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
open ResidueZero L7 FanSlab BoundarySix.Connected

/-- Start at any row at or above the height-14 cut. If the available
rooted suffix can pay three columns per downward step, it cannot
exist. Only the starting row is planted; the last column and its
north attachment at the cut are conclusions of propagation. -/
theorem wide_run_excludes {u y c F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (hk : 59≤11+14*u) (before : y+14≤11+14*u)
    (room : c+3*(11+14*u-2-y)+3≤11+14*u)
    (upper : ∀ i : Nat, c ≤ i → i < 11+14*u →
      tile F v y i=73 ∧ RootLine F v i y)
    (bank : ∀ j a : Nat, y ≤ j → j+2 ≤ 11+14*u → c ≤ a → a+2 ≤ 11+14*u →
      AdmittedWord (word (tile F v) j a)) : False := by
  let k := 11+14*u
  let d := k-2-y
  change c+3*d+3≤k at room
  have stop : y+d=k-2 := by dsimp [d,k]; omega
  have many := advance_suffix (W:=k) (d:=d) acy one
    (by dsimp [d,k]; omega) (by dsimp [k]; omega) upper
    (fun j hj e he a al ar => bank _ _ (by omega) (by dsimp [d,k] at *; omega)
      (by omega) (by omega))
  have row (r i : Nat) (lo : y ≤ r) (hi : r ≤ k-2) (il : k-3 ≤ i) (ir : i < k) :
      tile F v r i=73 ∧ RootLine F v i r := by
    have out := many (r-y) (by dsimp [d]; omega) i (by omega) ir
    rwa [show y+(r-y)=r by omega] at out
  have start := row (k-14) (k-1) (by dsimp [k]; omega) (by omega) (by omega) (by omega)
  have cut : firstRow k 14=1+3*(k-14) := rfl
  obtain ⟨j,jl,escape⟩ := eastRail_escape H acy one hk (by decide : 14≤14) (by decide)
    start.2 start.1
  have idx : cropTiles F v k 14 j (width 14-1)=tile F v (k-14+j) (k-1) := by
    unfold cropTiles tile firstRow firstCol
    have w : width 14=13 := rfl
    rw [w]; congr 1 <;> dsimp [k] at * <;> omega
  rw [idx] at escape
  by_cases mid : j+1<14
  · have m := row (k-14+j) (k-1) (by dsimp [k]; omega) (by omega) (by omega) (by omega)
    exact escape (m.1 ▸ rail_examples.2.2)
  · have bottom := bottom_carry (t:=tile F v) (k-2) (k-3)
      (fun i hi => (row _ _ (by dsimp [k]; omega) le_rfl (by omega) (by omega)).1)
      (fun i hi => bank _ _ (by dsimp [k]; omega) (by omega) (by omega) (by dsimp [k]; omega))
    rw [show k-2+1=k-14+j by omega,show k-3+2=k-1 by omega] at bottom
    rcases bottom with b|b
    · rw [b] at escape; exact escape rail_examples.2.1
    · rw [b] at escape; exact escape rail_examples.2.2

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
