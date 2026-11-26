import GridGraphs.ResidueTwoUpper.OneGap.RootedRailAdvance

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
open ResidueZero L7 FanSlab BoundarySix.Connected

theorem cap_word {u h F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (hk : 59≤11+14*u) (hi : h≤43) (r c : Nat) (rl : r+2≤h) (cl : c+2≤width h) :
    AdmittedWord (word (tile F v) (11+14*u-h+r) (11+14*u-width h+c)) := by
  let k := 11+14*u
  let w := word (tile F v) (k-h+r) (k-width h+c)
  have ok := physical_catalogue_admitted H acy score hk hi r c rl cl
  have same : widened ordinary (endTag h r) (endTag (width h) c) w := by
    simpa only [w,word,tile,firstRow,firstCol,Nat.mul_add,Nat.mul_one,Nat.add_assoc,k] using ok
  have lt (a b : Nat) : tile F v a b<512 := (unpack _).1
  have good : FitsWord w := ⟨lt ..,lt ..,lt ..,lt ..⟩
  have m := bankWords_cover good same
  have rt := tag_range rl
  have ct := tag_range cl
  let a : Fin 7 := ⟨endTag h r-6,by omega⟩
  let b : Fin 7 := ⟨endTag (width h) c-6,by omega⟩
  refine ⟨a,b,?_⟩
  rwa [show 6+a.val=endTag h r by dsimp [a]; omega,
    show 6+b.val=endTag (width h) c by dsimp [b]; omega]

/-- Actual scored-board version: the only planted facts are on the
incoming four tiles. In particular no catalogue or propagation
condition is assumed below them. -/
theorem physical_advance_four {u h F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u) (hi : h≤43)
    (r c : Nat) (rl : r+3≤h) (cl : c+4≤width h) :
    let y := 11+14*u-h+r
    let x := 11+14*u-width h+c
    (∀ i≤3, tile F v y (x+i)=73 ∧ RootLine F v (x+i) y) →
      tile F v (y+1) (x+3)=73 ∧ RootLine F v (x+3) (y+1) := by
  intro y x upper
  have w : width h≤11+14*u := by unfold width; omega
  apply advance_four acy one (by dsimp [y]; omega) (by dsimp [x]; omega) upper
  intro j jl i il
  simpa only [y,x,Nat.add_assoc] using
    cap_word H acy score hk hi (r+j) (c+i) (by omega) (by omega)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
