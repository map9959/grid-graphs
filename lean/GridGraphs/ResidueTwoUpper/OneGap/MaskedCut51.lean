import GridGraphs.ResidueTwoUpper.OneGap.NorthCut161
import GridGraphs.ResidueTwoUpper.OneGap.NestedDeparture
import GridGraphs.ResidueTwoUpper.OneGap.TrimmedCap
import GridGraphs.ResidueTwoUpper.OneGap.ShortNorthRoot

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.NorthCut161
open ResidueZero Stencil L7 FanSlab FanSweep Short EastBoundary BoundarySix.Connected SouthCap

theorem front51 {F w P} (S : Seed (u:=3) F P w 51)
    (H : PhysicalHalo 3 F w 51 (fanDirection 3 w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*3+588*3^2) :
    Front F w 51 53 9 27 := by
  obtain ⟨upper,seals,low⟩ := read51 S acy
  have grow (r : Nat) (rl : 4≤r) (rh : r≤9) : RootLine F w 52 r := by
    induction r,rl using Nat.le_induction with
    | base => exact Short.North.line_from_three S (by decide) (by decide)
                (fun j l h => upper j l (by omega))
    | succ j jl prev =>
      have m : Strip.GridScan.Rooted.tile F w j 52=73 := upper j (by omega) (by omega)
      apply Strip.GridScan.Rooted.extend_line (prev (by omega))
      · rw [m]; decide
      · left; rw [m]; decide
  have line := grow 9 (by decide) le_rfl
  have tail := Departure.plainBeyond H acy one score (by decide) (r:=9) (c:=26)
    (by decide) (by decide) (by decide) (by decide) low line
  refine ⟨?_,fun t tl _ rt => seals t tl rt,?_⟩
  · intro r rl rh i il ih; rw [show r=9 by omega]; exact tail i (by omega) ih
  · intro t _ th rt; rw [show t=52 by omega]; exact line

/-- Once the direct cone exceeds the available 19 columns, its first
26 rows already certify a medium restart. -/
private theorem restart51 : RestartCover 10 19 33 := by
  intro j jl jh
  by_cases early : j≤26
  · left; dsimp [coneCost]; omega
  · exact .inr ⟨_,_,_,_,_,Port.medium_test,by decide,by decide,by omega,by decide,
      by dsimp [coneCost]; omega⟩

theorem exclude51 {F w P} (S : Seed (u:=3) F P w 51)
    (H : PhysicalHalo 3 F w 51 (fanDirection 3 w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*3+588*3^2) : False := by
  have fr := front51 S H acy one score
  obtain ⟨Q⟩ := flow_of_score 3 F acy score one
  have st : Straight F w 9 27 13 33 := nested_window H acy one score (by decide) Q S.room
    fr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) restart51
  have hand := physical_dangling_step_rect 3 51 9 27 _ _ _ _ _ Port.long_test
    (by decide) (by decide) (by decide) (by decide) F acy w H.parent H.step H.patches H.stars Q st fr
  exact Strip.GridScan.trimmed_excludes_of_ge53 H acy one score (by decide) (y:=36) (a:=39)
    (by decide) (by decide) (by decide) (by decide) (hand.2 _ (by decide) le_rfl)
    (hand.1.2.2 _ (by decide) (by decide) (by decide))

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.NorthCut161
