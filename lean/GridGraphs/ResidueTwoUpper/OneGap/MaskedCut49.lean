import GridGraphs.ResidueTwoUpper.OneGap.NorthCut161
import GridGraphs.ResidueTwoUpper.OneGap.GuardedSchedules
import GridGraphs.ResidueTwoUpper.OneGap.ShortNorthRoot

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.NorthCut161
open ResidueZero L7 FanSlab Short EastBoundary BoundarySix.Connected SouthCap

theorem front49 {F w P} (S : Seed (u:=3) F P w 49)
    (H : PhysicalHalo 3 F w 49 (fanDirection 3 w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*3+588*3^2) :
    Front F w 49 53 9 26 := by
  obtain ⟨upper,_,west,low⟩ := read49 S acy
  have roots (i : Nat) (rt : 49 < i) (hi : i<53) : RootLine F w i 9 := by
    have grow (r : Nat) (rl : 4≤r) (rh : r≤9) : RootLine F w i r := by
      induction r,rl using Nat.le_induction with
      | base => exact Short.North.line_from_three S rt hi (fun j l h => upper j i l (by omega) rt hi)
      | succ j jl prev =>
        have m : Strip.GridScan.Rooted.tile F w j i=73 := upper j i (by omega) (by omega) rt hi
        apply Strip.GridScan.Rooted.extend_line (prev (by omega))
        · rw [m]; decide
        · left; rw [m]; decide
    exact grow _ (by decide) le_rfl
  have line := roots 52 (by decide) (by decide)
  have tail := Departure.plainBeyond H acy one score (by decide) (r:=9) (c:=26)
    (by decide) (by decide) (by decide) (by decide) low line
  have plain : maskAtTile F w 9 26=73 := by
    rcases west with plain|corner
    · exact east_step 3 49 9 25 (by decide) (by decide) (by decide) F acy w P S.step S.clean
        (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero) plain
    · exact low.resolve_left (fun nine => Break129.no_fast_tail H acy one score (by decide)
        (r:=9) (x:=25) (by decide) (by decide) (by decide) (by decide) corner nine
        (fun i lo hi => tail i (by omega) hi) line)
  refine ⟨?_,?_,fun i _ hi rt => roots i rt hi⟩
  · intro r rl rh i il ih; rw [show r=9 by omega]
    rcases Nat.eq_or_lt_of_le il with rfl|lt
    · exact plain
    · exact tail i lt ih
  · exact fun _ tl _ rt => seals49 S acy tl rt

theorem exclude49 {F w P} (S : Seed (u:=3) F P w 49)
    (H : PhysicalHalo 3 F w 49 (fanDirection 3 w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*3+588*3^2) : False := by
  have ck : Guarded.atCut 53 49 9 26 := by decide
  exact Guarded.exclude_from_cut H acy one score (by decide) S.room (y:=9) (f:=26) ck
    (by decide) (by decide) (by decide) (front49 S H acy one score)
    (fun cap => False.elim ((by decide : ¬Guarded.endFits 53 44 26) cap))
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.NorthCut161
