import GridGraphs.ResidueTwoUpper.OneGap.EastRailObstruction
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEastReplay

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
open ResidueZero L7 FanSlab BoundarySix.Connected

/-- A top-left mark and a second mark immediately right or below.
The remaining six bits of the tile are unrestricted. -/
def RailTile (m : Nat) : Prop := bit m 0=1 ∧ (bit m 1=1 ∨ bit m 3=1)

theorem rail_examples : RailTile 3 ∧ RailTile 9 ∧ RailTile 73 := by unfold RailTile; decide

/-- In a physical cap, the last column alone must contain a tile
which breaks the rail. There is no assumption on any other column
and no catalogue or strip replay in the path argument. -/
theorem eastRail_escape {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (line : RootLine F v (11+14*u-1) (11+14*u-h))
    (top : square F v (firstRow (11+14*u) h) (1+3*(11+14*u-1))=73) :
    ∃ k<h, ¬RailTile (cropTiles F v (11+14*u) h k (width h-1)) := by
  classical
  by_contra! allRail
  let s := (eastWindow h lo).window
  let t := cropTiles F v (11+14*u) h
  let p : Row.Program 6 := physicalProgram s F v true
  have wide : 2≤width h := by unfold width; omega
  have room : width h≤11+14*u := by unfold width; omega
  have ax : s.axis=.vertical := rfl
  have len : s.length=h := rfl
  have start : s.start=width h-2 := rfl
  have depth : s.depth=2 := rfl
  have read (k phase : Nat) (phaseLt : phase<3) (i : Fin 6) (slot : i.val/3=1) :
      (bit (t k (width h-1)) (3*phase+i.val%3)==1)=p.mark (3*k+phase) i := by
    have val := lineMark_physical s F v true (3*k+phase) i
    simpa only [lineMark,band,cell,ax,start,slot,show width h-2+1=width h-1 by omega,
      show (3*k+phase)/3=k by omega,show (3*k+phase)%3=phase by omega] using val
  have tooth := physical_tooth_replay s F v true room
  have rim : AcrossClosed s := by simp only [AcrossClosed,ax,start,depth]; omega
  have nr : p.tooth 1 3=true := by
    change (physicalProgram s F v true).tooth 1 (3 : Fin 6)=true
    rw [tooth]; simp [replayTooth,northIndex,ax,start]; omega
  have east (k : Nat) : p.tooth (3*k) 4=true := by
    change (physicalProgram s F v true).tooth _ _=true
    rw [tooth]; simp [replayTooth,EngineRimContact,rim,depth]
  have south : p.tooth (3*(h-1)+1) 3=true := by
    change (physicalProgram s F v true).tooth _ _=true
    rw [tooth]
    unfold replayTooth
    rw [Bool.or_eq_true]; left
    apply decide_eq_true; left
    rw [len]; omega
  have first : t 0 (width h-1)=73 := by
    have c : firstCol (11+14*u) h+3*(width h-1)=1+3*(11+14*u-1) := by unfold firstCol; omega
    simpa only [t,cropTiles,Nat.mul_zero,Nat.add_zero,c] using top
  have nm : p.mark 1 3=true := by
    rw [←read 0 1 (by decide) 3 rfl,first]; decide
  apply eastRail_obstruction h (by omega) p (physical_graph_acyclic H acy one s true hk lo hi line top)
    ⟨nm,nr⟩ (fun k _ => east k) south
  · intro k kl
    have m := (allRail k kl).1
    exact (read k 0 (by decide) 3 rfl).symm.trans (beq_iff_eq.mpr m)
  · intro k kl
    rcases (allRail k kl).2 with side|below
    · exact .inl ((read k 0 (by decide) 4 rfl).symm.trans (beq_iff_eq.mpr side))
    · exact .inr ((read k 1 (by decide) 3 rfl).symm.trans (beq_iff_eq.mpr below))

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
