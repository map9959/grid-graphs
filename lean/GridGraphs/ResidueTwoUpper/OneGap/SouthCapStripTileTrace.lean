import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripTileRead

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 BoundarySix.Connected
namespace GridScan

abbrev TileState (n : Nat) := PackedPartition × Option (Fin n → Bool)

def tick {n : Nat} (tooth exits : Nat → Fin n → Bool) (j : Nat) (mark : Fin n → Bool)
    (old : TileState n) : Option (TileState n) := do
  let t ← Row.transition old.1 old.2 mark (tooth j) (exits j)
  return (t,some mark)

def tileStep {n : Nat} (axis : Axis) (tooth exits : Nat → Fin n → Bool)
    (j : Nat) (line : Nat → Nat) (old : TileState n) : Option (TileState n) := do
  let x ← tick tooth exits (3*j) (fun i => lineMark axis line 0 i) old
  let y ← tick tooth exits (3*j+1) (fun i => lineMark axis line 1 i) x
  tick tooth exits (3*j+2) (fun i => lineMark axis line 2 i) y

def tileSweep (n : Nat) (axis : Axis) (tooth exits : Nat → Fin n → Bool) :
    Window.Sweep (TileState n) :=
  ⟨((Row.basePartition n).pack,none),
    fun j old line next => tileStep axis tooth exits j line old=some next,
    fun t => Row.Program.accepts n t.1=true⟩

private def atTime {n : Nat} (p : Row.Program n) (j : Nat) : TileState n :=
  ((p.run (Row.basePartition n).pack j).getD (Row.basePartition n).pack,p.previous j)

private theorem tick_atTime {n : Nat} (p : Row.Program n) (j : Nat)
    (prev : ∃ prev, p.run (Row.basePartition n).pack j=some prev)
    (next : ∃ next, p.run (Row.basePartition n).pack (j+1)=some next) :
    tick p.tooth p.exits j (p.mark j) (atTime p j)=some (atTime p (j+1)) := by
  obtain ⟨a,ha⟩ := prev
  obtain ⟨b,hb⟩ := next
  have step : p.advance j a=some b := by simpa only [Row.Program.run,ha,Option.bind_some] using hb
  change Row.transition a (p.previous j) (p.mark j) (p.tooth j) (p.exits j)=some b at step
  unfold tick atTime
  rw [ha,hb]
  change (Row.transition a (p.previous j) (p.mark j) (p.tooth j) (p.exits j)).bind
    (fun t => some (t,some (p.mark j)))=some (b,some (p.mark j))
  rw [step]
  rfl

/-- Whole accepted tile trace on the very same physical field as the
catalogue. Its step relation consumes the three physical site-lines
of one tile-line, and retains the previous mark row across steps. -/
theorem physical_tile_trace {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2)
    (s : Window h (width h)) (north : Bool) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (line : RootLine F v (11+14*u-1) (11+14*u-h))
    (top : FanSlab.square F v (firstRow (11+14*u) h) (1+3*(11+14*u-1))=73)
    (size : 3*s.depth+1≤16) :
    let p := physicalProgram s F v north
    s.HasTrace (tileSweep (3*s.depth) s.axis p.tooth p.exits)
      (band (cropTiles F v (11+14*u) h) s.axis s.start) := by
  let p := physicalProgram s F v north
  let b := band (cropTiles F v (11+14*u) h) s.axis s.start
  have run j bound := physical_run_prefix H acy one score s north hk lo hi line top size j bound
  refine ⟨fun j => atTime p (3*j),rfl,?_,?_⟩
  · intro j fit
    have marks (phase : Nat) (phaseLt : phase<3) :
        (fun i : Fin (3*s.depth) => lineMark s.axis (b j) phase i)=p.mark (3*j+phase) := by
      funext i
      have read := lineMark_physical s F v north (3*j+phase) i
      rw [show (3*j+phase)/3=j by omega,show (3*j+phase)%3=phase by omega] at read
      exact read
    change tileStep s.axis p.tooth p.exits j (b j) (atTime p (3*j))=
      some (atTime p (3*(j+1)))
    have A := tick_atTime p (3*j) (run _ (by omega)) (run _ (by omega))
    have B := tick_atTime p (3*j+1) (run _ (by omega)) (run _ (by omega))
    have C := tick_atTime p (3*j+2) (run _ (by omega)) (run _ (by omega))
    rw [tileStep,marks 0 (by decide),marks 1 (by decide),marks 2 (by decide)]
    rw [Nat.add_zero,A]
    change (tick p.tooth p.exits (3*j+1) (p.mark (3*j+1)) (atTime p (3*j+1))).bind
      (fun t => tick p.tooth p.exits (3*j+2) (p.mark (3*j+2)) t)=_
    rw [B]
    change tick p.tooth p.exits (3*j+2) (p.mark (3*j+2)) (atTime p (3*j+2))=_
    rw [C,show 3*j+2+1=3*(j+1) by omega]
  · obtain ⟨out,done,accepted⟩ := physical_packed_run_accepts H acy one score s north hk lo hi line top size
    change Row.Program.accepts (3*s.depth) (atTime p (3*s.length)).1=true
    simpa [atTime,p,done] using accepted

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
