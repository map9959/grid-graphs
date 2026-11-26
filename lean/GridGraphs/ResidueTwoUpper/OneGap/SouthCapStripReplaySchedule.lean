import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayBank

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 BoundarySix.Connected
namespace GridScan

def stripUpdates (h : Nat) (axis : Axis) (depth : Nat) (min : 2≤depth)
    (packed : 3*depth+1≤16) : List (Update h) :=
  let extent := match axis with
    | .horizontal => h
    | .vertical => width h
  (List.range (extent+1-depth)).filterMap fun start =>
    if fit : start+depth≤extent then
      some ⟨⟨axis,start,depth,min,fit⟩,true,packed⟩
    else none

def stripPass (h : Nat) (depth : Nat) (min : 2≤depth) (packed : 3*depth+1≤16)
    (reverse : Bool) : List (Update h) :=
  let order := fun l : List (Update h) => if reverse then l.reverse else l
  order (stripUpdates h .horizontal depth min packed) ++
    order (stripUpdates h .vertical depth min packed)

def stripSchedule (h passesTwo passesThree : Nat) : List (Update h) :=
  ((List.range passesTwo).flatMap fun i => stripPass h 2 (by decide) (by decide) (i%2==1)) ++
    ((List.range passesThree).flatMap fun i => stripPass h 3 (by decide) (by decide) (i%2==1))

/-- A positive result from the executable bank replay excludes the
physical cap. The only finite premise here is the replay result. -/
theorem checked_replay_excludes {u h F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u)
    (lo : 14≤h) (hi : h≤43)
    (line : RootLine F v (11+14*u-1) (11+14*u-h))
    (top : ∀ i, 11+14*u-width h ≤ i → i < 11+14*u →
      FanSlab.square F v (firstRow (11+14*u) h) (1+3*i)=73)
    (zs : List (Update h)) (rejected : execute zs (initialBank h)=true) : False := by
  have room : width h≤11+14*u := by unfold width; omega
  let t := cropTiles F v (11+14*u) h
  have fit : FitsTiles t := physical_tiles_fit F v _ _
  have admitted := physical_initially_admitted F v _ h room top
    (physical_catalogue_admitted H acy score hk hi)
  have init : Admitted h (width h) (memBank (initialBank h)) t := by
    intro r c hr hc
    exact initialBank_cover ⟨fit r c,fit r (c+1),fit (r+1) c,fit (r+1) (c+1)⟩
      (admitted r c hr hc)
  have last := top (11+14*u-1) (by unfold width; omega) (by omega)
  have keeps := execute_cannot_reject lo zs (initialBank h) t init (by
    intro z _
    have trace := physical_tile_trace H acy one score z.window z.north hk lo hi line last z.packedWidth
    simpa only [physical_tooth_replay _ _ _ _ room,physical_exits_replay] using trace)
  rw [keeps] at rejected
  contradiction

/-- A checked rejection at each possible height is enough for the
long-fan southern handoff, without an axis-filter hypothesis. -/
theorem southEnd_excluded_of_replays {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2)
    (big : 57≤q) (fit : q+2≤11+14*u)
    (reject : ∀ h, 14≤h → h≤43 → ∃ zs : List (Update h), execute zs (initialBank h)=true) :
    ¬SouthEnd F v q := by
  intro south
  obtain ⟨h,lo,hi,_,_,top,line⟩ := physical_input big fit south
  obtain ⟨zs,rejected⟩ := reject h lo hi
  exact checked_replay_excludes H acy one score (by omega) lo hi line top zs rejected

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
