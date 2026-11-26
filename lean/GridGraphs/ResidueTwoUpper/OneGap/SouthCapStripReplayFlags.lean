import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripSurvival

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7
namespace GridScan

/-- The north contact written in relative indices. It is one site
inward from the last top tooth, and is not a permission to wire any
of the other top columns. -/
def northIndex {h : Nat} (s : Window h (width h)) (j i : Nat) : Bool :=
  match s.axis with
  | .horizontal => decide (3*s.start+i=1 ∧ j+3=3*width h)
  | .vertical => decide (j=1 ∧ 3*s.start+i+3=3*width h)

def replayTooth {h : Nat} (s : Window h (width h)) (north : Bool)
    (j : Nat) (i : Fin (3*s.depth)) : Bool :=
  decide (EngineRimContact s j i) || (north && northIndex s j i)

def replayExits {h : Nat} (s : Window h (width h)) (j : Nat) (i : Fin (3*s.depth)) : Bool :=
  decide (EngineOpenSite s j i)

theorem physical_tooth_replay {u h : Nat} (s : Window h (width h)) (F : Finset (Site u))
    (v : View) (north : Bool) (room : width h≤11+14*u) :
    (physicalProgram s F v north).tooth = replayTooth s north := by
  funext j i
  have eq : decide (scanPoint (prefixBox s (11+14*u) (3*s.length)) s.axis j i =
      ((firstRow (11+14*u) h : Int)+1,((1+3*(11+14*u-1):Nat):Int))) =
      northIndex s j i := by
    cases ax : s.axis <;>
      simp only [northIndex,ax,scanPoint,prefixBox] <;>
      apply Bool.eq_iff_iff.mpr <;>
      simp only [decide_eq_true_eq,Prod.mk.injEq,firstCol,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] <;> omega
  simp only [physicalProgram,replayTooth,eq]

theorem physical_exits_replay {u h : Nat} (s : Window h (width h)) (F : Finset (Site u))
    (v : View) (north : Bool) :
    (physicalProgram s F v north).exits = replayExits s := rfl

/-- The replay projector depends only on the cap dimensions and the
strip placement, not on the side of the original square or its marks. -/
noncomputable def Update.replay {h : Nat} (z : Update h) (D : Domains) : Domains :=
  let s := z.window
  s.prune (tileSweep (3*s.depth) s.axis (replayTooth s z.north) (replayExits s)) D

theorem update_replay_eq {u h : Nat} (F : Finset (Site u)) (v : View)
    (room : width h≤11+14*u) (z : Update h) (D : Domains) :
    z.prune F v D=z.replay D := by
  simp only [Update.prune,Update.replay,physical_tooth_replay _ _ _ _ room,physical_exits_replay]

noncomputable def replayCap {h : Nat} (zs : List (Update h)) (D : Domains) : Domains :=
  zs.foldl (fun D z => z.replay D) D

theorem prune_replay_eq {u h : Nat} (F : Finset (Site u)) (v : View)
    (room : width h≤11+14*u) (zs : List (Update h)) (D : Domains) :
    pruneCap F v zs D=replayCap zs D := by
  induction zs generalizing D with
  | nil => rfl
  | cons z zs ih =>
    exact (ih (z.prune F v D)).trans (congrArg (replayCap zs) (update_replay_eq F v room z D))

/-- A rejected local domain is enough to refute a physical cap once
the finite replay has checked its emptiness. -/
theorem empty_domain_excludes {h : Nat} (zs : List (Update h)) (r c : Nat)
    (hr : r+2≤h) (hc : c+2≤width h)
    (empty : ∀ w, ¬replayCap zs (initialDomains h) r c w) (t : Tiles) :
    ¬Admitted h (width h) (replayCap zs (initialDomains h)) t :=
  fun ad => empty _ (ad r c hr hc)

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
