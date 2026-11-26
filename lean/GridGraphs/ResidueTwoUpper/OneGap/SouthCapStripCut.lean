import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripExit

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 Camera FanSeed

/-- Half-open, physical-site rectangle. This also describes a scan
prefix, cutting after any of the three site-lines within a tile. -/
structure SiteBox where
  north : Int
  south : Int
  west : Int
  east : Int

def SiteBox.Contains (B : SiteBox) (p : Pos) : Prop :=
  B.north≤p.1 ∧ p.1<B.south ∧ B.west≤p.2 ∧ p.2<B.east

def SiteBox.vertices (B : SiteBox) {n : Nat} (v : View) : Set (GridVertex n n) :=
  {p | B.Contains (coordinates v p)}

inductive Side where | north | south | west | east
deriving DecidableEq

/-- The four exact ways of leaving a rectangular prefix by a grid
edge. The boundary point is on the last *included* line. -/
def SiteBox.Crosses (B : SiteBox) (p q : Pos) : Side → Prop
  | .north => p.1=B.north ∧ q.1+1=p.1 ∧ q.2=p.2
  | .south => p.1+1=B.south ∧ q.1=p.1+1 ∧ q.2=p.2
  | .west => p.2=B.west ∧ q.2+1=p.2 ∧ q.1=p.1
  | .east => p.2+1=B.east ∧ q.2=p.2+1 ∧ q.1=p.1

private theorem axial {p q : Pos} (d : |p.1-q.1|+|p.2-q.2|=1) :
    (q.1=p.1-1 ∧ q.2=p.2) ∨ (q.1=p.1+1 ∧ q.2=p.2) ∨
    (q.2=p.2-1 ∧ q.1=p.1) ∨ (q.2=p.2+1 ∧ q.1=p.1) := by
  simp only [abs_eq_max_neg] at d
  omega

theorem cut_side {n : Nat} (B : SiteBox) (v : View) {x y : GridVertex n n}
    (xin : x∈B.vertices v) (yout : y∉B.vertices v) (adj : (gridGraph n n).Adj x y) :
    ∃ side, B.Crosses (coordinates v x) (coordinates v y) side := by
  have d := axial ((Camera.adj_iff v x y).mp adj)
  change B.Contains (coordinates v x) at xin
  change ¬B.Contains (coordinates v y) at yout
  simp only [SiteBox.Contains] at xin yout
  rcases d with d|d|d|d
  · exact ⟨.north,by unfold SiteBox.Crosses; omega⟩
  · exact ⟨.south,by unfold SiteBox.Crosses; omega⟩
  · exact ⟨.west,by unfold SiteBox.Crosses; omega⟩
  · exact ⟨.east,by unfold SiteBox.Crosses; omega⟩

/-- In axis-free mode the outside north/west sides are open. The
south/east sides are closed exactly when they end at the physical
rim. An interrupted sweep adds its own frontier in the sweep direction. -/
def CutKind (axis : Axis) (finished atSouth atEast : Bool) (side : Side) : Fin 3 :=
  match side with
  | .north | .west => 0 -- open side
  | .south =>
    if axis=.vertical ∧ ¬finished then 1 -- frontier
    else if atSouth then 2 else 0
  | .east =>
    if axis=.horizontal ∧ ¬finished then 1
    else if atEast then 2 else 0

def SiteBox.OnWall (B : SiteBox) (p : Pos) (isSouth : Bool) : Prop :=
  if isSouth then p.1+1=B.south else p.2+1=B.east

/-- At a closed south/east wall the attachment site is one line
inward from the last included site-line (`n-2` in the engine's
zero-based transverse numbering). -/
def SiteBox.Tooth (B : SiteBox) (p : Pos) (isSouth : Bool) : Prop :=
  if isSouth then p.1+2=B.south else p.2+2=B.east

/-- A marked component touching an unmarked closed wall already
contains a marked tooth. The first edge of its path back to a mark
cannot run along the wall, and cannot run out of the retained box. -/
theorem closed_wall_tooth {n : Nat} {F : Finset (GridVertex n n)}
    (B : SiteBox) (v : View) (isSouth : Bool)
    (clear : ∀ x : B.vertices v, B.OnWall (coordinates v x.val) isSouth → x.val∉F)
    (endpoint origin : B.vertices v)
    (wall : B.OnWall (coordinates v endpoint.val) isSouth)
    (mark : origin.val∈F)
    (reach : ((Bonds F).induce (B.vertices v)).Reachable endpoint origin) :
    ∃ tooth : B.vertices v, tooth.val∈F ∧
      B.Tooth (coordinates v tooth.val) isSouth ∧
      ((Bonds F).induce (B.vertices v)).Reachable origin tooth := by
  have blank := clear endpoint wall
  obtain ⟨path⟩ := reach
  cases path with
  | nil => exact (blank mark).elim
  | @cons _ y _ edge tail =>
    have forced : (Bonds F).Adj endpoint.val y.val := edge
    have markedY : y.val∈F := forced.2.resolve_left blank
    have notWall := fun h => clear y h markedY
    have inY : B.Contains (coordinates v y.val) := y.2
    have d := axial ((Camera.adj_iff v _ _).mp forced.1)
    have tooth : B.Tooth (coordinates v y.val) isSouth := by
      cases isSouth <;> simp [SiteBox.OnWall,SiteBox.Tooth,SiteBox.Contains] at wall notWall inY ⊢ <;> omega
    exact ⟨y,markedY,tooth,tail.reverse.reachable⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
