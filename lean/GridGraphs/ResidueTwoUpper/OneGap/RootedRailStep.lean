import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripNorthWire
import GridGraphs.ResidueTwoUpper.OneGap.EastRailCone

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
open ResidueZero L7 FanSeed FanSlab Camera BoundarySix.Connected SimpleGraph

abbrev tile {u} (F : Finset (Site u)) (v : View) (y t : Nat) :=
  square F v (1+3*y) (1+3*t)

abbrev onSite {u} (F : Finset (Site u)) (v : View) (r c : Nat) :=
  marked F (L7.view v (35+42*u:Nat) r c)

theorem readBit {u y t} {F : Finset (Site u)} {v : View} (i : Fin 9)
    (hit : bit (tile F v y t) i=1) :
    onSite F v (1+3*y+i.val/3) (1+3*t+i.val%3)=true := by
  let f (i : Fin 9) := onSite F v (1+3*y+i.val/3) (1+3*t+i.val%3)
  have e := (unpack f).2 i
  change bit (bits f) i=1 at hit
  change bit (bits f) i=(f i).toNat at e
  change f i=true
  cases h : f i <;> simp_all

/-- Retain the entire north path, even if mask 9 leaves a blank at the
last site of this tile: the next marked head supplies the crossing. -/
theorem extend_line {u y t} {F : Finset (Site u)} {v : View}
    (root : RootLine F v t y)
    (mid : bit (tile F v y t) 3=1)
    (cross : bit (tile F v y t) 6=1 ∨ bit (tile F v (y+1) t) 0=1) :
    RootLine F v t (y+1) := by
  have middle : onSite F v (1+3*y+1) (1+3*t)=true := readBit 3 mid
  intro r hr
  by_cases pre : r<1+3*y
  · exact root r pre
  apply Bool.or_eq_true_iff.mpr
  rcases (show r=1+3*y ∨ r=1+3*y+1 ∨ r=1+3*y+2 by omega) with e|e|e <;> subst r
  · exact .inr middle
  · exact .inl middle
  · rcases cross with a|b
    · exact .inl (readBit 6 a)
    · have h : onSite F v (1+3*(y+1)) (1+3*t)=true := readBit 0 b
      exact .inr (by simpa only [show 1+3*(y+1)=1+3*y+2+1 by omega] using h)

private theorem innerEdge {u} {F : Finset (Site u)} {v : View} {r c : Nat}
    (rl : 0<r) (ru : r+1<35+42*u) (cl : 0<c) (cu : c+2<35+42*u)
    (m : onSite F v r c=true ∨ onSite F v r (c+1)=true) :
    (interiorGraph F).Adj (railInner u v c r cl (by omega) rl ru)
      (railInner u v (c+1) r (by omega) cu rl ru) := by
  change (Bonds F).Adj (railPoint u v c r) (railPoint u v (c+1) r)
  have a := railPoint_coords (v:=v) (by omega : c<35+42*u) (by omega : r<35+42*u)
  have b := railPoint_coords (v:=v) (by omega : c+1<35+42*u) (by omega : r<35+42*u)
  constructor
  · rw [Camera.adj_iff v,a,b]; simp
  · have mark {d : Nat} (h : coordinates v (railPoint u v d r)=((r:Int),(d:Int)))
        (m : onSite F v r d=true) : railPoint u v d r∈F := by
      have eq := coords_view v (railPoint u v d r)
      rw [h] at eq
      unfold onSite at m
      rw [eq,marked_at] at m
      exact of_decide_eq_true m
    exact m.imp (mark a) (mark b)

/-- The east arm of a horizontal tile cannot bridge two distinct
north feet. Uses their physical paths, not the orientation of a
local arrow. -/
theorem no_crossbar {u y t} {F : Finset (Site u)} {v : View}
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (ry : 1+3*y+1<35+42*u) (ct : 1+3*t+4<35+42*u)
    (left : RootLine F v t y) (right : RootLine F v (t+1) y)
    (mid : bit (tile F v y t) 1=1) (head : bit (tile F v y (t+1)) 0=1) : False := by
  let c := 1+3*t
  let r := 1+3*y
  have R : 0<r := by dsimp [r]; omega
  have C : 0<c := by dsimp [c]; omega
  change r+1<35+42*u at ry
  change c+4<35+42*u at ct
  have cc : 1+3*(t+1)=c+3 := by dsimp [c]; omega
  let a := north_attachment (v:=v) C (by omega : c+1<35+42*u) (stop:=3*y)
    (by dsimp [r] at ry; omega) (fun i hi => left i (by omega))
  let b := north_attachment (v:=v) (c:=c+3) (by omega) (by omega) (stop:=3*y)
    (by dsimp [r] at ry; omega : 3*y+2<35+42*u)
    (F:=F) (fun i hi => by simpa only [cc] using right i (by omega))
  have m : onSite F v r (c+1)=true := readBit 1 mid
  have n : onSite F v r (c+3)=true := by
    have b : onSite F v r (1+3*(t+1))=true := readBit 0 head
    rwa [cc] at b
  have e := ((innerEdge R ry C (by omega) (.inr m)).reachable.trans
    (innerEdge R ry (by omega) (by omega) (.inl m)).reachable).trans
      (innerEdge R ry (by omega) (by omega) (.inr n)).reachable
  have path := a.reached.symm.trans ((by simpa only [show 3*y+1=r by dsimp [r]; omega] using e :
    (interiorGraph F).Reachable _ _) |>.trans b.reached)
  have eq := (unique_attachment (by omega) F acy one a.inside b.inside a.rim b.rim path a.link b.link).2
  have p := congrArg (fun z : PerimeterVertex (35+42*u) => (coordinates v z.val).2) eq
  change (coordinates v (railPoint u v c 0)).2=(coordinates v (railPoint u v (c+3) 0)).2 at p
  rw [railPoint_coords (by omega) (by omega),railPoint_coords (by omega) (by omega)] at p
  dsimp at p
  omega

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
