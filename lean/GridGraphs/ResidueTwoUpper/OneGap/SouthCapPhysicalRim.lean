import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPhysicalRows

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero L7
set_option maxRecDepth 1024

private theorem frame_preset (b : Bool) (X Y : Nat)
    (hx : 3≤X) (hy : 3≤Y) (ux : X<119) (uy : Y<119) :
    seFrame b (X,Y) =
      if 117≤X then preset 119 false b (118-X) Y
      else if 117≤Y then preset 119 false (!b) (118-Y) X else none := by
  have xCases : X=117 ∨ X=118 ∨ X<117 := by omega
  have yCases : Y=117 ∨ Y=118 ∨ Y<117 := by omega
  have x0 : X≠0 := by omega
  have x1 : X≠1 := by omega
  have x2 : X≠2 := by omega
  have y0 : Y≠0 := by omega
  have y1 : Y≠1 := by omega
  have y2 : Y≠2 := by omega
  rcases xCases with rfl|rfl|xl <;> rcases yCases with rfl|rfl|yl <;>
    simp (disch := omega) [seFrame,preset,Prod.ext_iff,x0,x1,x2,y0,y1,y2]
  all_goals
    try
      have xa : ¬117≤X := by omega
      have xb : X≠117 := by omega
      have xc : X≠118 := by omega
      have xd : (X:Int)≠117 := by omega
      have xe : (X:Int)≠118 := by omega
      simp [xa,xb,xc,xd,xe]
  all_goals
    have ya : ¬117≤Y := by omega
    have yb : Y≠117 := by omega
    have yc : Y≠118 := by omega
    have yd : (Y:Int)≠117 := by omega
    have ye : (Y:Int)≠118 := by omega
    simp [ya,yb,yc,yd,ye]

private theorem preset_transport {n z Z t : Nat} (b : Bool) (lo : 3≤z) (lo' : 3≤Z)
    (h1 : z+1=n ↔ Z+1=119) (h2 : z+2=n ↔ Z+2=119) :
    preset n false b t z = preset 119 false b t Z := by
  simp only [preset,show z≠0 by omega,show Z≠0 by omega,if_false,h1,h2,
    show z≠1 by omega,show Z≠1 by omega,show z≠2 by omega,show Z≠2 by omega,false_or]

/-- Every numeric frame unit clause comes from the two strips of
the same physical halo, with the correct complementary corner bits. -/
theorem physical_rim_law {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (p : BoardOffset) (hp : p∈sites)
    (board : onBoard (endTag h r) (endTag w c) p) (m : Bool)
    (frame : seFrame H.cornerBit (absAt (endTag h r) (endTag w c) p)=some m) :
    numericField (windowField pl H) (markVar p)=m := by
  have fit : fits p := by
    obtain ⟨i,hi,mem⟩ := List.mem_flatMap.mp hp
    obtain ⟨j,hj,e⟩ := List.mem_map.mp mem
    rw [←e]
    exact ⟨List.mem_range.mp hi,List.mem_range.mp hj⟩
  let x := haloSite k h r p.1
  let y := haloSite k w c p.2
  let X := atlasSite h r p.1
  let Y := atlasSite w c p.2
  let n := 35+42*u
  have gx := halo_site_geometry pl.size pl.wide pl.height pl.row (d:=p.1) (by have := fit.1; omega)
  have gy := halo_site_geometry pl.size pl.wide pl.width pl.col (d:=p.2) (by have := fit.2; omega)
  have loX : 88≤X := atlasSite_ge88 pl.row
  have loY : 88≤Y := atlasSite_ge88 pl.col
  have hx : 3≤x := halo_below_defect pl.wide pl.height
  have hy : 3≤y := halo_below_defect pl.wide pl.width
  obtain ⟨inX,inY⟩ := (onBoard_iff p).mp board
  change X<119 at inX
  change Y<119 at inY
  have frame' : seFrame H.cornerBit (X,Y)=some m := by
    simpa only [X,Y,atlasSite,absAt,baseAt,Nat.cast_add] using frame
  rw [frame_preset H.cornerBit X Y (by omega) (by omega) inX inY] at frame'
  let s : Slots h w r c := slot p fit board
  change numericField (windowField pl H) (wireNumber p.1 p.2 0)=m
  rw [show wireNumber p.1 p.2 0 = wireNumber s.1.1.val s.1.2.val 0 from rfl,numeric_mark]
  have mark_eq : (windowField pl H).mark s=marked F (L7.view v (n:Nat) x y) := by
    have eq : coord (pl.point v s)=L7.view v (n:Nat) x y := pl.point_coord v s
    rw [←eq, marked_at]
    rfl
  rw [mark_eq]
  split at frame'
  · rename_i a
    let t := 118-X
    have ht : t≤6 := by omega
    have hit : x+t+1=n := (gx.2.2.2.2 t ht).mpr (by omega)
    have atSite := H.south t y hy (by omega) (gy.2.2.1.mpr inY) m
      ((preset_transport H.cornerBit hy (by omega)
          (gy.2.2.2.2 0 (by decide)) (gy.2.2.2.2 1 (by decide))).trans frame')
    rw [south_coords,show (n:Int)-1-t=(x:Int) by omega] at atSite
    exact atSite
  · split at frame'
    · let t := 118-Y
      have ht : t≤6 := by omega
      have hit : y+t+1=n := (gy.2.2.2.2 t ht).mpr (by omega)
      have atSite := H.east t x hx (by omega) (gx.2.2.1.mpr inX) m
        ((preset_transport (!H.cornerBit) hx (by omega)
            (gx.2.2.2.2 0 (by decide)) (gx.2.2.2.2 1 (by decide))).trans frame')
      rw [south_coords,turned,show (n:Int)-1-t=(y:Int) by omega] at atSite
      exact atSite
    · contradiction

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
