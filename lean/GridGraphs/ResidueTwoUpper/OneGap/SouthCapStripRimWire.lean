import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripContact

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 Camera FanSeed

/-- A wire on a true south/east wall is realized by two physical
forced edges: the marked tooth to the depth-one vertex, then on to
the marked perimeter. This is a local wire, not yet a contraction
of all the perimeter and north contacts to a common apex. -/
theorem physical_rim_wire {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (s : Window h (width h)) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (used : Nat) (size : used≤3*s.length) (south : Bool)
    (wall : let B := prefixBox s (11+14*u) used
      (if south then B.south else B.east)=((35+42*u:Nat):Int)-1)
    (x : (prefixBox s (11+14*u) used).vertices v) (mark : x.val∈F)
    (tooth : (prefixBox s (11+14*u) used).Tooth (coordinates v x.val) south) :
    let d := if south then 1 else 0
    let p := coordinates v x.val
    let y := point u v (shift p d)
    let z := point u v (shift (shift p d) d)
    (Bonds F).Adj x.val y ∧ (Bonds F).Adj y z ∧ z∈F ∧
      coordinates v y=shift p d ∧ coordinates v z=shift (shift p d) d := by
  let B := prefixBox s (11+14*u) used
  let n := 35+42*u
  let p := coordinates v x.val
  have bd := prefix_bounds s hk lo hi size
  have inside : B.Contains p := x.2
  obtain ⟨lr,ur,lc,uc⟩ := inside
  have ar : 4≤B.north := bd.1
  have ac : 4≤B.west := bd.2.1
  have er : B.south≤(n:Int)-1 := bd.2.2.1
  have ec : B.east≤(n:Int)-1 := bd.2.2.2
  have strict (b : Bool) :
      (if b then p.1 else p.2)<(n:Int)-2 := by
    cases b
    · change p.2<(n:Int)-2
      by_contra bad
      have eq : p.2+1=B.east := by omega
      have W : B.east=(n:Int)-1 := by omega
      have blank := cap_prefix_wall_clear H s hk lo hi used size false W x eq
      exact blank mark
    · change p.1<(n:Int)-2
      by_contra bad
      have eq : p.1+1=B.south := by omega
      have W : B.south=(n:Int)-1 := by omega
      have blank := cap_prefix_wall_clear H s hk lo hi used size true W x eq
      exact blank mark
  let d := if south then 1 else 0
  let a := shift p d
  let b := shift a d
  have dep : (if south then p.1 else p.2)=(n:Int)-3 := by
    change (if south then B.south else B.east)=(n:Int)-1 at wall
    change B.Tooth p south at tooth
    cases south <;> simp [SiteBox.Tooth] at tooth wall ⊢ <;> omega
  have ain : Camera.In n a := by
    have r : p.1<(n:Int)-2 := strict true
    have c : p.2<(n:Int)-2 := strict false
    cases south <;> simp [a,d,shift,Camera.In] <;> omega
  have bin : Camera.In n b := by
    have r : p.1<(n:Int)-2 := strict true
    have c : p.2<(n:Int)-2 := strict false
    cases south <;> simp [a,b,d,shift,Camera.In] <;> omega
  let y := point u v a
  let z := point u v b
  have yz : coordinates v y=a := coords_point ain
  have zz : coordinates v z=b := coords_point bin
  have xyEdge : (gridGraph n n).Adj x.val y := by
    rw [Camera.adj_iff v, yz]
    change |p.1-a.1|+|p.2-a.2|=1
    cases south <;> simp [a,d,shift]
  have yzEdge : (gridGraph n n).Adj y z := by
    rw [Camera.adj_iff v,yz,zz]
    cases south <;> simp [b,d,shift]
  have zm : z∈F := by
    have Z : coord z=L7.view v (n:Nat) b.1 b.2 := coord_point bin
    have m : marked F (coord z)=true := by
      rw [Z]
      cases south
      · have r : p.1<(n:Int)-2 := strict true
        have P : p.2=(n:Int)-3 := dep
        have cast : (p.1.toNat:Int)=p.1 := Int.toNat_of_nonneg (by omega)
        have preset' : preset n false (!H.cornerBit) 0 p.1.toNat=some true := by
          simp [preset,show p.1.toNat≠1 by omega,show p.1.toNat≠2 by omega,
            show p.1.toNat+2≠n by omega]
        have m := H.east 0 p.1.toNat (by omega) (by decide) (by omega) true preset'
        rw [south_coords,turned,cast] at m
        simpa [b,a,d,shift,show p.2+1+1=(n:Int)-1 by omega,n] using m
      · have c : p.2<(n:Int)-2 := strict false
        have P : p.1=(n:Int)-3 := dep
        have cast : (p.2.toNat:Int)=p.2 := Int.toNat_of_nonneg (by omega)
        have preset' : preset n false H.cornerBit 0 p.2.toNat=some true := by
          simp [preset,show p.2.toNat≠1 by omega,show p.2.toNat≠2 by omega,
            show p.2.toNat+2≠n by omega]
        have m := H.south 0 p.2.toNat (by omega) (by decide) (by omega) true preset'
        rw [south_coords,cast] at m
        simpa [b,a,d,shift,show p.1+1+1=(n:Int)-1 by omega,n] using m
    rw [marked_at] at m
    exact of_decide_eq_true m
  exact ⟨⟨xyEdge,.inl mark⟩,⟨yzEdge,.inr zm⟩,zm,yz,zz⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
