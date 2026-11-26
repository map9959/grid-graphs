import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripCut

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 Camera FanSeed

/-- The exact rectangle consumed by the sweep, in physical-site
coordinates. `used` counts individual site-lines, including the
three substeps of a tile-line. -/
def prefixBox {h : Nat} (s : Window h (width h)) (k used : Nat) : SiteBox :=
  match s.axis with
  | .horizontal =>
    ⟨firstRow k h+3*s.start,firstRow k h+3*(s.start+s.depth),
      firstCol k h,firstCol k h+used⟩
  | .vertical =>
    ⟨firstRow k h,firstRow k h+used,
      firstCol k h+3*s.start,firstCol k h+3*(s.start+s.depth)⟩

theorem prefix_bounds {u h : Nat} (s : Window h (width h)) (hk : 59≤11+14*u)
    (lo : 14≤h) (hi : h≤43) {used : Nat} (size : used≤3*s.length) :
    let B := prefixBox s (11+14*u) used
    4≤B.north ∧ 4≤B.west ∧
      B.south≤((35+42*u:Nat):Int)-1 ∧ B.east≤((35+42*u:Nat):Int)-1 := by
  have bounds := crop_bounds (11+14*u) rfl hk lo hi
  have fit := s.fits
  cases direction : s.axis with
  | horizontal =>
    simp only [prefixBox,direction,Window.length] at size fit ⊢
    omega
  | vertical =>
    simp only [prefixBox,direction,Window.length] at size fit ⊢
    omega

private theorem strip_clear_wall {u F v q dir} (H : PhysicalHalo u F v q dir)
    (B : SiteBox) (lowR : 4≤B.north) (lowC : 4≤B.west)
    (hiR : B.south≤((35+42*u:Nat):Int)-1) (hiC : B.east≤((35+42*u:Nat):Int)-1)
    (south : Bool) (trueWall : (if south then B.south else B.east)=((35+42*u:Nat):Int)-1)
    (x : B.vertices v) (atWall : B.OnWall (coordinates v x.val) south) : x.val∉F := by
  let n := 35+42*u
  let p := coordinates v x.val
  have within : B.Contains p := x.2
  rcases within with ⟨r0,r1,c0,c1⟩
  have co : L7.view v (n:Nat) p.1 p.2=coord x.val := coords_view v x.val
  have blank : marked F (coord x.val)=false := by
    cases south
    · have col : p.2=(n:Int)-2 := by
        simp [SiteBox.OnWall] at atWall
        simp only [Bool.false_eq_true,if_false] at trueWall
        change p.2+1=B.east at atWall
        omega
      have hrow : (p.1.toNat:Int)=p.1 := Int.toNat_of_nonneg (by omega)
      have get := H.east 1 p.1.toNat (by omega) (by decide) (by omega) false (by
        simp [preset,show p.1.toNat≠0 by omega,show p.1.toNat+1≠n by omega,n])
      rw [south_coords,turned] at get
      change marked F (L7.view v (n:Nat) p.1.toNat ((n:Int)-1-1))=false at get
      rw [hrow,←show p.2=(n:Int)-1-1 by omega,co] at get
      exact get
    · have row : p.1=(n:Int)-2 := by
        simp [SiteBox.OnWall] at atWall
        simp only [if_true] at trueWall
        change p.1+1=B.south at atWall
        omega
      have hcol : (p.2.toNat:Int)=p.2 := Int.toNat_of_nonneg (by omega)
      have get := H.south 1 p.2.toNat (by omega) (by decide) (by omega) false (by
        simp [preset,show p.2.toNat≠0 by omega,show p.2.toNat+1≠n by omega,n])
      rw [south_coords] at get
      change marked F (L7.view v (n:Nat) ((n:Int)-1-1) p.2.toNat)=false at get
      rw [hcol,←show p.1=(n:Int)-1-1 by omega,co] at get
      exact get
  rw [marked_at] at blank
  exact of_decide_eq_false blank

theorem cap_prefix_wall_clear {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (s : Window h (width h)) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (used : Nat) (size : used≤3*s.length) (south : Bool)
    (wall : let B := prefixBox s (11+14*u) used
      (if south then B.south else B.east)=((35+42*u:Nat):Int)-1) :
    let B := prefixBox s (11+14*u) used
    ∀ x : B.vertices v, B.OnWall (coordinates v x.val) south → x.val∉F := by
  have b := prefix_bounds s hk lo hi size
  exact strip_clear_wall H _ b.1 b.2.1 b.2.2.1 b.2.2.2 south wall

private theorem se_coordinates (u : Nat) (v : View) :
    coordinates v (seSite u v) =
      (((34+42*u:Nat):Int),((34+42*u:Nat):Int)) := by
  apply view_inj v (35+42*u:Nat)
  rw [coords_view]
  exact coord_onSite ..

/-- Every marked component of every physical scan prefix meets a real
open side, the current frontier, or a marked depth-two wired site.
The north/east versus west/south scan order does not change the
physical marks or the southeast root. -/
theorem cap_prefix_component {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (s : Window h (width h)) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (used : Nat) (size : used≤3*s.length) :
    let B := prefixBox s (11+14*u) used
    let last : Int := ((35+42*u:Nat):Int)-1
    let kind := CutKind s.axis (decide (used=3*s.length))
      (decide (B.south=last)) (decide (B.east=last))
    ∀ x : B.vertices v, x.val∈F →
      (∃ (a : B.vertices v) (b : Site u) (side : Side),
        B.Crosses (coordinates v a.val) (coordinates v b) side ∧ kind side≠2 ∧
        ((Bonds F).induce (B.vertices v)).Reachable x a) ∨
      (∃ (a : B.vertices v) (south : Bool), (if south then B.south else B.east)=last ∧
        a.val∈F ∧ B.Tooth (coordinates v a.val) south ∧
        ((Bonds F).induce (B.vertices v)).Reachable x a) := by
  let B := prefixBox s (11+14*u) used
  let last : Int := ((35+42*u:Nat):Int)-1
  let kind := CutKind s.axis (decide (used=3*s.length))
    (decide (B.south=last)) (decide (B.east=last))
  have bounds := prefix_bounds s hk lo hi size
  have rootOut : seSite u v∉B.vertices v := by
    change ¬B.Contains (coordinates v (seSite u v))
    rw [se_coordinates]
    have edge : B.south≤last := bounds.2.2.1
    unfold SiteBox.Contains
    dsimp [last] at edge
    omega
  dsimp only
  change ∀ x : B.vertices v, x.val∈F → _
  intro x mark
  obtain ⟨a,b,bout,edge,reach⟩ := scored_prefix_crossing acy score (B.vertices v) rootOut x mark
  obtain ⟨side,hit⟩ := cut_side B v a.2 bout edge.1
  by_cases closed : kind side=2
  · right
    have which : ∃ south : Bool, (if south then B.south else B.east)=last ∧
        B.OnWall (coordinates v a.val) south := by
      cases side with
      | north => simp [kind,CutKind] at closed
      | west => simp [kind,CutKind] at closed
      | south =>
        refine ⟨true,?_,hit.1⟩
        by_contra no
        change B.south≠last at no
        simp [kind,CutKind,no] at closed
        split at closed <;> contradiction
      | east =>
        refine ⟨false,?_,hit.1⟩
        by_contra no
        change B.east≠last at no
        simp [kind,CutKind,no] at closed
        split at closed <;> contradiction
    obtain ⟨south,trueWall,wall⟩ := which
    have clear := cap_prefix_wall_clear H s hk lo hi used size south trueWall
    obtain ⟨t,tm,tt,tr⟩ := closed_wall_tooth B v south clear a x wall mark reach.symm
    exact ⟨t,south,trueWall,tm,tt,tr⟩
  · exact .inl ⟨a,b,side,hit,closed,reach⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
