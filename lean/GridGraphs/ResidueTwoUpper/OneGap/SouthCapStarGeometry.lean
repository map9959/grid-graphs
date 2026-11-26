import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStarBits

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero L7

def fanPos (k h w r c : Nat) (p : Offset) : Pos :=
  (haloSite k h r p.1,haloSite k w c p.2)

private theorem shifted_axis_iff {u k h r i : Nat}
    (ke : k=11+14*u) (wide : 53≤k) (hh : h+4≤k) (rr : r+2≤h) (ii : i<18)
    (board : atlasSite h r i<119) (j : Int) (lo : -1≤j) (hi : j≤1) :
    (0≤(haloSite k h r i:Int)+j ∧ (haloSite k h r i:Int)+j<(35+42*u:Nat)) ↔
      (0≤(atlasSite h r i:Int)+j ∧ (atlasSite h r i:Int)+j<119) := by
  have g := halo_site_geometry ke wide hh rr (d:=i) (by omega)
  obtain ⟨low,low',clipped,_,same⟩ := g
  have home := clipped.mpr board
  have a := same 0 (by decide)
  have b := same 1 (by decide)
  have c := same 2 (by decide)
  interval_cases j <;> omega

/-- Every compass slot is clipped identically on the actual board
and the atlas, including the off-board east and south directions. -/
theorem star_shift_inside {u k h w r c} (pl : Placement u k h w r c) (p : Offset)
    (hp : fits p) (board : onBoard (endTag h r) (endTag w c) p) (d : Nat) (hd : d<4) :
    inside (35+42*u:Nat) (shift (fanPos k h w r c p) d) =
      inside 119 (shift (absAt (endTag h r) (endTag w c) p) d) := by
  obtain ⟨bx,by'⟩ := (onBoard_iff p).mp board
  have R j lo hi := shifted_axis_iff pl.size pl.wide pl.height pl.row hp.1 bx j lo hi
  have C j lo hi := shifted_axis_iff pl.size pl.wide pl.width pl.col hp.2 by' j lo hi
  have xy : absAt (endTag h r) (endTag w c) p =
      ((atlasSite h r p.1:Int),(atlasSite w c p.2:Int)) := by
    simp only [absAt,atlasSite,baseAt,Nat.cast_add]
  rw [xy]
  apply Bool.eq_iff_iff.mpr
  interval_cases d <;>
    simp only [inside,fanPos,shift,Bool.and_eq_true,decide_eq_true_eq] <;>
    (first
      | have a := R 0 (by decide) (by decide); have b := C 1 (by decide) (by decide); omega
      | have a := R 1 (by decide) (by decide); have b := C 0 (by decide) (by decide); omega
      | have a := R 0 (by decide) (by decide); have b := C (-1) (by decide) (by decide); omega
      | have a := R (-1) (by decide) (by decide); have b := C 0 (by decide) (by decide); omega)

theorem fanPos_move {k h w r c : Nat} (p : Offset) (d : Nat) (hd : d<4)
    (halo : inHalo p d) :
    fanPos k h w r c (move p d)=shift (fanPos k h w r c p) d := by
  interval_cases d <;>
    simp [fanPos,haloSite,move,inHalo,inside,shift,Prod.ext_iff] at * <;> omega

/-- Reading one numerical mark wire is the same as reading its
geometric site in the original board. -/
theorem physical_mark_wire {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (p : Offset) (fit : fits p)
    (board : onBoard (endTag h r) (endTag w c) p) :
    numericField (windowField pl H) (markVar p) =
      marked F (L7.view v (35+42*u:Nat) (fanPos k h w r c p).1 (fanPos k h w r c p).2) := by
  let x : Slots h w r c := slot p fit board
  have mx := numeric_mark (windowField pl H) x
  change numericField (windowField pl H) (markVar p)=(windowField pl H).mark x at mx
  have xy : coord (pl.point v x) =
      L7.view v (35+42*u:Nat) (fanPos k h w r c p).1 (fanPos k h w r c p).2 := pl.point_coord v x
  rw [mx,←xy,marked_at]
  rfl

theorem fan_view_step (v : View) (n : Int) (p : Pos) (d : Fin 4) :
    let z := shift p d
    L7.view v n z.1 z.2 = shift (L7.view v n p.1 p.2) (turn (viewIndex v) d) := by
  dsimp only
  rw [←image_viewIndex v n (shift p d),←image_viewIndex v n p]
  exact image_step n (viewIndex v) d p

private theorem rot_code : ∀ (g : Fin 8) (f a : Fin 4 → Bool),
    (∀ d : Fin 4, a ⟨turn g d,by unfold turn; omega⟩=f d) →
    rotBits g (code f)=code a := by native_decide

/-- The packed numeric sample gives exactly the original centre and
four neighbours after translating compass directions back from the fan view. -/
theorem physical_star_mark_readout {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (p : Offset) (hp : fits p)
    (board : onBoard (endTag h r) (endTag w c) p)
    (halo : (starDirs (absAt (endTag h r) (endTag w c) p)).all (inHalo p)) :
    let z := absAt (endTag h r) (endTag w c) p
    let a := numericField (windowField pl H)
    let m := packVars a (starMarkVars p (starDirs z))
    let x := pl.point v (slot p hp board)
    bit m 0=(decide (x∈F)).toNat ∧
      rotBits (viewIndex v) (neighbourCode (starDirs z) m)=neighbours F (coord x) := by
  dsimp only
  let x := pl.point v (slot p hp board)
  let t := fanPos k h w r c p
  let z := absAt (endTag h r) (endTag w c) p
  let a := numericField (windowField pl H)
  have vx : coord x=L7.view v (35+42*u:Nat) t.1 t.2 := pl.point_coord v _
  have packed := packed_star_bits a p z
  constructor
  · have mark := physical_mark_wire pl H p hp board
    change a (markVar p)=_ at mark
    rw [packed.1,mark,←vx,marked_at]
  · rw [packed.2]
    unfold neighbours
    apply rot_code
    intro d
    have coordEq := fan_view_step v (35+42*u:Nat) t d
    rw [←vx] at coordEq
    change marked F (shift (coord x) (turn (viewIndex v) d)) =
      (inside 119 (shift z d) && a (markVar (move p d)))
    rw [←coordEq]
    by_cases on : inside 119 (shift z d)
    · have mem : d.val∈starDirs z := List.mem_filter.mpr ⟨List.mem_range.mpr d.isLt,on⟩
      have ih := List.all_eq_true.mp halo d mem
      have dst := move_board d.isLt ih on
      have mark := physical_mark_wire pl H _ (move_geom hp d.isLt ih).1 dst
      change a (markVar (move p d))=_ at mark
      rw [mark,fanPos_move p d d.isLt ih]
      simp [on,t]
    · have notPhysical : ¬inside (35+42*u:Nat) (shift t d) := by
        rw [star_shift_inside pl p hp board d d.isLt]
        exact on
      have blank : marked F (L7.view v (35+42*u:Nat) (shift t d).1 (shift t d).2)=false := by
        apply Bool.eq_false_iff.mpr
        intro m
        apply notPhysical
        have insideMark := marked_inside m
        rw [←image_viewIndex v _ (shift t d)] at insideMark
        rwa [image_inside_iff] at insideMark
      rw [blank]
      simp [Bool.eq_false_iff.mpr on]

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
