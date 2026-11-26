import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStarGeometry

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero L7 Std.Sat

def starGuard (p : Offset) (ds : List Nat) (o : Nat) : CNF.Clause Nat :=
  if o=4 then (ds.map (arcVar p)).map (·,true) else [(arcVar p o,false)]

private theorem turn_surj : ∀ (g : Fin 8) (d : Fin 4), ∃ e : Fin 4, turn g e=d.val := by
  decide +kernel

private theorem shift_inj (t : Pos) : ∀ d e : Fin 4, shift t d=shift t e → d=e := by
  intro d e eq
  fin_cases d <;> fin_cases e <;>
    simp [shift,Prod.ext_iff] at eq ⊢ <;> omega

private theorem dir_lt_of_ne {n : Nat} {x y : GridVertex n n} (ne : x≠y) :
    outDir x y<4 := by
  unfold outDir
  split_ifs <;> first | contradiction | decide

private theorem turn_lt' (g d : Nat) : turn g d<4 := by unfold turn; omega

theorem physical_arc_wire {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (p : Offset) (hp : fits p)
    (board : onBoard (endTag h r) (endTag w c) p) (d : Fin 4)
    (on : inside 119 (shift (absAt (endTag h r) (endTag w c) p) d))
    (halo : inHalo p d) :
    let x := pl.point v (slot p hp board)
    numericField (windowField pl H) (arcVar p d)=true ↔
      H.parent x≠x ∧ outDir x (H.parent x)=turn (viewIndex v) d := by
  let src : Slots h w r c := slot p hp board
  let dst : Slots h w r c := slot (move p d) (move_geom hp d.isLt halo).1
    (move_board d.isLt halo on)
  let x := pl.point v src
  let y := pl.point v dst
  have next : nextSlot src d=some dst := nextSlot_move _ _ d.isLt halo _
  have reads := numeric_arc (windowField pl H) src d
  rw [next] at reads
  change numericField (windowField pl H) (arcVar p d)=(windowField pl H).arrow src dst at reads
  have stepEq : shift (coord x) (turn (viewIndex v) d)=coord y := by
    dsimp only [x,y]
    rw [pl.point_coord,pl.point_coord]
    change shift (L7.view v (35+42*u:Nat) (fanPos k h w r c p).1 (fanPos k h w r c p).2) _ =
      L7.view v (35+42*u:Nat) (fanPos k h w r c (move p d)).1 (fanPos k h w r c (move p d)).2
    rw [fanPos_move p d d.isLt halo]
    exact (fan_view_step v _ _ d).symm
  have adj : (GridGraphs.gridGraph (35+42*u) (35+42*u)).Adj x y :=
    (pl.point_adj v src dst).mpr (move_geom hp d.isLt halo).2.2.2
  rw [reads]
  change (decide (src≠dst ∧ H.parent x=y)=true) ↔ _
  simp only [decide_eq_true_eq]
  change (src≠dst ∧ H.parent x=y) ↔ (H.parent x≠x ∧ outDir x (H.parent x)=turn (viewIndex v) d)
  constructor
  · rintro ⟨_,par⟩
    rw [par]
    refine ⟨adj.ne.symm,?_⟩
    let a : Fin 4 := ⟨outDir x y,dir_lt_of_ne adj.ne⟩
    let b : Fin 4 := ⟨turn (viewIndex v) d,turn_lt' _ _⟩
    exact congrArg Fin.val (shift_inj (coord x) a b ((shift_out adj).trans stepEq.symm))
  · rintro ⟨ne,out⟩
    refine ⟨fun e => adj.ne (congrArg (pl.point v) e),coord_injective ?_⟩
    rw [←shift_out (H.step x ne).1,out,stepEq]

/-- An active CNF star guard reads exactly the physical outgoing
direction, or the physical fixed point when it reads code four. -/
theorem guarded_star_out {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (p : Offset) (hp : fits p)
    (board : onBoard (endTag h r) (endTag w c) p) (o : Nat)
    (halo : (starDirs (absAt (endTag h r) (endTag w c) p)).all (inHalo p))
    (mem : o∈starDirs (absAt (endTag h r) (endTag w c) p)++[4])
    (guard : (starGuard p (starDirs (absAt (endTag h r) (endTag w c) p)) o).eval
      (numericField (windowField pl H))≠true) :
    let x := pl.point v (slot p hp board)
    outDir x (H.parent x)=spin (viewIndex v) o := by
  dsimp only
  let x := pl.point v (slot p hp board)
  let a := numericField (windowField pl H)
  let z := absAt (endTag h r) (endTag w c) p
  let t := fanPos k h w r c p
  have vx : coord x=L7.view v (35+42*u:Nat) t.1 t.2 := pl.point_coord v _
  by_cases sink : o=4
  · have fix : H.parent x=x := by
      by_contra step
      have adj := (H.step x step).1
      let d : Fin 4 := ⟨outDir x (H.parent x),dir_lt_of_ne (fun eq => step eq.symm)⟩
      obtain ⟨e,turn⟩ := turn_surj (viewIndex v) d
      have eq := fan_view_step v (35+42*u:Nat) t e
      rw [←vx,turn] at eq
      change _ = shift (coord x) (outDir x (H.parent x)) at eq
      rw [shift_out adj] at eq
      have phy := coord_inside (H.parent x)
      rw [←eq,←image_viewIndex v _ (shift t e),image_inside_iff,
        star_shift_inside pl p hp board e e.isLt] at phy
      have en : e.val∈starDirs z := List.mem_filter.mpr ⟨List.mem_range.mpr e.isLt,phy⟩
      have arc := (physical_arc_wire pl H p hp board e phy (List.all_eq_true.mp halo _ en)).mpr
        ⟨step,turn.symm⟩
      apply guard
      simp only [starGuard,sink,if_true,CNF.Clause.eval]
      apply List.any_eq_true.mpr
      refine ⟨(arcVar p e,true),List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨e.val,en,rfl⟩,rfl⟩,?_⟩
      simp [arc]
    change outDir x (H.parent x)=_
    simp [fix,outDir,spin,sink]
  · have en : o∈starDirs z := by simpa [sink] using mem
    obtain ⟨lt,on⟩ := List.mem_filter.mp en
    let e : Fin 4 := ⟨o,List.mem_range.mp lt⟩
    have arc : a (arcVar p o)=true := by
      by_contra no
      apply guard
      have z0 : a (arcVar p o)=false := Bool.eq_false_iff.mpr no
      simp [starGuard,sink,CNF.Clause.eval,z0,a] -- singleton negative guard
    have h := (physical_arc_wire pl H p hp board e on (List.all_eq_true.mp halo _ en)).mp arc
    simpa [spin,beq_iff_eq,sink,e] using h.2

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
