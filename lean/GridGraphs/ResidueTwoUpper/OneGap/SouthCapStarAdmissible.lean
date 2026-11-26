import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStarArrows

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero L7 Stencil

private def localOK (clip : Fin 4 → Bool) (f : Bool) (nb : Nat) (o : Fin 5) : Bool :=
  (List.finRange 4).all (fun d => bit nb d == 0 ||
    (clip d && bit nb ((d.val+1)%4) == 0)) &&
  (if h : o.val<4 then clip ⟨o,h⟩ && 0 < f.toNat+bit nb o else true)

private theorem starOK_local (n : Int) (p : Pos) (f : Bool) (nb : Nat) (o : Fin 5) :
    starOK n p f.toNat nb o = localOK (fun d => inside n (shift p d)) f nb o := by
  fin_cases o <;> rfl

private theorem localOK_view : ∀ (g : Fin 8) (f : Bool) (nb : Fin 16) (o : Fin 5)
    (a b : Fin 4 → Bool),
    (∀ d : Fin 4, b ⟨turn g d,by unfold turn; omega⟩=a d) →
    localOK b f (rotBits g nb) ⟨spin g o,by unfold spin turn; split_ifs <;> omega⟩ =
      localOK a f nb o := by native_decide

theorem starOK_atlas_transport {u k h w r c} (pl : Placement u k h w r c) (v : View)
    (p : Offset) (hp : fits p) (board : onBoard (endTag h r) (endTag w c) p)
    (f : Bool) (nb : Fin 16) (o : Fin 5) :
    let z := absAt (endTag h r) (endTag w c) p
    let x := pl.point v (slot p hp board)
    starOK (35+42*u:Nat) (coord x) f.toNat (rotBits (viewIndex v) nb) (spin (viewIndex v) o) =
      starOK 119 z f.toNat nb o := by
  let t := fanPos k h w r c p
  let z := absAt (endTag h r) (endTag w c) p
  let x := pl.point v (slot p hp board)
  let k' : Fin 5 := ⟨spin (viewIndex v) o,by unfold spin turn; split_ifs <;> omega⟩
  have coordX : coord x=L7.view v (35+42*u:Nat) t.1 t.2 := pl.point_coord v _
  dsimp only
  change starOK (35+42*u:Nat) (coord x) f.toNat (rotBits (viewIndex v) nb) k' =
    starOK 119 z f.toNat nb o
  rw [starOK_local,starOK_local]
  apply localOK_view
  intro d
  have geo := fan_view_step v (35+42*u:Nat) t d
  rw [←coordX] at geo
  change inside (35+42*u:Nat) (shift (coord x) (turn (viewIndex v) d)) =
    inside 119 (shift z d)
  rw [←geo,←image_viewIndex v _ (shift t d),image_inside_iff]
  exact star_shift_inside pl p hp board d d.isLt

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
