import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPatchOrientation

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero Stencil L7

/-- The orbit action fixes the sink code and rotates all four arrows. -/
def spin (g o : Nat) := if o==4 then 4 else turn g o

private theorem spin_compose : ∀ (g h : Fin 8) (o : Fin 5),
    spin g (spin h o)=spin (compose g h) o := by decide +kernel

private theorem star_rot_compose : ∀ (g h : Fin 8) (nb : Fin 16),
    rotBits g (rotBits h nb)=rotBits (compose g h) nb := by native_decide

/-- Prices do not change when coordinates, neighbour bits and
the outgoing direction are all transformed by the same view. -/
theorem star_view_price (v : View) (n : Int) (p : Pos) (f : Nat) (nb : Fin 16) (o : Fin 5) :
    twoOrbitStar n p f nb o =
      twoOrbitStar n (L7.view v n p.1 p.2) f (rotBits (viewIndex v) nb) (spin (viewIndex v) o) := by
  let h := viewIndex v
  rw [←image_viewIndex v n p]
  let term := fun g => twoStarBill (starLocation n (image n g p)) f (rotBits g nb) (spin g o)
  have sums := ((orbit_perm h).map term).sum_eq
  simp only [List.map_map,Function.comp_def] at sums
  change ((List.range 8).map term).sum =
    ((List.range 8).map fun g => twoStarBill (starLocation n (image n g (image n h p)))
      f (rotBits g (rotBits h nb)) (spin g (spin h o))).sum
  rw [←sums]
  apply congrArg List.sum
  apply List.map_congr_left
  intro g hg
  let i : Fin 8 := ⟨g,List.mem_range.mp hg⟩
  change term (compose i h)=twoStarBill (starLocation n (image n i (image n h p)))
    f (rotBits i (rotBits h nb)) (spin i (spin h o))
  rw [image_compose n i h p,star_rot_compose i h nb,spin_compose i h o]

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
