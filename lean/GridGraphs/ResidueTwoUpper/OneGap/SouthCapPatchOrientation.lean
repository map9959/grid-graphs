import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPatchRows

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero Stencil L7

/-- The existing price orbit reflects columns before rotating. -/
def viewIndex (v : View) : Fin 8 :=
  match v.rowFar, v.colFar, v.swap with
  | false, false, false => 0
  | false, true,  false => 4
  | true,  false, false => 6
  | true,  true,  false => 2
  | false, false, true  => 7
  | false, true,  true  => 1
  | true,  false, true  => 3
  | true,  true,  true  => 5

theorem image_viewIndex (v : View) (s : Int) (p : Pos) :
    image s (viewIndex v) p = L7.view v s p.1 p.2 := by
  cases v with | mk a b c =>
    cases a <;> cases b <;> cases c <;>
      norm_num [viewIndex,image,L7.view,reflect]

def compose (g h : Nat) : Nat :=
  (g%4 + (if g<4 then h%4 else 4-h%4))%4 +
    if (g<4) = (h<4) then 0 else 4

set_option maxHeartbeats 2000000 in
theorem image_compose (s : Int) (g h : Fin 8) (p : Pos) :
    image s g (image s h p) = image s (compose g h) p := by
  fin_cases g <;> fin_cases h <;>
    norm_num [image,compose,Prod.ext_iff]

private theorem rot_compose : ∀ (g h : Fin 8) (m : Fin 512),
    rotMask g (rotMask h m)=rotMask (compose g h) m := by native_decide

theorem orbit_perm : ∀ h : Fin 8,
    ((List.range 8).map (fun g => compose g h)).Perm (List.range 8) := by
  intro h
  fin_cases h <;> decide

theorem patch_encode_mark_ok (v : View) (m : Fin 512) (ok : maskOK m) :
    maskOK (encode m v) := by
  revert v m
  native_decide

private theorem encode_push : ∀ (v : View) (m : Fin 512),
    encode m v<512 ∧ rotMask (viewIndex v) (encode m v)=m := by native_decide

/-- Pulling a physical patch back to the fan view leaves its price
unchanged: the eight terms of the orbit sum are merely permuted. -/
theorem patch_encode_price (v : View) (n : Int) (p : Pos) (m : Fin 512) :
    twoOrbitPatch n p (encode m v) =
      twoOrbitPatch n (L7.view v (n-2) p.1 p.2) m := by
  let h := viewIndex v
  let e : Fin 512 := ⟨encode m v,(encode_push v m).1⟩
  have push : rotMask h e=m := (encode_push v m).2
  rw [←image_viewIndex v (n-2) p,←push]
  let term := fun g => twoPatchBill (patchLocation (n-2) (image (n-2) g p)) (rotMask g e)
  have sums := ((orbit_perm h).map term).sum_eq
  simp only [List.map_map,Function.comp_def] at sums
  unfold twoOrbitPatch
  change _ = ((List.range 8).map fun g => twoPatchBill
    (patchLocation (n-2) (image (n-2) g (image (n-2) h p))) (rotMask g (rotMask h e))).sum
  rw [←sums]
  apply congrArg List.sum
  apply List.map_congr_left
  intro g hg
  let i : Fin 8 := ⟨g,List.mem_range.mp hg⟩
  change term (compose i h) = twoPatchBill
    (patchLocation (n-2) (image (n-2) i (image (n-2) h p))) (rotMask i (rotMask h e))
  rw [image_compose (n-2) i h p,rot_compose i h e]

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
