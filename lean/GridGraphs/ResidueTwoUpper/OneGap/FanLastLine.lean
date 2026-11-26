import GridGraphs.ResidueTwoUpper.OneGap.FanLong

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSeed FanSlab

set_option maxHeartbeats 750000 in
/-- The height-two end of the transport: a physical 73 in the last
nonsouth tile row reads as a 73 facing south. Only its last line must
be rooted; all other top contacts may be open. -/
theorem last_line_cap (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u))) (w : View)
    (root : RootLine F w (10+14*u) (9+14*u)) (mask : square F w (28+42*u) (31+42*u)=73)
    (terminal : tile F (FanSeed.opposite w) 4 (31+42*u)=73 → ∃ r,5≤r ∧ r<29+42*u ∧
      marked F (L7.view w (35+42*u:Nat) r (31+42*u:Nat))=false ∧ marked F (L7.view w (35+42*u:Nat) (r+1:Nat) (31+42*u:Nat))=false) : False := by
  let n := 35+42*u; let c := 31+42*u; let v := FanSeed.opposite w
  have mark (a b : Fin 3) := plateau_bit mask a b
  have bit' (a b : Fin 3) : lane (chartCol F v (c+a.val)) (4+b.val)=(decide (a.val=0)).toNat := by
    let l : Fin 7 := ⟨4+b.val,by omega⟩; have t := col_bit F v l (c+a.val)
    change lane _ (4+b.val)=_ at t; rw [t]; dsimp only [v]; rw [opposite_pos]
    have eq : ((35+42*u:Nat):Int)-1-(l.val:Nat)=((28+42*u+(2-b.val):Nat):Int) := by dsimp [l]; omega
    rw [eq]; exact mark a ⟨2-b.val,by omega⟩
  have trans : ∀ a b c : Fin 128, (∀ j t : Fin 3, lane (if j.val=0 then a.val else if j.val=1 then b.val else c.val) (4+t.val)=(decide (j.val=0)).toNat) → window a b c 4=73 := by native_decide
  have cap : tile F v 4 c=73 := trans ⟨_,col_lt F v c⟩ ⟨_,col_lt F v (c+1)⟩ ⟨_,col_lt F v (c+2)⟩ (by intro a b; fin_cases a <;> first | exact bit' 0 b | exact bit' 1 b | exact bit' 2 b)
  obtain ⟨r,lo,hi,h1,h2⟩ := terminal cap
  by_cases early : r<28+42*u
  · have h := root r (by omega); change (_ || _)=true at h
    simp only [show 1+3*(10+14*u)=31+42*u by omega,h1,h2] at h; cases h
  · have eq : r=28+42*u := by omega
    have m := mark 0 0; subst r; change (marked F (L7.view w _ (28+42*u:Nat) (31+42*u:Nat))).toNat=1 at m; rw [h1] at m; cases m
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
