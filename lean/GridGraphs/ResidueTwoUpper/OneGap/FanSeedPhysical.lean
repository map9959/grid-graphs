import GridGraphs.ResidueTwoUpper.OneGap.FanSeedData
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
open ResidueZero Stencil L7
theorem physical (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (clean : ∀ a, patchSlack F a=0) (v : View) (j : Nat)
    (hj : j<33+42*u) : cleanBand (fold u j) (chartCol F v j) (chartCol F v (j+1)) (chartCol F v (j+2)) := by
  apply List.all_eq_true.mpr
  intro r h
  have hr := List.mem_range.mp h
  let a := onSite (s:=35+42*u-2) (view v (33+42*(u:Int)) r j) (by
    rw [show 35+42*u-2=33+42*u by omega]
    exact_mod_cast inside_view (n:=33+42*u) v (by omega : r<_) hj)
  have ha : coord a=view v (33+42*(u:Int)) r j := coord_onSite ..
  have z := clean a
  change twoOrbitPatch ((35+42*u:Nat):Int) (coord a) _=0 at z
  rw [ha] at z; push_cast at z
  rw [samePatch v u r j hr] at z
  have fj : fold u j<33 := by unfold fold; split_ifs <;> omega
  have ok := seed_table v ⟨r,hr⟩ ⟨fold u j,fj⟩ _ (physical_mask_ok F acy ..) z
  change accept r (fold u j) (encode (maskAt F a) v)=true at ok
  rw [window_encode u F v r j hr a (by rw [ha]; congr 2 <;> ring)] at ok
  exact ok
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
