import GridGraphs.ResidueTwoUpper.OneGap.FanSeed
import GridGraphs.ResidueTwoUpper.OneGap.FanStep

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
open ResidueZero Stencil L7 FanSlab

-- A zero patch at the gap elbow, with the actual eight oriented views.
private theorem elbow : ∀ (w : View) (m : Fin 512) (s : Bool),
    maskOK m → twoOrbitPatch 35 (L7.view w 33 0 0) m=0 →
    (∀ k : Fin 9, k.val≠8 → lane (encode m w) k=
      ((preset 35 s false (k.val/3) (k.val%3)).getD false).toNat) → lane (encode m w) 8=1 := by native_decide

theorem gap_tooth (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (clean : ∀ a,patchSlack F a=0) (w : View) (s f : Bool) (side : rim F w s f) :
    marked F (L7.view w (35+42*u:Nat) 2 2) := by
  let n := 35+42*u
  let a := onSite (s:=n-2) (L7.view w (33+42*(u:Int)) 0 0) (by
    rw [show n-2=33+42*u by dsimp [n]; omega]
    exact_mod_cast inside_view (n:=33+42*u) (r:=0) (j:=0) w (by omega) (by omega))
  have ha : coord a=L7.view w (33+42*(u:Int)) 0 0 := coord_onSite ..
  have z := clean a
  change twoOrbitPatch ((35+42*u:Nat):Int) (coord a) _=0 at z
  rw [ha] at z; push_cast at z
  have same := samePatch w u 0 0 (by decide) (maskAt F a)
  simp only [Nat.cast_zero,fold,show 0<21 by decide,if_true] at same
  have ee : square F w 0 0=encode (maskAt F a) w := square_eq F w _ _ a (by rw [ha]; push_cast; congr 1 <;> ring)
  have readBit (k : Fin 9) : lane (encode (maskAt F a) w) k=(marked F (L7.view w n (k.val/3:Nat) (k.val%3:Nat))).toNat := by
    rw [←ee]; simpa [square,n] using (unpack (fun q : Fin 9 => marked F (L7.view w n (q.val/3:Nat) (q.val%3:Nat)))).2 k
  have ok := elbow w (maskAt F a) s (physical_mask_ok F acy ..) (same.symm.trans z) (by
    intro k hk; rw [readBit]; apply congrArg Bool.toNat
    apply side _ _ (by have := k.isLt; omega) (by have := k.isLt; omega)
    fin_cases k <;> cases s <;> simp_all [preset] <;> omega)
  change lane (encode (maskAt F a) w) ((8 : Fin 9).val)=1 at ok; rw [readBit] at ok; simpa [n] using ok
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
