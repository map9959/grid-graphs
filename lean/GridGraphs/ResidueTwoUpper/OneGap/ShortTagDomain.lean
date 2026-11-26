import GridGraphs.ResidueTwoUpper.OneGap.ShortCache

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open ResidueZero L7 Stencil

private def clipped (n i k : Nat) := min 3 (min (i+k) (n-1-(i+k)))
private theorem endtag (u i k : Nat) (hi : i<33+42*u) (hk : k≤2) :
    clipped (35+42*u) i k=clipped 35 (tag u i) k := by unfold clipped tag; split_ifs <;> omega

private def shellBit (a b : Nat) : Option Bool :=
  if min a b=1 then some false else if min a b=0 ∧ 3 ≤ max a b then some true else none
private theorem skin_clip (n r c i j : Nat) :
    skin n (r+i) (c+j)=shellBit (clipped n r i) (clipped n c j) := by
  unfold skin shellBit clipped; dsimp only; split_ifs <;> first | rfl | omega

private theorem wall_code {n r c : Nat} (hr : r<n-2) (hc : c<n-2) (d : Fin 4) :
    wall n r c d=(match d.val with
      | 0 => clipped n c 2==0 | 1 => clipped n r 2==0 | 2 => clipped n c 0==0 | _ => clipped n r 0==0) := by
  fin_cases d <;> apply Bool.eq_iff_iff.mpr <;>
    norm_num [wall,Frame.depthAt,Frame.depth,clipped,center,shift] <;> omega

theorem filter_tag (u r c : Nat) (hr : r<33+42*u) (hc : c<33+42*u) (m o : Nat) :
    (frameOK (35+42*u) r c m && wallOK (35+42*u) r c m o) =
      (frameOK 35 (tag u r) (tag u c) m && wallOK 35 (tag u r) (tag u c) m o) := by
  have br : tag u r<33 := by unfold tag; split_ifs <;> omega
  have bc : tag u c<33 := by unfold tag; split_ifs <;> omega
  have w (d : Fin 4) : wall (35+42*u) r c d=wall 35 (tag u r) (tag u c) d := by
    rw [wall_code (by omega : r<35+42*u-2) (by omega : c<35+42*u-2),wall_code br bc]
    simp only [endtag u c 2 hc (by decide),endtag u r 2 hr (by decide),
      endtag u c 0 hc (by decide),endtag u r 0 hr (by decide)]
  have f (i : Fin 9) : skin (35+42*u) (r+i.val/3) (c+i.val%3)=
      skin 35 (tag u r+i.val/3) (tag u c+i.val%3) := by
    have := i.isLt; rw [skin_clip,skin_clip,endtag _ _ _ hr (by omega),endtag _ _ _ hc (by omega)]
  simp only [frameOK,wallOK,f,w]

theorem same_domain {u v r c a b : Nat}
    (hr : r<33+42*u) (hc : c<33+42*u) (ha : a<33+42*v) (hb : b<33+42*v)
    (R : tag u r=tag v a) (C : tag u c=tag v b) :
    atRC (cached u chart) r c=atRC (cached v chart) a b := by
  simp only [cached,at_build hr hc,at_build ha hb,filter_tag u r c hr hc,filter_tag v a b ha hb,R,C]
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
