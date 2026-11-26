import GridGraphs.ResidueTwoUpper.StencilLocal
import GridGraphs.ResidueZero.PhysicalPatch

namespace GridGraphs.ResidueTwoUpper.Stencil
open GridGraphs.ResidueZero hiding scale starNormPrices patchNormPrices edgePrices incidencePrices overlapPrices cornerPrices
open Finset

theorem checkStars : twoStarCheck 20 && twoStarCheck 23 := by native_decide
theorem checkPatches : twoPatchCheck 20 && twoPatchCheck 23 := by native_decide

private theorem fromStar {n : Nat} (checked : twoStarCheck n) {p : Pos} (hp : inside n p)
    {f nb o : Nat} (hf : f<2) (hn : nb<16) (ho : o<5) (ok : starOK n p f nb o) :
    0 ≤ twoOrbitStar n p f nb o := by
  simp [twoStarCheck,List.all_eq_true] at checked
  simp [inside] at hp
  have H := checked p.1.toNat (by omega) p.2.toNat (by omega) f (by omega) nb (by omega) o (by omega)
  simpa [Int.toNat_of_nonneg (by omega : 0≤p.1),Int.toNat_of_nonneg (by omega : 0≤p.2),ok] using H

private theorem fromPatch {n : Nat} (checked : twoPatchCheck n) {p : Pos} (hp : inside (n-2:Nat) p)
    {m : Nat} (hm : m<512) (ok : maskOK m) : 0 ≤ twoOrbitPatch n p m := by
  simp [twoPatchCheck,List.all_eq_true] at checked
  simp [inside] at hp
  have H := checked p.1.toNat (by omega) p.2.toNat (by omega) m hm
  simpa [Int.toNat_of_nonneg (by omega : 0≤p.1),Int.toNat_of_nonneg (by omega : 0≤p.2),ok] using H

private theorem rep_inside {b j : Int} (hb : 19≤b) (hj : 0≤j) {p : Pos} (h : inside (b+3*j) p) :
    inside b (representative b j p) := by
  simp [inside] at h
  have hr := rep_bounds hb hj (i:=p.1) (by omega) (by omega)
  have hc := rep_bounds hb hj (i:=p.2) (by omega) (by omega)
  have ok {q : Pos} (a : 0≤q.1) (b' : q.1<b) (c : 0≤q.2) (d : q.2<b) :
      inside b q := by simp [inside,a,b',c,d]
  exact ok hr.1 hr.2 hc.1 hc.2

end GridGraphs.ResidueTwoUpper.Stencil
