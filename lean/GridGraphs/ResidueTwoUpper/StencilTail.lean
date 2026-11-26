import GridGraphs.ResidueTwoUpper.StencilLocal

namespace GridGraphs.ResidueTwoUpper.Stencil
open GridGraphs.ResidueZero

theorem fromStar {n : Nat} (checked : twoStarCheck n) {p : Pos} (hp : inside n p)
    {f nb o : Nat} (hf : f<2) (hn : nb<16) (ho : o<5) (ok : starOK n p f nb o) :
    0 ≤ twoOrbitStar n p f nb o := by
  simp [twoStarCheck,List.all_eq_true] at checked
  simp [inside] at hp
  have H := checked p.1.toNat (by omega) p.2.toNat (by omega) f (by omega) nb (by omega) o (by omega)
  simpa [Int.toNat_of_nonneg (by omega : 0≤p.1),Int.toNat_of_nonneg (by omega : 0≤p.2),ok] using H

theorem fromPatch {n : Nat} (checked : twoPatchCheck n) {p : Pos} (hp : inside (n-2:Nat) p)
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

private theorem ok_transport (t : Nat) (p : Pos) (f nb o : Nat) :
    starOK (23+3*(t:Int)) p f nb o=starOK 23 (representative 23 t p) f nb o := by
  have loc := starLocation_transport (b:=23) (by decide) (j:=(t:Int)) (by positivity) p 0
  have h (d : Nat) := congrArg (fun l : StarLocation => (l.neighbour d).isSome) loc
  have use (d : Nat) : inside (23+3*(t:Int)) (shift p d)=inside 23 (shift (representative 23 t p) d) := by
    have eq := h d
    simp only [starLocation,image,located] at eq
    split_ifs at eq <;> simp_all
  simp only [starOK,use]

theorem star_nonneg_of_check (checks : twoStarCheck 20 && twoStarCheck 23) (t : Nat) {p : Pos} (hp : inside (20+3*(t:Int)) p)
    {f nb o : Nat} (hf : f<2) (hn : nb<16) (ho : o<5) (ok : starOK (20+3*(t:Int)) p f nb o) :
    0≤twoOrbitStar (20+3*(t:Int)) p f nb o := by
  have h := checks
  simp only [Bool.and_eq_true] at h
  cases t with
  | zero => exact fromStar h.1 (by simpa using hp) hf hn ho (by simpa using ok)
  | succ j =>
    have e : 20+3*((j+1:Nat):Int)=23+3*(j:Int) := by omega
    rw [e,ok_transport] at ok
    rw [e] at hp ⊢
    have loc := starLocation_transport (b:=23) (by decide) (j:=(j:Int)) (by positivity) p
    simp only [twoOrbitStar,loc]
    exact fromStar h.2 (rep_inside (by decide) (by positivity) hp) hf hn ho ok

theorem patch_nonneg_of_check (checks : twoPatchCheck 20 && twoPatchCheck 23) (t : Nat) {p : Pos} (hp : inside (18+3*(t:Int)) p)
    {m : Nat} (hm : m<512) (ok : maskOK m) : 0≤twoOrbitPatch (20+3*(t:Int)) p m := by
  have h := checks
  simp only [Bool.and_eq_true] at h
  cases t with
  | zero => exact fromPatch h.1 (by simpa using hp) hm ok
  | succ j =>
    have e : 20+3*((j+1:Nat):Int)-2=21+3*(j:Int) := by omega
    have u : 18+3*((j+1:Nat):Int)=21+3*(j:Int) := by omega
    rw [u] at hp
    have loc := patchLocation_transport (b:=21) (by decide) (j:=(j:Int)) (by positivity) p
    simp only [twoOrbitPatch,e,loc]
    exact fromPatch h.2 (rep_inside (by decide) (by positivity) hp) hm ok

end GridGraphs.ResidueTwoUpper.Stencil
