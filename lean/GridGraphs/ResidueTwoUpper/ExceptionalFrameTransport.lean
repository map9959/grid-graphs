import GridGraphs.ResidueTwoUpper.ExceptionalFrameRules

namespace GridGraphs.ResidueTwoUpper.Exceptional.Frame
open ResidueZero Stencil

private theorem patch_axis (j i t : Int) (hj : 0≤j) (ht : 0≤t ∧ t≤2) :
    axis (21+3*j) 4 (i-t)=axis 21 4 (rep 23 j i-t) := by
  simp only [axis,rep]; split_ifs <;> omega
private theorem star_axis (j i t : Int) (hj : 0≤j) (ht : 0≤t ∧ t≤2) :
    axis (23+3*j) 5 (i+t)=axis 23 5 (rep 21 j i+t) := by
  simp only [axis,rep]; split_ifs <;> omega

private theorem ranks_star (j : Nat) (p : Pos) (f nb : Nat) (b : Bool) :
    starRank (23+3*(j:Int)) p f nb b=starRank 23 (representative 23 j p) f nb b := by
  funext q
  have e : 23+3*(j:Int)-2=21+3*j := by ring
  have bnds : 0≤(offset q).1 ∧ (offset q).1≤2 ∧ 0≤(offset q).2 ∧ (offset q).2≤2 := by
    have := q.isLt; simp [offset]; omega
  have trans (i : Int) : axis (23+3*j) 5 i=axis 23 5 (rep 23 j i) :=
    transport_fine (by decide) (by positivity) (by decide) false
  have ax := patch_axis (j:Int) p.1 (offset q).1 (by positivity) ⟨bnds.1,bnds.2.1⟩
  have ay := patch_axis (j:Int) p.2 (offset q).2 (by positivity) bnds.2.2
  have ok (i t : Int) (ht : 0≤t ∧ t≤2) :
      (0 ≤ i-t ∧ i-t<21+3*(j:Int) ↔ 0≤rep 23 j i-t ∧ rep 23 j i-t<21) := by
    unfold rep; split_ifs <;> omega
  have same : inside (21+3*(j:Int)) (p-offset q)=inside 21 (representative 23 j p-offset q) := by
    apply Bool.eq_iff_iff.mpr
    simp only [inside,Bool.and_eq_true,decide_eq_true_eq]
    have x := ok p.1 _ ⟨bnds.1,bnds.2.1⟩; have y := ok p.2 _ bnds.2.2
    change (((0 ≤ p.1-(offset q).1 ∧ p.1-(offset q).1<21+3*(j:Int)) ∧
      0 ≤ p.2-(offset q).2) ∧ p.2-(offset q).2<21+3*(j:Int)) ↔
      (((0 ≤ rep 23 j p.1-(offset q).1 ∧ rep 23 j p.1-(offset q).1<21) ∧
      0 ≤ rep 23 j p.2-(offset q).2) ∧ rep 23 j p.2-(offset q).2<21)
    tauto
  simp only [starRank,event,e,show (23:Int)-2=21 by decide,same,atPos,representative,
    Prod.fst_sub,Prod.snd_sub,ax,ay,trans]

private theorem ranks_patch (j : Nat) (p : Pos) (m : Nat) (b : Bool) :
    patchRank (23+3*(j:Int)) p m b=patchRank 23 (representative 21 j p) m b := by
  funext q
  have bnds : 0≤(offset q).1 ∧ (offset q).1≤2 ∧ 0≤(offset q).2 ∧ (offset q).2≤2 := by
    have := q.isLt; simp [offset]; omega
  have trans (i : Int) : axis (21+3*j) 4 i=axis 21 4 (rep 21 j i) :=
    transport_fine (by decide) (by positivity) (by decide) false
  simp only [patchRank,event,show 23+3*(j:Int)-2=21+3*j by ring,
    show (23:Int)-2=21 by decide,atPos,representative,Prod.fst_add,Prod.snd_add,trans,
    star_axis (j:Int) p.1 (offset q).1 (by positivity) ⟨bnds.1,bnds.2.1⟩,
    star_axis (j:Int) p.2 (offset q).2 (by positivity) bnds.2.2]

private theorem inside_rep (b j : Nat) (hb : 19≤b) (p : Pos) (hp : inside (b+3*(j:Int)) p) :
    ∃ i k : Fin b, ((i.val:Int),(k.val:Int))=representative b j p := by
  simp [inside] at hp
  have x := rep_bounds (base:= (b:Int)) (j:=(j:Int)) (i:=p.1) (by omega) (by positivity) (by omega) (by omega)
  have y := rep_bounds (base:=(b:Int)) (j:=(j:Int)) (i:=p.2) (by omega) (by positivity) (by omega) (by omega)
  exact ⟨⟨_,show (rep b j p.1).toNat<b by omega⟩,⟨_,show (rep b j p.2).toNat<b by omega⟩,
    Prod.ext (by dsimp [representative]; omega) (by dsimp [representative]; omega)⟩

theorem traces_star (checked_stars : baseS) (j : Nat) {p : Pos} (hp : inside (23+3*(j:Int)) p)
    (f : Fin 2) (nb : Fin 16) (o : Fin 5) (ok : starOK (23+3*(j:Int)) p f nb o)
    (corner : ends 14 (axis (23+3*(j:Int)) 6 p.1) (axis (23+3*(j:Int)) 6 p.2) → f.val=1)
    (cheap : twoOrbitStar (23+3*(j:Int)) p f nb o=0 ∨ twoOrbitStar (23+3*(j:Int)) p f nb o=full) :
    traceOK (starRank (23+3*(j:Int)) p f nb false) (starRank (23+3*(j:Int)) p f nb true)
      (S (23+3*(j:Int)) p f nb o) := by
  let a := representative 23 j p
  obtain ⟨i,k,eq⟩ := inside_rep 23 j (by decide) p hp
  have h := of_decide_eq_true checked_stars i k f nb o
  rw [eq] at h
  have loc := starLocation_transport (b:=23) (by decide) (j:=(j:Int)) (by positivity) p
  have w : twoOrbitStar (23+3*(j:Int)) p f nb o=twoOrbitStar 23 a f nb o := by simp [twoOrbitStar,loc,a]
  have ins (d : Nat) : inside (23+3*(j:Int)) (shift p d)=inside 23 (shift a d) := by
    have e := congrArg (fun l : StarLocation => (l.neighbour d).isSome) (loc 0)
    simp only [starLocation,image,located] at e
    split_ifs at e <;> simp_all [a]
  have ok' : starOK 23 a f nb o := by simpa only [starOK,ins] using ok
  have tag (z : Int) : axis (23+3*(j:Int)) 6 z=axis 23 6 (rep 23 j z) :=
    transport_fine (by decide) (by positivity) (by decide) false
  unfold S; simp only [tag,w] at cheap corner ⊢
  rw [ranks_star,ranks_star]
  exact h ok' corner cheap

theorem traces_patch (checked_patches : baseP) (j : Nat) {p : Pos} (hp : inside (21+3*(j:Int)) p)
    (m : Fin 512) (ok : maskOK m) (cheap : twoOrbitPatch (23+3*(j:Int)) p m=0 ∨ twoOrbitPatch (23+3*(j:Int)) p m=full) :
    traceOK (patchRank (23+3*(j:Int)) p m true) (patchRank (23+3*(j:Int)) p m false)
      (W (23+3*(j:Int)) p m) := by
  obtain ⟨i,k,eq⟩ := inside_rep 21 j (by decide) p hp
  have h := of_decide_eq_true checked_patches i k m
  rw [eq] at h
  have w : twoOrbitPatch (23+3*(j:Int)) p m=twoOrbitPatch 23 (representative 21 j p) m := by
    simp [twoOrbitPatch,show 23+3*(j:Int)-2=21+3*j by ring,
      patchLocation_transport (b:=21) (by decide) (j:=(j:Int)) (by positivity)]
  have tag (z : Int) : axis (21+3*(j:Int)) 5 z=axis 21 5 (rep 21 j z) :=
    transport_fine (by decide) (by positivity) (by decide) false
  unfold W; simp only [w,show 23+3*(j:Int)-2=21+3*j by ring,tag] at cheap ⊢
  rw [ranks_patch,ranks_patch]
  exact h ok cheap

end GridGraphs.ResidueTwoUpper.Exceptional.Frame
