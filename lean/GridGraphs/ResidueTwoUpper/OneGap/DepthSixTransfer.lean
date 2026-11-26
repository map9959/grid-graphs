import GridGraphs.ResidueTwoUpper.OneGap.WideCrop
import GridGraphs.ResidueTwoUpper.OneGap.DeepNorthSuffix

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open ResidueZero Stencil L7 FanSlab FanBoot BoundarySix.Connected FanBoot.SouthCap

private theorem geo {l k v r c} (w : View) (room : v+l≤k) (hr : r<3*l) (hc : c<3*l) :
    let a := Wide.loc (3*l) k v w r c; let t := unview w (3*l) r c
    a.1<3*k ∧ a.2<3*k ∧ unview w (3*k) a.1 a.2=(t.1,3*v+t.2) := by
  cases w with | mk f g b => cases f <;> cases g <;> cases b <;>
    simp [Wide.loc,Wide.axis,unview,Prod.ext_iff] <;> omega

private theorem crop_domain (l u ref v s d : Nat) (w : View)
    (left : (v=0 ∧ s=0) ∨ (3≤v ∧ 3 ≤ s)) (refRoom : s+l+3≤11+14*ref) (room : v+l+3≤11+14*u)
    (r c : Nat) (hr : r<3*l) (hc : c<3*l) :
    let a := Wide.loc (3*l) (11+14*u) v w r c; let b := Wide.loc (3*l) (11+14*ref) s w r c
    atRC (planted (35+42*u) (v+d) w (cached u chart)) a.1 a.2 =
      atRC (planted (35+42*ref) (s+d) w (cached ref chart)) b.1 b.2 := by
  intro a b
  let T := unview w (3*l) r c
  obtain ⟨ha,hc',x⟩ := geo w (by omega : v+l≤11+14*u) hr hc
  obtain ⟨hb,hd,y⟩ := geo w (by omega : s+l≤11+14*ref) hr hc
  change a.1<3*(11+14*u) at ha
  change a.2<3*(11+14*u) at hc'
  change b.1<3*(11+14*ref) at hb
  change b.2<3*(11+14*ref) at hd
  change unview w (3*(11+14*u)) a.1 a.2=(T.1,3*v+T.2) at x
  change unview w (3*(11+14*ref)) b.1 b.2=(T.1,3*s+T.2) at y
  have ax (i : Nat) (hi : i<3*l) (vert far : Bool) :
      tag u (Wide.axis (3*l) (11+14*u) (if vert then 0 else v) far i)=
      tag ref (Wide.axis (3*l) (11+14*ref) (if vert then 0 else s) far i) := by
    cases vert <;> cases far <;> simp only [Wide.axis,tag,Bool.false_eq_true,if_false,if_true]
      <;> split_ifs <;> omega
  have tags : (tag u a.1,tag u a.2)=(tag ref b.1,tag ref b.2) := by
    cases w with | mk f g sw =>
      cases sw
      · exact Prod.ext (ax _ hr true f) (ax _ hc false g)
      · exact Prod.ext (ax _ hr false f) (ax _ hc true g)
  have dom := same_domain (u:=u) (v:=ref) (r:=a.1) (c:=a.2) (a:=b.1) (b:=b.2)
    (by omega) (by omega) (by omega) (by omega) (Prod.mk.inj tags).1 (Prod.mk.inj tags).2
  have n : 35+42*u-2=3*(11+14*u) := by omega
  have lt : (3*v+T.2<1+3*(v+d)) ↔ (3*s+T.2<1+3*(s+d)) := by omega
  have hit : (3*v+T.2=1+3*(v+d)) ↔ (3*s+T.2=1+3*(s+d)) := by omega
  have phase : (3*v+T.2)%3=(3*s+T.2)%3 := by omega
  have nr : 35+42*ref-2=3*(11+14*ref) := by omega
  have filters : seedOK (35+42*u) (v+d) w a.1 a.2=seedOK (35+42*ref) (s+d) w b.1 b.2 := by
    funext m; simp only [seedOK,n,nr,x,y,lt,hit,phase]
  unfold planted
  rw [at_build (show a.1<35+42*u-2 by omega) (show a.2<35+42*u-2 by omega),
    at_build (show b.1<35+42*ref-2 by omega) (show b.2<35+42*ref-2 by omega)]
  simp only [filters,n,nr,x,y,dom,Prod.mk.injEq,hit]

theorem read_reference (ref l : Nat) {u v s d F P w} (S : Seed (u:=u) F P w (v+d))
    (acy : (Bonds F).IsAcyclic) (left : (v=0 ∧ s=0) ∨ (3≤v ∧ 3 ≤ s))
    (refRoom : s+l+3≤11+14*ref) (room : v+l+3≤11+14*u)
    {j i : Nat} (hj : j<l) (hi : i<l)
    (test : let t := Wide.target (3*l) w (3*j+1) (3*i+1)
            (atRC (Kernel.prune (3*l) 18 (build (3*l) fun r c =>
              let b := Wide.loc (3*l) (11+14*ref) s w r c; atRC (planted (35+42*ref) (s+d) w (cached ref chart)) b.1 b.2))
              t.1 t.2).all fun z => encode (Fin.ofNat 512 z.1) w==73) :
    square F w (1+3*j) (1+3*(v+i))=73 := by
  let k := 11+14*u
  let a := Wide.loc (3*l) k v w
  let M (r c : Nat) := actual F P (a r c).1 (a r c).2
  have lim (r c : Nat) (hr : r<3*l) (hc : c<3*l) : (a r c).1<33+42*u ∧ (a r c).2<33+42*u := by
    obtain ⟨h₁,h₂,_⟩ := geo w (by dsimp [k]; omega : v+l≤k) hr hc
    change (a r c).1<3*k at h₁; change (a r c).2<3*k at h₂; dsimp [k] at *; omega
  have agree : Agree (3*l) M := by
    let x := (a 0 0).1; let y := (a 0 0).2
    have eq (r c : Nat) : a r c=(x+r,y+c) := by simp [a,x,y,Wide.loc,Wide.axis]
    have L := lim (3*l-1) (3*l-1) (by omega) (by omega); rw [eq] at L
    obtain ⟨h₁,h₂⟩ := L
    have G := actual_agree F P S.step S.owners
    intro r hr c hc
    simp only [M,eq]
    exact ⟨fun _ => (G (x+r) (by omega) (y+c) (by omega)).1 (by omega),
      fun _ => (G (x+r) (by omega) (y+c) (by omega)).2 (by omega)⟩
  have live := kept_physical S acy
  rw [←cached_eq] at live
  have base : Kept (3*l) M (build (3*l) fun r c => let b := Wide.loc (3*l) (11+14*ref) s w r c
      atRC (planted (35+42*ref) (s+d) w (cached ref chart)) b.1 b.2) := by
    intro r hr c hc
    rw [at_build hr hc,←crop_domain l u ref v s d w left refRoom room r c hr hc]
    obtain ⟨h₁,h₂⟩ := lim r c hr hc
    exact live (a r c).1 (by omega) (a r c).2 (by omega)
  let r := 3*j+1; let c := 3*i+1; let t := Wide.target (3*l) w r c
  have tr : t.1<3*l ∧ t.2<3*l ∧ unview w (3*l) t.1 t.2=(r,c) := by
    cases w with | mk f g b => cases f <;> cases g <;> cases b <;>
      simp [t,Wide.target,r,c,unview,Prod.ext_iff] <;> omega
  have m := List.all_eq_true.mp test _ (kernel_kept agree base 18 t.1 tr.1 t.2 tr.2.1)
  change encode (Fin.ofNat 512 (M t.1 t.2).1) w==73 at m
  obtain ⟨h₁,h₂⟩ := lim t.1 t.2 tr.1 tr.2.1
  let z := origin (n:=35+42*u) (a t.1 t.2).1 (a t.1 t.2).2 (by omega) (by omega)
  have pos : coord z=L7.view w ((35+42*u:Int)-2) r (3*v+c:Nat) := by
    obtain ⟨_,_,eq⟩ := geo w (by dsimp [k]; omega : v+l≤k) tr.1 tr.2.1
    rw [tr.2.2] at eq
    apply Eq.trans _ (congrArg (fun p : Nat × Nat => L7.view w ((35+42*u:Int)-2) p.1 p.2) eq)
    change (((a t.1 t.2).1:Int),((a t.1 t.2).2:Int))=
      L7.view w _ (unview w (3*k) (a t.1 t.2).1 (a t.1 t.2).2).1 (unview w (3*k) (a t.1 t.2).1 (a t.1 t.2).2).2
    cases w with | mk f g b => cases f <;> cases g <;> cases b <;>
      simp [unview,L7.view,reflect,Prod.ext_iff,k] <;> dsimp [k] at * <;> omega
  have mask := square_eq F w r (3*v+c) z (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using pos)
  unfold M at m; rw [actual_at _ _ _ _ (by omega) (by omega)] at m
  change (encode (Fin.ofNat 512 (maskAt F z)) w==73)=true at m
  have fin (x : Fin 512) : Fin.ofNat 512 x=x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
  simpa only [fin,←mask,beq_iff_eq,r,c,show 3*j+1=1+3*j by omega,
    show 3*v+(3*i+1)=1+3*(v+i) by omega] using m

theorem read_crop (l : Nat) {u v s d F P w} (S : Seed (u:=u) F P w (v+d))
    (acy : (Bonds F).IsAcyclic) (left : (v=0 ∧ s=0) ∨ (3≤v ∧ 3 ≤ s))
    (refRoom : s+l+3≤53) (room : v+l+3≤11+14*u)
    {j i : Nat} (hj : j<l) (hi : i<l)
    (test : let t := Wide.target (3*l) w (3*j+1) (3*i+1)
            (atRC (Kernel.prune (3*l) 18 (build (3*l) fun r c =>
              let b := Wide.loc (3*l) 53 s w r c; atRC (planted 161 (s+d) w (cached 3 chart)) b.1 b.2))
              t.1 t.2).all fun z => encode (Fin.ofNat 512 z.1) w==73) :
    square F w (1+3*j) (1+3*(v+i))=73 :=
  read_reference 3 l S acy left refRoom room hj hi test

theorem read_big {u v s d F P w} (S : Seed (u:=u) F P w (v+d))
    (acy : (Bonds F).IsAcyclic) (left : (v=0 ∧ s=0) ∨ (3≤v ∧ 3 ≤ s))
    (refRoom : s+27≤53) (room : v+27≤11+14*u)
    {j i : Nat} (hj : j<24) (hi : i<24)
    (test : bigFixed (Kernel.prune 72 18 (build 72 fun r c =>
      let b := loc72 53 s w r c; atRC (planted 161 (s+d) w (cached 3 chart)) b.1 b.2)) w j i) :
    square F w (1+3*j) (1+3*(v+i))=73 :=
  read_crop 24 S acy left refRoom room hj hi test

theorem exclude_six {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (hk : 53≤11+14*u) (lo : 21≤q) (room : q+17≤11+14*u)
    (width : 4*(q+1)≤11+14*u+18) : False := by
  apply exclude_with_sites S H acy one score (y:=6) (e:=1) (by decide) _ hk (by omega) room width
  intro j jl jh
  let v := q-18
  have eq : v+18=q := by dsimp [v]; omega
  obtain ⟨b,hb,ok⟩ := six_rays w jl jh
  exact ⟨v+b,by omega,by omega,read_big (s:=6) (eq ▸ S : Seed F P w (v+18)) acy
    (.inr ⟨by omega,by decide⟩) (by decide) (by omega) (by omega) (by omega) ok⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
