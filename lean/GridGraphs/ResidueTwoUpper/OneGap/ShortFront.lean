import GridGraphs.ResidueTwoUpper.OneGap.ShortNorthScan
import GridGraphs.ResidueTwoUpper.OneGap.ShortTagDomain

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
open ResidueZero Stencil L7 FanSlab FanBoot
local notation "side(" u ")" => (35+42*u : Nat)
local notation "tiles(" u ")" => (11+14*u : Nat)

theorem decode_loc (u v : Nat) (w : View) (room : v+16≤tiles(u))
    (F : Finset (GridVertex side(u) side(u))) (r c : Nat) (hr : r<48) (hc : c<48) :
    let a := loc tiles(u) v w r c; let t := unview w 48 r c
    ∃ x : origins side(u), coord x=((a.1:Int),(a.2:Int)) ∧
      encode (maskAt F x) w=square F w t.1 (3*v+t.2) := by
  let a := loc tiles(u) v w r c
  let t := unview w 48 r c
  have lim := loc_bounds room w hr hc
  change a.1<3*tiles(u) ∧ a.2<3*tiles(u) at lim
  let x := origin (n:=side(u)) a.1 a.2 (by omega) (by omega)
  refine ⟨x,rfl,(square_eq F w t.1 (3*v+t.2) x ?_).symm⟩
  have eq := normalized room w hr hc
  change unview w (3*tiles(u)) a.1 a.2=(t.1,3*v+t.2) at eq
  apply Eq.trans _ (congrArg (fun p : Nat × Nat =>
    L7.view w ((side(u):Int)-2) p.1 p.2) eq)
  change ((a.1:Int),(a.2:Int))=
    L7.view w ((side(u):Int)-2) (unview w (3*tiles(u)) a.1 a.2).1
      (unview w (3*tiles(u)) a.1 a.2).2
  obtain ⟨ha,hb⟩ := lim
  cases w with | mk f g b => cases f <;> cases g <;> cases b <;>
    simp [unview,L7.view,reflect,Prod.ext_iff] <;> omega

set_option maxHeartbeats 1200000 in
theorem block (u q v : Nat) {F : Finset (GridVertex side(u) side(u))} {w P} (S : Seed F P w q)
    (acy : (Bonds F).IsAcyclic) (lo : q<v) (left : 3≤v) (room : v+16≤tiles(u))
    (j i : Fin 4) : square F w (1+3*(j.val+1)) (1+3*(v+12+i.val))=73 := by
  let a := loc tiles(u) v w
  let b := loc 25 (baseWest tiles(u) v) w
  let M (r c : Nat) := actual F P (a r c).1 (a r c).2
  have lim (r c : Nat) (hr : r<48) (hc : c<48) : (a r c).1<33+42*u ∧ (a r c).2<33+42*u := by
    simpa only [show 3*tiles(u)=33+42*u by omega] using loc_bounds room w hr hc
  have B : 6≤baseWest tiles(u) v ∧ baseWest tiles(u) v≤9 := by unfold baseWest; omega
  have B' (r c : Nat) (hr : r<48) (hc : c<48) : (b r c).1<75 ∧ (b r c).2<75 :=
    loc_bounds (by omega : baseWest tiles(u) v+16≤25) w hr hc
  have G := actual_agree F P S.step S.owners
  have agree : Agree 48 M := by
    let x := (a 0 0).1;let y := (a 0 0).2
    have e (r c : Nat) : a r c=(x+r,y+c) := by simp [x,y,a,loc,coordAt]
    have L := lim 47 47 (by decide) (by decide); rw [e] at L
    simpa only [M,e] using moveAgree G x y (by obtain ⟨h₁,h₂⟩ := L; omega)
  have live := kept_physical S acy
  rw [←cached_eq] at live
  have base : Kept 48 M (window w (baseWest tiles(u) v) (cached 1 chart)) := by
    intro r hr c hc
    let A := a r c; let T := unview w 48 r c
    have H := lim r c hr hc; have B' := B' r c hr hc
    have D := tags u v left room w r c hr hc
    have hA : A.1<side(u)-2 ∧ A.2<side(u)-2 := by
      change (a r c).1<side(u)-2 ∧ (a r c).2<side(u)-2
      obtain ⟨h₁,h₂⟩ := H
      omega
    have old := live A.1 hA.1 A.2 hA.2
    have X := normalized room w hr hc
    have N' : side(u)-2=3*tiles(u) := by omega
    change unview w (3*tiles(u)) A.1 A.2=(T.1,3*v+T.2) at X
    have ne : (T.1,3*v+T.2)≠(1,1+3*q) := by intro eq; have := congrArg Prod.snd eq; dsimp at this; omega
    unfold planted at old
    rw [at_build hA.1 hA.2,N',X,if_neg ne] at old
    obtain ⟨dom,seed⟩ := List.mem_filter.mp old
    have dom' : M r c∈atRC (cached 1 chart) (b r c).1 (b r c).2 := by
      rw [←same_domain H.1 H.2 B'.1 B'.2 (Prod.mk.inj D).1 (Prod.mk.inj D).2]; exact dom
    unfold window; rw [at_build hr hc]
    by_cases al : T.1=1 ∧ T.2%3=1
    · rw [if_pos al]; refine List.mem_filter.mpr ⟨dom',?_⟩
      unfold seedOK at seed; rw [N',X] at seed
      change (if T.1=1 ∧ (3*v+T.2)%3=1 then
        if 3*v+T.2<1+3*q then bit (M r c).1 4==1 else
          encode (Fin.ofNat 512 (M r c).1) w==(if 3*v+T.2=1+3*q then 64 else 72)
        else true)=true at seed
      have phase : (3*v+T.2)%3=1 := by omega
      simpa only [al.1,phase,eq_self,true_and,if_true,if_neg (by omega : ¬3*v+T.2<1+3*q),
        if_neg (by omega : 3*v+T.2≠1+3*q)] using seed
    · rwa [if_neg al]
  have idx : ∃ z : Fin 4, baseWest tiles(u) v=6+z.val := ⟨⟨baseWest tiles(u) v-6,by omega⟩,by dsimp; omega⟩
  obtain ⟨z,Z⟩ := idx
  have ready := of_decide_eq_true tests w z
  rw [←Z] at ready
  let r := 3*(j.val+1)+1; let c := 3*(i.val+12)+1; let t := target w r c
  have tr : t.1<48 ∧ t.2<48 ∧ unview w 48 t.1 t.2=(r,c) := by
    have := j.isLt; have := i.isLt
    cases w with | mk aa bb kk => cases aa <;> cases bb <;> cases kk <;>
      simp [t,target,r,c,unview,Prod.ext_iff] <;> omega
  have g := kernel_kept agree base 30 t.1 tr.1 t.2 tr.2.1
  have final := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp ready j.val
    (List.mem_range.mpr j.isLt)) i.val (List.mem_range.mpr i.isLt)) _ g
  obtain ⟨x,hx,mask⟩ := decode_loc u v w room F t.1 t.2 tr.1 tr.2.1
  obtain ⟨H₁,H₂⟩ := lim t.1 t.2 tr.1 tr.2.1
  have same : origin (n:=side(u)) (a t.1 t.2).1 (a t.1 t.2).2 (by omega) (by omega)=x :=
    coord_injective hx.symm
  change encode (Fin.ofNat 512 (M t.1 t.2).1) w==73 at final
  unfold M at final; rw [actual_at _ _ _ _ (by omega) (by omega),same] at final
  have fin (m : Fin 512) : Fin.ofNat 512 m=m := Fin.ext (Nat.mod_eq_of_lt m.isLt)
  simp only [fin,mask,tr.2.2,beq_iff_eq] at final
  simpa only [r,c,show 3*(j.val+1)+1=1+3*(j.val+1) by omega,
    show 3*v+(3*(i.val+12)+1)=1+3*(v+12+i.val) by omega] using final

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
