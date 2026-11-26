import GridGraphs.ResidueTwoUpper.OneGap.MixedNorthCheck

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
open ResidueZero Stencil L7 FanSlab FanBoot

/-- Translate the planted isolate along the same side.  At every origin
both the price-domain tags and the mask/owner filter agree, including
at the paid star. No parent field is translated between boards. -/
theorem domain_eq (u v d : Nat) (w : View) (left : 3≤v) (room : v+19≤11+14*u)
    (r c : Nat) (hr : r<48) (hc : c<48) :
    let a := loc (11+14*u) v w r c
    let b := loc 53 6 w r c
    atRC (planted (35+42*u) (v+d) w (cached u chart)) a.1 a.2 =
      atRC (planted 161 (6+d) w (cached 3 chart)) b.1 b.2 := by
  intro a b
  let T := unview w 48 r c
  have ha := loc_bounds (by omega : v+16≤11+14*u) w hr hc
  have hb := loc_bounds (by decide : 6+16≤53) w hr hc
  change a.1<3*(11+14*u) ∧ a.2<3*(11+14*u) at ha
  change b.1<159 ∧ b.2<159 at hb
  have x := normalized (by omega : v+16≤11+14*u) w hr hc
  have y := normalized (by decide : 6+16≤53) w hr hc
  change unview w (3*(11+14*u)) a.1 a.2=(T.1,3*v+T.2) at x
  change unview w 159 b.1 b.2=(T.1,18+T.2) at y
  have D := tags u v left (by omega) w r c hr hc
  have E := tags 3 6 (by decide) (by decide) w r c hr hc
  rw [show baseWest (11+14*u) v=6 by unfold baseWest; omega] at D
  have eq := D.trans E.symm
  have dom := same_domain (u:=u) (v:=3) (r:=a.1) (c:=a.2) (a:=b.1) (b:=b.2)
    (by omega) (by omega) hb.1 hb.2 (Prod.mk.inj eq).1 (Prod.mk.inj eq).2
  have n : 35+42*u-2=3*(11+14*u) := by omega
  unfold planted
  rw [at_build (show a.1<35+42*u-2 by omega) (show a.2<35+42*u-2 by omega),
    at_build (show b.1<161-2 from hb.1) (show b.2<161-2 from hb.2)]
  simp only [seedOK,n,show 161-2=159 by decide,x,y,dom,Prod.mk.injEq]
  have lt : (3*v+T.2<1+3*(v+d)) ↔ (18+T.2<1+3*(6+d)) := by omega
  have hit : (3*v+T.2=1+3*(v+d)) ↔ (18+T.2=1+3*(6+d)) := by omega
  have phase : (3*v+T.2)%3=(18+T.2)%3 := by omega
  simp only [lt,hit,phase]
  have filters : seedOK (35+42*u) (v+d) w a.1 a.2=seedOK 161 (6+d) w b.1 b.2 := by
    funext m
    simp only [seedOK,n,show 161-2=159 by decide,x,y,lt,hit,phase]
  rw [filters]

theorem translated_label {u v d F P w} (S : Seed (u:=u) F P w (v+d))
    (acy : (Bonds F).IsAcyclic) (left : 3≤v) (room : v+19≤11+14*u)
    (fuel r c : Nat) (hr : r<48) (hc : c<48) :
    let t := target w r c
    ∃ z∈atRC (Kernel.prune 48 fuel (crop w 6 (planted 161 (6+d) w (cached 3 chart)))) t.1 t.2,
      encode (Fin.ofNat 512 z.1) w=square F w r (3*v+c) := by
  let a := loc (11+14*u) v w
  let M (r c : Nat) := actual F P (a r c).1 (a r c).2
  have lim (r c : Nat) (hr : r<48) (hc : c<48) : (a r c).1<33+42*u ∧ (a r c).2<33+42*u := by
    simpa only [show 3*(11+14*u)=33+42*u by omega] using loc_bounds (by omega : v+16≤11+14*u) w hr hc
  have agree : Agree 48 M := by
    let x := (a 0 0).1; let y := (a 0 0).2
    have eq (r c : Nat) : a r c=(x+r,y+c) := by simp [a,x,y,loc,coordAt]
    have L := lim 47 47 (by decide) (by decide); rw [eq] at L
    simpa only [M,eq] using moveAgree (actual_agree F P S.step S.owners) x y (by
      obtain ⟨_,_⟩ := L; omega)
  have live := kept_physical S acy
  rw [←cached_eq] at live
  have base : Kept 48 M (crop w 6 (planted 161 (6+d) w (cached 3 chart))) := by
    intro r hr c hc
    rw [crop,at_build hr hc,←domain_eq u v d w left room r c hr hc]
    obtain ⟨h₁,h₂⟩ := lim r c hr hc
    exact live (a r c).1 (by omega) (a r c).2 (by omega)
  intro t
  have tr : t.1<48 ∧ t.2<48 ∧ unview w 48 t.1 t.2=(r,c) := by
    cases w with | mk aa bb kk => cases aa <;> cases bb <;> cases kk <;>
      simp [t,target,unview,Prod.ext_iff] <;> omega
  refine ⟨_,kernel_kept agree base fuel t.1 tr.1 t.2 tr.2.1,?_⟩
  obtain ⟨x,hx,mask⟩ := decode_loc u v w (by omega) F t.1 t.2 tr.1 tr.2.1
  obtain ⟨h₁,h₂⟩ := lim t.1 t.2 tr.1 tr.2.1
  have same : origin (n:=35+42*u) (a t.1 t.2).1 (a t.1 t.2).2 (by omega) (by omega)=x :=
    coord_injective hx.symm
  unfold M; rw [actual_at _ _ _ _ (by omega) (by omega),same]
  have fin (z : Fin 512) : Fin.ofNat 512 z=z := Fin.ext (Nat.mod_eq_of_lt z.isLt)
  simpa only [fin,tr.2.2] using mask

theorem translated_mixed {u v F P w} (S : Seed (u:=u) F P w (v+3))
    (acy : (Bonds F).IsAcyclic) (left : 3≤v) (room : v+20≤11+14*u) :
    ∀ j, 1≤j → j≤4 → ∀ i, v+8 ≤ i → i<11+14*u →
      square F w (1+3*j) (1+3*i)=73 ∨ (j=4 ∧ i=v+8 ∧ square F w (1+3*j) (1+3*i)=9) := by
  intro j jl jh i il ih
  by_cases old : v+16 ≤ i
  · exact .inl (plateau S acy (by omega) j jl jh i (by omega) ih)
  · obtain ⟨z,live,mask⟩ := translated_label S acy left (by omega) 15 (3*j+1) (3*(i-v)+1)
      (by omega) (by omega)
    have chk := List.all_eq_true.mp (List.all_eq_true.mp (mixed_checked w) (j-1)
      (List.mem_range.mpr (by omega))) (i-(v+8)) (List.mem_range.mpr (by omega))
    rw [show j-1+1=j by omega,show i-(v+8)+8=i-v by omega] at chk
    have val := List.all_eq_true.mp chk _ live
    simp only [mask,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,
      show 3*j+1=1+3*j by omega,show 3*v+(3*(i-v)+1)=1+3*i by omega] at val
    rcases val with yes|⟨⟨jj,ii⟩,z⟩
    · exact .inl yes
    · exact .inr ⟨by omega,by omega,z⟩

theorem translated_front {u v F P w} (S : Seed (u:=u) F P w (v+3))
    (acy : (Bonds F).IsAcyclic) (left : 3≤v) (room : v+20≤11+14*u) :
    Front F w (v+3) (11+14*u) 4 (v+10) := by
  apply front_of_plateau S (by omega)
  intro j lo hi i l h
  rcases translated_mixed S acy left room j lo hi i (by omega) h with m|⟨_,e,_⟩
  · exact m
  · omega

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
