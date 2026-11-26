import GridGraphs.ResidueTwoUpper.OneGap.ShortSevenNorth

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
open ResidueZero Stencil L7 FanSlab FanBoot

/-- Read any certified mask from a pruned isolate crop on side 161. -/
theorem crop_read {q F P w} (S : Seed (u:=3) F P w q) (acy : (Bonds F).IsAcyclic)
    (v fuel r c m : Nat) (room : v+16≤53) (hr : r<48) (hc : c<48)
    (ok : let t := target w r c
          (atRC (Kernel.prune 48 fuel (crop w v (planted 161 q w (cached 3 chart))))
            t.1 t.2).all (fun z => encode (Fin.ofNat 512 z.1) w==m)) :
    square F w r (3*v+c)=m := by
  let a := loc 53 v w
  let M (r c : Nat) := actual F P (a r c).1 (a r c).2
  have lim (r c : Nat) (hr : r<48) (hc : c<48) : (a r c).1<159 ∧ (a r c).2<159 :=
    loc_bounds room w hr hc
  have agree : Agree 48 M := by
    let x := (a 0 0).1; let y := (a 0 0).2
    have eq (r c : Nat) : a r c=(x+r,y+c) := by simp [a,x,y,loc,coordAt]
    have L := lim 47 47 (by decide) (by decide); rw [eq] at L
    simpa only [M,eq] using moveAgree (actual_agree F P S.step S.owners) x y (by
      change x+48≤159 ∧ y+48≤159; obtain ⟨_,_⟩ := L; omega)
  have live := kept_physical S acy
  rw [←cached_eq] at live
  have base : Kept 48 M (crop w v (planted 161 q w (cached 3 chart))) := by
    intro i hi j hj
    rw [crop,at_build hi hj]
    exact live _ (lim i j hi hj).1 _ (lim i j hi hj).2
  let t := target w r c
  have tr : t.1<48 ∧ t.2<48 ∧ unview w 48 t.1 t.2=(r,c) := by
    cases w with | mk aa bb kk => cases aa <;> cases bb <;> cases kk <;>
      simp [t,target,unview,Prod.ext_iff] <;> omega
  have g := kernel_kept agree base fuel t.1 tr.1 t.2 tr.2.1
  have chk := List.all_eq_true.mp ok _ g
  obtain ⟨x,hx,mask⟩ := decode_loc 3 v w room F t.1 t.2 tr.1 tr.2.1
  obtain ⟨h₁,h₂⟩ := lim t.1 t.2 tr.1 tr.2.1
  have same : origin (n:=161) (a t.1 t.2).1 (a t.1 t.2).2 h₁ h₂=x := coord_injective hx.symm
  change encode (Fin.ofNat 512 (M t.1 t.2).1) w==m at chk
  unfold M at chk
  rw [actual_at _ _ _ _ h₁ h₂,same] at chk
  have fin (z : Fin 512) : Fin.ofNat 512 z=z := Fin.ext (Nat.mod_eq_of_lt z.isLt)
  simpa only [fin,mask,tr.2.2,beq_iff_eq] using chk

theorem seven_front {F P w} (S : Seed (u:=3) F P w 7) (acy : (Bonds F).IsAcyclic) :
    Front F w 7 53 4 16 := by
  apply front_of_plateau S (by decide)
  intro j jl jh i il ih
  by_cases old : 20 ≤ i
  · exact plateau S acy (by decide) j jl jh i old ih
  · have ok := List.all_eq_true.mp (List.all_eq_true.mp (seven_checked w) (j-1)
        (List.mem_range.mpr (by omega))) (i-16) (List.mem_range.mpr (by omega))
    have m := crop_read S acy 4 15 _ _ 73 (by decide) (by omega) (by omega) ok
    simpa only [show 3*(j-1+1)+1=1+3*j by omega,
      show 3*4+(3*(i-16+12)+1)=1+3*i by omega] using m

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
