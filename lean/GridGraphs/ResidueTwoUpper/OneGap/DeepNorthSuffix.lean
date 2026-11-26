import GridGraphs.ResidueTwoUpper.OneGap.DeepNorthCheck
import GridGraphs.ResidueTwoUpper.OneGap.MixedRimWave
import GridGraphs.ResidueTwoUpper.OneGap.FanEast

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
open ResidueZero Stencil L7 FanSlab FanBoot BoundarySix.Connected FanBoot.SouthCap
open FanBoot.SouthCap.Strip.GridScan.Rooted

private theorem read73 {u v d F P w} (S : Seed (u:=u) F P w (v+d))
    (acy : (Bonds F).IsAcyclic) (left : 3≤v) (room : v+19≤11+14*u)
    {j i : Nat} (hj : j<16) (hi : i<16) (test : fixed73 (grid w (cached 3 chart) d) w j i) :
    square F w (1+3*j) (1+3*(v+i))=73 := by
  obtain ⟨z,live,mask⟩ := translated_label S acy left room 15 (3*j+1) (3*i+1) (by omega) (by omega)
  have m := List.all_eq_true.mp test _ live
  change encode (Fin.ofNat 512 z.1) w==73 at m
  simpa only [mask,beq_iff_eq,show 3*j+1=1+3*j by omega,
    show 3*v+(3*i+1)=1+3*(v+i) by omega] using m

/-- Attach row one from the small crop, grow each deeper crop witness
east, then carry each column's own north line down to the target row. -/
theorem suffix_from_sites {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    {y e : Nat} (bounds : 1≤e ∧ e≤3 ∧ 4≤y ∧ y<16)
    (rows : ∀ j, 2≤j → j≤y → ∃ b, 2≤b ∧ b≤q+e ∧ square F w (1+3*j) (1+3*b)=73)
    (_hk : 53≤11+14*u)
    (left : 6≤q) (room : q+17≤11+14*u) :
    ∀ i, q+e ≤ i → i<11+14*u → tile F w y i=73 ∧ RootLine F w i y := by
  let k := 11+14*u
  have tiles (j i : Nat) (jl : 1≤j) (jh : j≤y) (il : q+e ≤ i) (ih : i<k) :
      square F w (1+3*j) (1+3*i)=73 := by
    by_cases row1 : j=1
    · subst j
      let v := q-3
      have eq : v+3=q := by dsimp [v]; omega
      have small : Seed F P w (v+3) := eq ▸ S
      by_cases far : v+8 ≤ i
      · rcases translated_mixed small acy (by omega) (by omega) 1 le_rfl (by decide) i far ih with m|⟨z,_⟩
        · exact m
        · omega
      · let a := i-(q+1)
        have m := read73 small acy (by omega) (by omega) (by decide) (by dsimp [a]; omega)
          (first w a (by dsimp [a]; omega))
        rwa [show v+(4+a)=i by dsimp [a]; omega] at m
    · obtain ⟨b,bl,bh,init⟩ := rows j (by omega) jh
      have grow (t : Nat) (ht : b+t<k) : square F w (1+3*j) (1+3*(b+t))=73 := by
        induction t with
        | zero => exact init
        | succ t it =>
          apply east_step u q j (b+t) (by omega) (by dsimp [k] at ht; omega)
            ⟨by omega,by omega⟩ F acy w P S.step S.clean
          · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero
          · exact it (by omega)
      simpa only [show b+(i-b)=i by omega] using grow (i-b) (by omega)
  intro i il ih
  refine ⟨tiles _ _ (by omega) le_rfl il ih,?_⟩
  have root (t : Nat) (ht : 4+t≤y) : RootLine F w i (4+t) := by
    induction t with
    | zero => exact line_from_three S (by omega) ih (fun j lo hi => tiles _ _ lo (by omega) il ih)
    | succ t it =>
      have tile73 := tiles (4+t) i (by omega) (by omega) il ih
      apply extend_line (it (by omega))
      · rw [show tile F w (4+t) i=73 from tile73]; decide
      · left; rw [show tile F w (4+t) i=73 from tile73]; decide
  simpa only [show 4+(y-4)=y by omega] using root (y-4) (by omega)

theorem exclude_with_sites {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    {y e : Nat} (bounds : 1≤e ∧ e≤3 ∧ 4≤y ∧ y<16)
    (rows : ∀ j, 2≤j → j≤y → ∃ b, 2≤b ∧ b≤q+e ∧ square F w (1+3*j) (1+3*b)=73)
    (hk : 53≤11+14*u)
    (left : 6≤q) (room : q+17≤11+14*u) (width : 4*(q+e)≤11+14*u+3*y) : False := by
  apply Mixed.exclude_suffix H acy one score hk y (q+e) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  intro i il ih
  obtain ⟨m,line⟩ := suffix_from_sites S acy bounds rows hk left room i il ih
  exact ⟨.inl m,line⟩

theorem exclude {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    {d y e : Nat} (p : profile d y e) (hk : 53≤11+14*u)
    (left : d+3≤q) (room : q+17≤11+14*u) (width : 4*(q+e)≤11+14*u+3*y) : False := by
  have bounds : 9≤d ∧ d+e<16 ∧ 1≤e ∧ e≤3 ∧ 4≤y ∧ y<16 := by
    rcases p with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;> decide
  apply exclude_with_sites S H acy one score bounds.2.2 _ hk (by omega) room width
  intro j jl jh
  let v := q-d
  have eq : v+d=q := by dsimp [v]; omega
  obtain ⟨b,bh,test⟩ := starts w p jl jh
  exact ⟨v+b,by omega,by omega,read73 (eq ▸ S : Seed F P w (v+d)) acy (by omega) (by omega)
    (by omega) (by omega) test⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North.Deep
