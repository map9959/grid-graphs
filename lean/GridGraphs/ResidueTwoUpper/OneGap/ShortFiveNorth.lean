import GridGraphs.ResidueTwoUpper.OneGap.ShortNorthRoot

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
open ResidueZero Stencil L7 FanSlab FanBoot

/-- In the isolate window use the actual planted domains, including the
exceptional owner, rather than sixteen copies of the eastern seed. -/
def crop (w : View) (v : Nat) (A : Board) := build 48 fun r c =>
  let t := loc 53 v w r c
  atRC A t.1 t.2

def fiveTest (w : View) (A : Board) :=
  let G := Kernel.prune 48 15 (crop w 3 (planted 161 5 w A))
  (List.range 4).all fun j => (List.range 2).all fun i =>
    let t := target w (3*(j+1)+1) (3*(i+13)+1)
    (atRC G t.1 t.2).all fun z => encode (Fin.ofNat 512 z.1) w==73

theorem five_block {F P w} (S : Seed (u:=3) F P w 5) (acy : (Bonds F).IsAcyclic)
    (ok : fiveTest w (cached 3 chart)) (j : Fin 4) (i : Fin 2) :
    square F w (1+3*(j.val+1)) (1+3*(16+i.val))=73 := by
  let a := loc 53 3 w
  let M (r c : Nat) := actual F P (a r c).1 (a r c).2
  have lim (r c : Nat) (hr : r<48) (hc : c<48) : (a r c).1<159 ∧ (a r c).2<159 :=
    loc_bounds (by decide : 3+16≤53) w hr hc
  have agree : Agree 48 M := by
    let x := (a 0 0).1; let y := (a 0 0).2
    have eq (r c : Nat) : a r c=(x+r,y+c) := by simp [a,x,y,loc,coordAt]
    have L := lim 47 47 (by decide) (by decide); rw [eq] at L
    simpa only [M,eq] using moveAgree (actual_agree F P S.step S.owners) x y (by
      change x+48≤159 ∧ y+48≤159; obtain ⟨_,_⟩ := L; omega)
  have live := kept_physical S acy
  rw [←cached_eq] at live
  have base : Kept 48 M (crop w 3 (planted 161 5 w (cached 3 chart))) := by
    intro r hr c hc
    rw [crop,at_build hr hc]
    exact live _ (lim r c hr hc).1 _ (lim r c hr hc).2
  let r := 3*(j.val+1)+1; let c := 3*(i.val+13)+1; let t := target w r c
  have tr : t.1<48 ∧ t.2<48 ∧ unview w 48 t.1 t.2=(r,c) := by
    have := j.isLt; have := i.isLt
    cases w with | mk aa bb kk => cases aa <;> cases bb <;> cases kk <;>
      simp [t,target,r,c,unview,Prod.ext_iff] <;> omega
  have g := kernel_kept agree base 15 t.1 tr.1 t.2 tr.2.1
  have chk := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp ok j.val
    (List.mem_range.mpr j.isLt)) i.val (List.mem_range.mpr i.isLt)) _ g
  obtain ⟨x,hx,mask⟩ := decode_loc 3 3 w (by decide) F t.1 t.2 tr.1 tr.2.1
  obtain ⟨h₁,h₂⟩ := lim t.1 t.2 tr.1 tr.2.1
  have same : origin (n:=161) (a t.1 t.2).1 (a t.1 t.2).2 h₁ h₂=x := coord_injective hx.symm
  change encode (Fin.ofNat 512 (M t.1 t.2).1) w==73 at chk
  unfold M at chk
  rw [actual_at _ _ _ _ h₁ h₂,same] at chk
  have fin (m : Fin 512) : Fin.ofNat 512 m=m := Fin.ext (Nat.mod_eq_of_lt m.isLt)
  simp only [fin,mask,tr.2.2,beq_iff_eq] at chk
  simpa only [r,c,show 3*(j.val+1)+1=1+3*(j.val+1) by omega,
    show 3*3+(3*(i.val+13)+1)=1+3*(16+i.val) by omega] using chk

@[noinline] private def viewsPass (A : Board) := decide (∀ w : View, fiveTest w A)
private theorem checked : viewsPass (cached 3 chart) := by native_decide

/-- On side 161 the original isolate at index five pins two more
columns on all four upper plateau rows, in the seed's own view. -/
theorem five_front {F P w} (S : Seed (u:=3) F P w 5) (acy : (Bonds F).IsAcyclic) :
    Front F w 5 53 4 16 := by
  apply front_of_plateau S (by decide)
  intro j jl jh i il ih
  by_cases old : 18 ≤ i
  · exact plateau S acy (by decide) j jl jh i old ih
  · have m := five_block S acy (of_decide_eq_true checked w)
      ⟨j-1,by omega⟩ ⟨i-16,by omega⟩
    simpa only [show j-1+1=j by omega,show 16+(i-16)=i by omega] using m

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
