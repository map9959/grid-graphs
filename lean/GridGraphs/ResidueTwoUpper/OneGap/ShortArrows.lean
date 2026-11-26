import GridGraphs.ResidueTwoUpper.OneGap.ShortBoard

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open ResidueZero Stencil L7 FanSlab
variable {n : Nat}

def origin (r c : Nat) (hr : r<n-2) (hc : c<n-2) : origins n := (⟨r,hr⟩,⟨c,hc⟩)
def site (r c : Nat) (hr : r<n-2) (hc : c<n-2) : GridVertex n n :=
  (⟨r+1,by omega⟩,⟨c+1,by omega⟩)
def actual (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n) (r c : Nat) : Label :=
  if hr : r<n-2 then if hc : c<n-2 then
    (maskAt F (origin r c hr hc),outDir (site r c hr hc) (P (site r c hr hc))) else (0,4) else (0,4)
theorem actual_at (F : Finset (GridVertex n n)) (P : GridVertex n n → _) (r c) (hr : r<n-2) (hc : c<n-2) :
    actual F P r c=((maskAt F (origin r c hr hc)).val,outDir (site r c hr hc) (P (site r c hr hc))) := by
  simp [actual,hr,hc]
theorem coord_origin (r c) (hr : r<n-2) (hc : c<n-2) : coord (origin r c hr hc)=((r:Int),(c:Int)) := rfl
theorem coord_site (r c) (hr : r<n-2) (hc : c<n-2) : coord (site r c hr hc)=center r c := rfl

theorem dir_eq {v w : GridVertex n n} {P : GridVertex n n → GridVertex n n}
    (F : Finset (GridVertex n n)) (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (adj : (gridGraph n n).Adj v w) :
    outDir v (P v)=outDir v w ↔ P v=w := by
  refine ⟨fun e => ?_,fun h => congrArg _ h⟩
  by_cases h : P v=v
  · rw [h] at e; unfold outDir at e; simp only [if_pos rfl,if_neg adj.ne] at e
    split_ifs at e <;> contradiction
  · apply coord_injective
    rw [←shift_out (step v h).1,e,shift_out adj]

theorem owner_edge (F : Finset (GridVertex n n)) (P : GridVertex n n → _)
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (arr : ∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) {v w : GridVertex n n}
    (adj : (gridGraph n n).Adj v w) :
    xor (decide (v∈F ∨ w∈F)) (outDir v (P v)==outDir v w) =
      (outDir w (P w)==outDir w v) := by
  have a := dir_eq F step adj
  have b := dir_eq F step adj.symm
  by_cases h : v∈F ∨ w∈F
  · have z := arr v w ⟨adj,h⟩
    apply Bool.eq_iff_iff.mpr
    simp [h,a,b,z]
  · have x : P v≠w := fun e => h (e ▸ (step v (fun eq => adj.ne (eq.symm.trans e))).2)
    have y : P w≠v := fun e => h (Or.symm (e ▸ (step w (fun eq => adj.ne.symm (eq.symm.trans e))).2))
    simp [h,a.not.mpr x,b.not.mpr y]

theorem contact_iff (F : Finset (GridVertex n n)) (r c) (hr : r<n-2) (hc : c<n-2)
    {v : GridVertex n n} (d : Fin 4) (eq : coord v=shift (center r c) d) :
    contact (maskAt F (origin r c hr hc)) d ↔ site r c hr hc∈F ∨ v∈F := by
  obtain ⟨a,b⟩ := PatchFilter.packed_center F (origin r c hr hc) (site r c hr hc) rfl
  have ds : ∀ (m : Fin 512) (d : Fin 4), bit m ([5,7,3,1][d.val]!)=bit (PatchFilter.cnb m) d := by decide +kernel
  unfold contact; rw [a,ds,b,neighbours_bit,coord_site,←eq,marked_at]
  by_cases x : site r c hr hc∈F <;> by_cases y : v∈F <;> simp [x,y]

private def idView := View.mk false false false
private theorem square_mask (F : Finset (GridVertex n n)) (r c) (hr : r<n-2) (hc : c<n-2) :
    square F idView r c=maskAt F (origin r c hr hc) := by
  have E := square_eq F idView r c (origin r c hr hc) rfl
  have dec : ∀ m : Fin 512, encode m idView=m.val := by decide +kernel
  exact E.trans (dec _)

theorem actual_agree (F : Finset (GridVertex n n)) (P : GridVertex n n → _)
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (arr : ∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) : Agree (n-2) (actual F P) := by
  intro r hr c hc
  have edge (v : Bool) (r' c' : Nat) (hr' : r'<n-2) (hc' : c'<n-2)
      (R : r'=r+v.toNat) (C : c'=c+(!v).toNat) :
      let d := v.toNat
      let d' := d+2
      port true d (actual F P r c)=port false d' (actual F P r' c') ∧
      port true d' (actual F P r' c')=port false d (actual F P r c) := by
    let a := site r c hr hc; let b := site r' c' hr' hc'
    have gr : (gridGraph n n).Adj a b := by
      cases v <;> subst r' <;> subst c' <;> change adjacent .. <;> simp [a,b,site,adjacent]
    have o : outDir a b=v.toNat ∧ outDir b a=v.toNat+2 := by
      cases v <;> subst r' <;> subst c' <;> simp [a,b,site,outDir,Prod.ext_iff,Fin.ext_iff,Fin.lt_def]
    have x := owner_edge F P step arr gr; have y := owner_edge F P step arr gr.symm
    rw [o.1,o.2] at x y
    have z := square_meet F idView r c v
    rw [←R,←C,square_mask F r c hr hc,square_mask F r' c' hr' hc'] at z
    have A := contact_iff F r c hr hc (v:=b) ⟨v.toNat,by cases v <;> decide⟩ (by
      change coord b=shift (coord a) v.toNat; rw [←o.1,shift_out gr])
    have B := contact_iff F r' c' hr' hc' (v:=a) ⟨v.toNat+2,by cases v <;> decide⟩ (by
      change coord a=shift (coord b) (v.toNat+2); rw [←o.2,shift_out gr.symm])
    dsimp only at A B ⊢
    rw [actual_at F P r c hr hc,actual_at F P r' c' hr' hc']
    change contact _ _ ↔ a∈F ∨ b∈F at A
    change contact _ _ ↔ b∈F ∨ a∈F at B
    simp only [port,Bool.true_and,Bool.false_and,Bool.false_xor,Prod.fst,Prod.snd,A,B,x,y,a,b] at *
    cases v <;> simp_all
  exact ⟨fun h => edge false _ _ hr h rfl rfl,fun h => edge true _ _ h hc rfl rfl⟩
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
