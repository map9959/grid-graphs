import GridGraphs.ResidueTwoUpper.OneGap.L7Chart

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.L7
open ResidueZero Stencil

def chartCol {n} (F : Finset (GridVertex n n)) (v : View) (j : Nat) :=
  ((List.finRange 7).map fun i => (marked F (view v n i.val j)).toNat <<< i.val).sum
private def pack7 (f : Fin 7 → Bool) := ((List.finRange 7).map fun i => (f i).toNat <<< i.val).sum
private theorem pack_ok : ∀ f : Fin 7 → Bool, pack7 f<128 ∧ ∀ i : Fin 7,
    lane (pack7 f) i=(f i).toNat := by decide +kernel
theorem col_bit {n} (F : Finset (GridVertex n n)) (v : View) (i : Fin 7) (j : Nat) :
    lane (chartCol F v j) i=(marked F (view v n i.val j)).toNat := (pack_ok _).2 i
theorem col_lt {n} (F : Finset (GridVertex n n)) (v : View) (j : Nat) :
    chartCol F v j<128 := (pack_ok _).1

private theorem view_offset (v : View) (n r j a b : Int) :
    view v (n-2) r j+view v 3 a b=view v n (r+a) (j+b) := by
  cases v with | mk x y s =>
    cases s <;> cases x <;> cases y <;> ext <;> simp [view,reflect] <;> ring

private theorem getbit (a b c : Nat) (r : Nat) (q : Fin 9) :
    lane (window a b c r) q =
      lane (if q.val%3=0 then a else if q.val%3=1 then b else c) (r+q.val/3) := by
  have trunc (x k : Nat) (hk : k<3) : lane (x%8) k=lane x k := by
    interval_cases k <;> norm_num [lane,Nat.shiftRight_eq_div_pow] <;> omega
  have sp (x : Nat) : spread (x%8)=spread x := by simp [spread,trunc]
  let cut (x : Nat) : Fin 8 := ⟨(x>>>r)%8,by omega⟩
  have finite : ∀ x y z : Fin 8, ∀ i : Fin 9,
      lane (spread x+2*spread y+4*spread z) i =
      lane (if i.val%3=0 then x.val else if i.val%3=1 then y.val else z.val) (i.val/3) := by native_decide
  have H := finite (cut a) (cut b) (cut c) q
  dsimp only [cut] at H
  simp only [sp] at H
  unfold window; rw [H]
  split_ifs <;> rw [trunc _ _ (by have := q.isLt; omega)] <;>
    simp [lane,Nat.shiftRight_add]

/-- The scan reads the nine physical marks in this very patch, in scan order. -/
theorem window_encode (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (v : View) (r j : Nat) (hr : r<5) (a : origins (35+42*u))
    (ha : coord a=view v ((35+42*(u:Int))-2) r j) :
    encode (maskAt F a) v=window (chartCol F v j) (chartCol F v (j+1)) (chartCol F v (j+2)) r := by
  let n := 35+42*u
  let N : Int := 35+42*(u:Int)
  have hn : (n:Int)=N := by dsimp [n,N]
  let m := maskAt F a
  let X := chartCol F v
  let W := window (X j) (X (j+1)) (X (j+2)) r
  have E (q : Fin 9) : lane W q = bit m (posIdx (view v 3 (q.val/3:Nat) (q.val%3:Nat))) := by
    let off := view v 3 (q.val/3:Nat) (q.val%3:Nat)
    have ho : inside 3 off := inside_view (n:=3) v (by have := q.isLt; omega) (by omega)
    have bound : posIdx off < 9 := by simp [inside] at ho; unfold posIdx; omega
    let t : Fin 9 := ⟨_,bound⟩
    have B := patch_bit F a.1.val a.2.val (by have := a.1.isLt; omega)
      (by have := a.2.isLt; omega) t
    change bit m t=(marked F (coord a+offset t)).toNat at B
    have O : offset t=off := by
      simp [inside] at ho; ext <;> simp [t,offset,posIdx] <;> omega
    rw [ha,O] at B
    dsimp only [off] at B
    rw [view_offset] at B
    change lane (window ..) q=bit m t
    rw [B,getbit]
    let row : Fin 7 := ⟨r+q.val/3,by have := q.isLt; omega⟩
    have cb (j' : Nat) := col_bit F v row j'
    change lane (if q.val%3=0 then X j else if q.val%3=1 then X (j+1) else X (j+2)) row=_
    have eqn : ((35+42*u:Nat):Int)=N := hn
    have rr : (row.val:Int)=(r:Int)+(q.val/3:Nat) := Nat.cast_add .. 
    have E' (k : Nat) (hk : k=q.val%3) : marked F (view v N ((r:Int)+(q.val/3:Nat)) (↑(j+k):Int)) =
        marked F (view v N ((r:Int)+(q.val/3:Nat)) ((j:Int)+(q.val%3:Nat))) := by simp [hk]
    split_ifs <;> rw [cb,eqn,rr] <;> apply congrArg Bool.toNat
    · simpa using E' 0 (by omega)
    · exact E' 1 (by omega)
    · exact E' 2 (by omega)
  have sumBits : ∀ z : Fin 512, ((List.finRange 9).map fun (q : Fin 9) => lane z q <<< q.val).sum=z.val := by native_decide
  have bound : W<512 := by dsimp [W,window,spread,lane]; omega
  have ee : encode m v=W := by
    unfold encode; simp_rw [←E]; exact sumBits ⟨_,bound⟩
  exact ee

theorem local_band (checked : catCheck) (u : Nat)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (P : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u))
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (wp : ∀ a, patchSlack F a=0 ∨ patchSlack F a=full)
    (v : View) (j : Nat) (hj : j<33+42*u)
    (zs : ∀ (r : Nat), r<5 → (r≠4 ∨ fold u j≠31) → ∀ x,
      coord x=view v (35+42*(u:Int)) ((r:Int)+1) ((j:Int)+1) → starSlack F P x=0) :
    band (fold u j) (chartCol F v j) (chartCol F v (j+1)) (chartCol F v (j+2)) := by
  let n := 35+42*u
  let N : Int := 35+42*(u:Int)
  have hn : (n:Int)=N := by dsimp [n,N]
  have hS : ((n-2:Nat):Int)=N-2 := by dsimp [n,N]; omega
  have h33 : N-2=33+42*(u:Int) := by dsimp [N]; ring
  apply List.all_eq_true.mpr
  intro r h
  have hr := List.mem_range.mp h
  apply Bool.or_eq_true_iff.mpr
  by_cases active : r≠4 ∨ fold u j≠31
  swap
  · left; simp_all
  right
  let aa := view v (N-2) r j
  let pp := view v N ((r:Int)+1) ((j:Int)+1)
  let a := onSite (s:=n-2) aa (by
    dsimp [aa]; rw [←hS]; apply inside_view <;> dsimp [n] <;> omega)
  let p := onSite (s:=n) pp (by
    dsimp [pp]; rw [←hn]; exact_mod_cast inside_view (n:=n) (r:=r+1) (j:=j+1) v
      (by dsimp [n]; omega) (by dsimp [n]; omega))
  have ha : coord a=aa := coord_onSite ..
  have hp : coord p=pp := coord_onSite ..
  have eq : coord p=coord a+(1,1) := by rw [hp,ha]; exact (view_center ..).symm
  let m := maskAt F a
  obtain ⟨e₁,e₂⟩ := PatchFilter.packed_center F a p eq
  let o : Fin 5 := ⟨outDir p (P p),outDir_lt ..⟩
  have st := zs r hr active p hp
  change twoOrbitStar (n:Int) _ _ _ _=0 at st
  rw [←e₁,←e₂,hp,hn] at st
  have st' := (sameStar v u r j hr (bit m 4) (PatchFilter.cnb m) o).symm.trans st
  have fj : fold u j<33 := by unfold fold; split_ifs <;> omega
  let pos := view v 33 r (fold u j)
  have starPos : pos+(1,1)=view v 35 ((r:Int)+1) ((fold u j:Int)+1) := view_center v 35 _ _
  have inside' (d : Nat) : inside 35 (shift (pos+(1,1)) d) := by
    have h := inside_view (n:=33) v (r:=r) (by omega) (j:=fold u j) fj
    change inside 33 pos=true at h
    simp [inside] at h
    unfold shift; split <;> simp [inside] <;> omega
  have ok := starOK_physical F acy p _ (fun h => step _ h.symm)
  rw [←e₁,←e₂] at ok
  have ok' : starOK 35 (pos+(1,1)) (bit m 4) (PatchFilter.cnb m) o := by
    unfold starOK at ok ⊢
    simp only [inside',Bool.true_and,Bool.and_eq_true,Bool.or_eq_true,List.all_eq_true] at *
    exact ⟨fun d hd => (ok.1 _ hd).imp_right And.right,ok.2.imp_right And.right⟩
  have w0 : twoOrbitPatch 35 pos m=0 ∨ twoOrbitPatch 35 pos m=full := by
    have w := wp a
    change twoOrbitPatch (n:Int) (coord a) m=0 ∨ twoOrbitPatch (n:Int) (coord a) m=full at w
    rw [ha,hn] at w
    dsimp only [aa] at w; rw [h33,samePatch v u r j hr] at w
    exact w
  have C := of_decide_eq_true checked v ⟨r,hr⟩ ⟨fold u j,fj⟩ m
  have valid : allowed r (fold u j) (encode m v) := by
    change ((!maskOK m || allowed r (fold u j) (encode m v) || _ || _)=true) at C
    have clean : maskOK m := physical_mask_ok F acy ..
    have st'' : twoOrbitStar 35 (pos+(1,1)) (bit m 4) (PatchFilter.cnb m) o=0 := starPos ▸ st'
    simp only [clean,Bool.not_true,Bool.false_or,Bool.or_eq_true,Bool.not_eq_true',
      List.all_eq_true,List.mem_range,Bool.not_eq_false',beq_iff_eq,bne_iff_ne] at C
    rcases C with (yes|bad)|all
    · exact yes
    · rcases w0 with w|w <;> simp_all [pos]
    · specialize all o o.isLt
      change (starOK 35 (pos+(1,1)) _ _ o=false ∨ twoOrbitStar 35 (pos+(1,1)) _ _ o≠0) at all
      simp [ok',st''] at all
  rw [window_encode u F v r j hr a ha] at valid
  exact valid

theorem physical_band (checked : catCheck) (u : Nat)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (P : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u))
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (zs : ∀ x, starSlack F P x=0) (wp : ∀ a, patchSlack F a=0 ∨ patchSlack F a=full)
    (v : View) (j : Nat) (hj : j<33+42*u) :
    band (fold u j) (chartCol F v j) (chartCol F v (j+1)) (chartCol F v (j+2)) :=
  local_band checked u F acy P step wp v j hj (fun _ _ _ x _ => zs x)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.L7
