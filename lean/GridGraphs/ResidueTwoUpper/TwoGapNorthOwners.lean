import GridGraphs.ResidueTwoUpper.TwoGapNorthColumns

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North.Scan
open ResidueZero Stencil Words

def vertex {n} (r j : Nat) (hr : r<n) (hj : j<n) : GridVertex n n := (⟨r,hr⟩,⟨j,hj⟩)
def arrow {n} (P : GridVertex n n → GridVertex n n) (r j : Nat) :=
  if h : r<n ∧ j<n then outDir (vertex r j h.1 h.2) (P (vertex r j h.1 h.2)) else 4
def west {n} (P : GridVertex n n → GridVertex n n) (j : Nat) := pack fun r => arrow P r j==2
private theorem west_bit {n} (P : GridVertex n n → GridVertex n n) (j r : Nat) (hr : r<6) :
    bit (west P j) r=(arrow P r j==2).toNat :=
  (by native_decide : ∀ f : Fin 6 → Bool, ∀ r : Fin 6, bit (pack f) r=(f r).toNat) _ ⟨r,hr⟩

private theorem points {n} {F : Finset (GridVertex n n)} {P : GridVertex n n → GridVertex n n}
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x)) (x y : GridVertex n n)
    (d : Fin 4) (eq : shift (coord x) d=coord y) : outDir x (P x)=d ↔ P x=y := by
  have fixed : x≠y := by
    rintro rfl; fin_cases d <;> simp [shift,coord,Prod.ext_iff] at eq <;> omega
  constructor
  · intro h
    by_cases fx : P x=x
    · rw [fx] at h; simp [outDir] at h; have := d.isLt; omega
    · apply coord_injective
      rw [←shift_out (step _ fx).1,h,eq]
  · rintro h; rw [h]; unfold outDir; rw [if_neg fixed]
    fin_cases d <;> dsimp [shift,coord] at eq ⊢ <;> simp only [Prod.mk.injEq] at eq <;> simp only [Fin.lt_def] <;> split_ifs <;> omega

private theorem field {n} {F : Finset (GridVertex n n)} {P : GridVertex n n → GridVertex n n}
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (arr : ∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) (x y : GridVertex n n)
    (d e : Fin 4) (toY : shift (coord x) d=coord y) (toX : shift (coord y) e=coord x)
    (grid : (gridGraph n n).Adj x y) :
    (outDir x (P x)==d.val).toNat+(outDir y (P y)==e.val).toNat=(decide (x∈F ∨ y∈F)).toNat := by
  have a := points step x y d toY; have b := points step y x e toX
  by_cases active : x∈F ∨ y∈F
  · have h := arr _ _ ⟨grid,active⟩
    by_cases xy : P x=y
    · simp [a.mpr xy,show outDir y (P y)≠e.val from mt b.mp (h.mp xy),active]
    · have yx : P y=x := by by_contra no; exact xy (h.mpr no)
      simp [mt a.mp xy,b.mpr yx,active]
  · have none {x y : GridVertex n n} (miss : ¬(x∈F ∨ y∈F)) (ne : x≠y) : P x≠y := by
      intro eq; have path := step x (by rw [eq]; exact Ne.symm ne); exact miss (eq ▸ path.2)
    simp [active,mt a.mp (none active grid.ne),mt b.mp (none (fun h => active h.symm) grid.ne.symm)]

private theorem no_east_last {u d} {F : Finset (GridVertex (35+42*u) (35+42*u))} {P}
    (C : Chart F P d) (x : GridVertex (35+42*u) (35+42*u)) (end' : x.2.val+1=35+42*u) :
    outDir x (P x)≠0 := by unfold outDir; have := (P x).2.isLt; simp only [Fin.lt_def]; split_ifs <;> omega
private theorem no_north {u d} {F : Finset (GridVertex (35+42*u) (35+42*u))} {P}
    (C : Chart F P d) (x : GridVertex (35+42*u) (35+42*u)) (top : x.1.val=0) :
    outDir x (P x)≠3 := by
  by_cases h : P x=x
  · simp [outDir,h]
  · intro eq; have move := shift_out (C.step _ h).1
    rw [eq] at move; simp [shift,coord,Prod.ext_iff,top] at move

private def partialMask {n} (P : GridVertex n n → GridVertex n n) (j r : Nat) :=
  ∑ k ∈ Finset.range r, if arrow P k j=2 then 2^k else 0
private theorem partialMask_all {n} (P : GridVertex n n → GridVertex n n) (j : Nat) :
    partialMask P j 6=west P j := by
  let f (r : Nat) := if arrow P r j=2 then 2^r else 0
  have h : ∑ i ∈ Finset.range 6, f i=∑ i : Fin 6, f i.val := Finset.sum_range ..
  rw [show partialMask P j 6=∑ i ∈ Finset.range 6,f i by rfl,h]
  unfold west pack
  rw [←List.ofFn_eq_map]; simp only [List.sum_ofFn]
  apply Finset.sum_congr rfl; intro i _
  dsimp [f]; by_cases eq : arrow P i.val j=2 <;> simp [eq,Nat.shiftLeft_eq]

theorem owner_pass {u d j : Nat} {F : Finset (GridVertex (35+42*u) (35+42*u))} {P}
    (C : Chart F P d) (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (wrong : d%3≠2) (hj : j<35+42*u) :
    west P (j+1) ∈ owners (tag u j) (X F (j-1:Int)) (X F j) (X F (j+1:Int)) (west P j) := by
  let n := 35+42*u
  have end' : tag u j=34 ↔ j+1=n := by dsimp [tag,n]; split_ifs <;> omega
  have bound : tag u j<35 := by unfold tag; split_ifs <;> omega
  let v (r : Nat) (h : r<6) := vertex r j (n:=n) (by dsimp [n]; omega) hj
  have dir (r) (h : r<6) : arrow P r j=outDir (v r h) (P (v r h)) := by unfold arrow; rw [dif_pos ⟨by dsimp [n] at *; omega,hj⟩]
  have mark (r) (h : r<6) : bit (X F j) r=(decide (v r h∈F)).toNat := (X_bit F _ _ h).trans (congrArg Bool.toNat (marked_at F (v r h)))
  have pair (r) (hr : r<6) (next : j+1<n) :
      (arrow P r j==0).toNat+(arrow P r (j+1)==2).toNat=
        (decide (bit (X F j) r+bit (X F (j+1:Int)) r>0)).toNat := by
    let y := vertex r (j+1) (n:=n) (by dsimp [n]; omega) next
    have e : (gridGraph n n).Adj (v r hr) y := Or.inl ⟨rfl,Or.inl rfl⟩
    have f := field C.step C.arrows (v r hr) y 0 2 (by ext <;> simp [coord,v,y,vertex,shift]) (by ext <;> simp [coord,v,y,vertex,shift]) e
    have ym : bit (X F (j+1:Int)) r=(decide (y∈F)).toNat := (X_bit F _ _ hr).trans (by rw [←marked_at F y]; simp [y,coord,vertex])
    rw [mark r hr,ym,dir r hr]
    change _+(arrow P r (j+1)==2).toNat=_
    rw [show arrow P r (j+1)=outDir y (P y) by unfold arrow; rw [dif_pos ⟨by dsimp [n] at *; omega,next⟩]]
    by_cases xM : v r hr∈F <;> by_cases yM : y∈F <;> simpa [xM,yM] using f
  rw [←partialMask_all P (j+1)]
  apply owners_sound _ _ _ _ _ (fun r => arrow P r j) (partialMask P (j+1)) (by simp [partialMask])
  · intro r hr
    unfold dirs; split_ifs with bottom
    · have lt : arrow P r j<5 := (dir r hr) ▸ outDir_lt ..
      simp only [List.mem_cons,List.not_mem_nil,or_false]; omega
    · have small : r<5 := by omega
      have f := star_entry C acy score wrong (v r hr) rfl small
      have bitOk := mark r hr
      have nbOk := local_nb (j:=j) F small
      let nb := neighbours F (coord (v r hr))
      change nbAt _ _ _ r=nb at nbOk
      have nbLim : nb<16 := code_lt _
      have fLim : (decide (v r hr∈F)).toNat<2 := by cases decide (v r hr∈F) <;> decide
      simp [st,bound,small,bitOk,nbOk,fLim,nbLim,dir r hr,List.mem_filter, outDir_lt]
      exact f
  · intro r hr; rw [west_bit P j r hr]; cases (arrow P r j==2) <;> decide
  · intro r hr
    by_cases top : r=0
    · subst r
      have no : arrow P 0 j≠3 := (dir 0 hr) ▸ no_north C _ rfl
      simp [no]
    · have prev : r-1<6 := by omega
      have e : (gridGraph n n).Adj (v (r-1) prev) (v r hr) := Or.inr ⟨rfl,Or.inl (by dsimp [v,vertex]; omega)⟩
      have f := field C.step C.arrows (v (r-1) prev) (v r hr) 1 3
        (by ext <;> norm_num [coord,v,vertex,shift] <;> omega) (by ext <;> norm_num [coord,v,vertex,shift] <;> omega) e
      rw [dir _ prev,dir _ hr,mark _ hr,mark _ prev]
      by_cases xM : v (r-1) prev∈F <;> by_cases yM : v r hr∈F <;> simpa [bne_iff_ne.mpr top,show 0<r by omega,xM,yM] using f
  · intro r hr dir0
    by_cases last : j+1=n
    · exact False.elim (no_east_last C (v r hr) last ((dir r hr).symm.trans dir0))
    · have f := pair r hr (by omega)
      refine ⟨mt end'.mp last,?_⟩
      by_contra h; simp only [dir0,beq_self_eq_true,Bool.toNat_true,decide_eq_false h,Bool.toNat_false] at f; omega
  · intro r hr
    unfold partialMask; rw [Finset.sum_range_succ]
    congr 1
    by_cases last : j+1=n
    · have endj := end'.mpr last
      simp [endj,arrow,show ¬j+1<35+42*u by dsimp [n] at last; omega]
    · have f := pair r hr (by omega)
      have neq := mt end'.mp last
      have tab : ∀ a b c : Bool, a.toNat+b.toNat=c.toNat → b=(c && !a) := by decide
      have test := tab _ _ _ f
      simp only [bne_iff_ne.mpr neq,Bool.true_and,bne_eq,←test,beq_iff_eq]

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North.Scan
