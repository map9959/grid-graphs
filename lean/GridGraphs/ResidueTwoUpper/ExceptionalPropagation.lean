import GridGraphs.ResidueTwoUpper.ExceptionalTransport

namespace GridGraphs.ResidueTwoUpper.Exceptional
open ResidueZero Stencil Finset

private theorem same {n} (hn : 2≤n) (F : Finset (GridVertex n n)) (v : GridVertex n n)
    (a : origins n) (q : Fin 9) (eq : coord v=coord a+offset q) (b : Bool) :
    starRank n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) b q =
      patchRank n (coord a) (maskAt F a) b q := by
  have ok := coord_inside a
  rw [Nat.cast_sub hn] at ok
  norm_num1 at ok
  have ev := physical_incidence_key F a.1 a.2 (by have := a.1.isLt; omega)
    (by have := a.2.isLt; omega) q 0
  have ident : ∀ (q : Fin 9) (nb : Fin 16) (m : Fin 512),
      patchQ 0 q=q ∧ rotBits 0 nb=nb ∧ rotMask 0 m=m := by native_decide
  obtain ⟨q0,nb0,m0⟩ := ident q ⟨neighbours F (coord v),code_lt _⟩ (maskAt F a)
  change localEvent (patchQ 0 q) (marked F (coord a+offset q)).toNat
    (rotBits 0 (neighbours F (coord a+offset q))) = localEvent (patchQ 0 q)
      (bit (rotMask 0 (maskAt F a)) (patchQ 0 q)) (patchNbr (rotMask 0 (maskAt F a)) (patchQ 0 q)) at ev
  rw [←eq,q0,marked_at,nb0,m0] at ev
  change localEvent q (decide (v∈F)).toNat (neighbours F (coord v))=_ at ev
  have back : coord v-offset q=coord a := sub_eq_iff_eq_add.mpr eq
  unfold starRank patchRank
  rw [back,if_pos ok,ev,eq]

def occurrence (n : Nat) := GridVertex n n ⊕ origins n
def weightAt {n} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n) :
    occurrence n → Int := Sum.elim (starSlack F P) (patchSlack F)
def rankAt {n} (F : Finset (GridVertex n n)) (own : Bool) : occurrence n → Fin 9 → Nat :=
  Sum.elim (fun v => starRank n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) (!own))
    (fun a => patchRank n (coord a) (maskAt F a) own)

theorem opposite {n} (hn : 2≤n) (F : Finset (GridVertex n n)) (x : occurrence n) (q : Fin 9)
    (pos : 0<rankAt F false x q) : ∃ y, rankAt F true y q=rankAt F false x q := by
  cases x with
  | inl v =>
    have h : inside ((n:Int)-2) (coord v-offset q) := by
      by_contra bad
      simp [rankAt,starRank,bad] at pos
    have h' : inside (n-2:Nat) (coord v-offset q) := by simpa [Nat.cast_sub hn] using h
    let a := onSite _ h'
    have eq : coord v=coord a+offset q := by rw [show coord a=_ from coord_onSite ..]; simp
    exact ⟨Sum.inr a,(same hn F v a q eq true).symm⟩
  | inr a =>
    have h : inside n (coord a+offset q) := by
      have h₁ := a.1.isLt; have h₂ := a.2.isLt; have h₃ := q.isLt
      have h₄ : q.val/3<3 := by omega
      have h₅ : q.val%3<3 := Nat.mod_lt _ (by decide)
      have ha : inside n ((a.1.val:Int)+(q.val/3:Nat),(a.2.val:Int)+(q.val%3:Nat)) := by
        simp only [inside,Bool.and_eq_true,decide_eq_true_eq]; omega
      exact ha
    let v := onSite _ h
    exact ⟨Sum.inl v,same hn F v a q (coord_onSite ..) false⟩

theorem eliminate {n} (hn : 2≤n) (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (h : ∀ x, traceOK (rankAt F true x) (rankAt F false x) (weights (weightAt F P x))) :
    ∀ x, weights (weightAt F P x) := by
  have none (r : Nat) : ∀ x q, rankAt F true x q=r → r≠0 → False := by
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro x q eq pos
      obtain ⟨j,low,lt⟩ := (h x).1 q (eq ▸ pos)
      obtain ⟨y,other⟩ := opposite hn F x j low
      exact ih _ (lt.trans_eq eq) y j other low.ne'
  intro x
  by_contra bad
  obtain ⟨j,val⟩ := (h x).2 (by simpa using bad)
  obtain ⟨y,other⟩ := opposite hn F x j val
  exact none _ y j other val.ne'

attribute [local irreducible] messages rank
set_option maxHeartbeats 900000 in
theorem physical_weights (checked_stars : baseStars) (checked_patches : basePatches) (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (P : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u))
    (acy : (Bonds F).IsAcyclic) (step : ∀ v, P v≠v → (Bonds F).Adj v (P v))
    (total : (∑ x, starSlack F P x)+(∑ x, patchSlack F x)=full) :
    ∀ x, weights (weightAt F P x) := by
  let n := 35+42*u
  let j := 4+14*u
  have e : (n:Int)=23+3*(j:Int) := by dsimp [n,j]; omega
  have ep : ((n-2:Nat):Int)=21+3*(j:Int) := by dsimp [n,j]; omega
  have sOK (v : GridVertex n n) := starOK_physical F acy v (P v) (fun h => step _ h.symm)
  have pOK (v : origins n) := physical_mask_ok F acy v.1 v.2
    (by have := v.1.isLt; omega) (by have := v.2.isLt; omega)
  have e' : (n:Int)=20+3*((j+1:Nat):Int) := by omega
  have ep' : ((n-2:Nat):Int)=18+3*((j+1:Nat):Int) := by omega
  have nnS (v : GridVertex n n) : 0 ≤ starSlack F P v := by
    unfold starSlack; rw [e']
    exact star_nonneg_of_check checkStars _ (e' ▸ coord_inside v)
      (by cases decide (v∈F) <;> decide) (code_lt _) (outDir_lt ..) (e' ▸ sOK v)
  have nnP (v : origins n) : 0 ≤ patchSlack F v := by
    unfold patchSlack; rw [e']
    exact patch_nonneg_of_check checkPatches _ (ep' ▸ coord_inside v) (Fin.isLt _) (pOK v)
  have ss := sum_nonneg (s:=univ) (fun x _ => nnS x)
  have pp := sum_nonneg (s:=univ) (fun x _ => nnP x)
  apply eliminate (n:=n) (by dsimp [n]; omega)
  intro x
  cases x with
  | inl v =>
    have l := single_le_sum (s:=univ) (f:=starSlack F P) (fun x _ => nnS x) (mem_univ v)
    have cheap : starSlack F P v≤full := by linarith
    change traceOK (starRank n _ _ _ false) (starRank n _ _ _ true) (weights (twoOrbitStar n _ _ _ _))
    unfold starSlack at cheap
    rw [e] at cheap ⊢
    let f : Fin 2 := ⟨(decide (v∈F)).toNat,by cases decide (v∈F) <;> decide⟩
    let nb : Fin 16 := ⟨neighbours F (coord v),code_lt _⟩
    let o : Fin 5 := ⟨outDir v (P v),outDir_lt ..⟩
    have hp : inside (23+3*(j:Int)) (coord v) := e ▸ coord_inside v
    have legal : starOK (23+3*(j:Int)) (coord v) f nb o := e ▸ sOK v
    exact traces_star checked_stars j hp f nb o legal cheap
  | inr a =>
    have l := single_le_sum (s:=univ) (f:=patchSlack F) (fun x _ => nnP x) (mem_univ a)
    have cheap : patchSlack F a≤full := by linarith
    change traceOK (patchRank n _ _ true) (patchRank n _ _ false) (weights (twoOrbitPatch n _ _))
    unfold patchSlack at cheap
    rw [e] at cheap ⊢
    exact traces_patch checked_patches j (ep ▸ coord_inside a) _ (pOK a) cheap

end GridGraphs.ResidueTwoUpper.Exceptional
