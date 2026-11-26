import GridGraphs.NoPitch.Budget.StarPaths

namespace GridGraphs.NoPitch.Budget
open PitchCut Finset Keys GridGraphs.NoPitch.Dual
attribute [local irreducible] chart19 chart58 chart61
variable {k : Nat}

def eventPrice (x : Site k) (f : Bool) (bits : Fin 4 → Bool) (o : Option (Fin 4)) :=
  pathBit x f bits + 2*(sinkBit x o).toNat + 2*(exitBit x f bits o).toNat

private theorem count_iff {A : Type} [Fintype A] (b : A → Bool) (s : Finset A)
    (h : ∀ x, b x=true ↔ x∈s) : ∑ x, (b x).toNat=s.card := by
  classical
  have eq (x : A) : (b x).toNat=if x∈s then 1 else 0 := by simp only [←h x]; cases b x <;> rfl
  simp [eq]

theorem physical_events_sum (F : Finset (Site k)) (acy : (G F).IsAcyclic) :
    ∑ x, eventPrice x (decide (x∈F)) (bitsAt F x) (out F x)=2*(k+1)^2 := by
  simp only [eventPrice,sum_add_distrib,←mul_sum,pathBit_sum,
    count_iff _ _ (sinkBit_iff F),count_iff _ _ (exitBit_iff F)]
  have p := physical_paths_sinks_exits F acy
  rw [paths_eq] at p
  have n : (liveSegs F).card+(sinks F).card+(exits F).card=(k+1)^2 := by exact_mod_cast p
  omega

def lookupPrice (D : Chart) (i : Nat) (m : Index) (key : Nat) :=
  ((locate D m key).map fun j => coeff i D.cols[j].terms*(D.cols[j].units:Int)).getD 0

def checkEvents (D : Chart) (k i : Nat) :=
  let m := index D
  decide (∀ (x : Site k) (bits : Fin 4 → Bool), allowed x bits →
    ∀ (f : Bool) (o : Option (Fin 4)),
      (∀ d∈o, (probe x d.val).isSome ∧ (f || bits d)) →
      ((!f && !bits 0 && !bits 1 && !bits 2 && !bits 3) → o.isNone) →
      lookupPrice D i m (8*starCode (N k) x.1.val x.2.val (sampled x bits) o + f.toNat)=
        8*(eventPrice x f bits o:Int))

def onlyStars (D : Chart) (i : Nat) :=
  D.cols.all fun c => c.key%8<2 || coeff i c.terms==0

private theorem check19 : checkEvents chart19 6 1928 := by native_decide
private theorem support19 : onlyStars chart19 1928 := by native_decide
private theorem meta19 : ∃ i : Fin chart19.rows.size, i.val=1928 ∧ chart19.rows[i].source=4675 ∧
    chart19.rows[i].sense=0 ∧ chart19.rows[i].rhs=⟨196,0,0⟩ := by native_decide

private theorem physical_price (D : Chart) (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (i : Nat) (ok : checkEvents D k i) (x : Site k) :
    lookupPrice D i (index D) (Keys.star F (out F) x)=
      8*(eventPrice x (decide (x∈F)) (bitsAt F x) (out F x):Int) := by
  have step {d} (hd : d∈out F x) : x∈F ∨ bitsAt F x d := by
    have ne : parent F x≠x := fun h => by rw [(out_none F x).mpr h] at hd; cases hd
    have e := (CapBill.parent_step _ (sectionRoot F) (mt (CapBill.parent_fix _ _ x).mpr ne)).1.2
    change x∈F ∨ parent F x∈F at e
    exact e.imp_right (fun h => by simp [bitsAt,out_points F x d hd,h])
  have pass := of_decide_eq_true ok x (bitsAt F x) (bits_allowed F acy x) (decide (x∈F)) (out F x)
    (fun d h => ⟨out_inside F x d h,by simpa using step h⟩)
  have iso : ((!decide (x∈F) && !bitsAt F x 0 && !bitsAt F x 1 && !bitsAt F x 2 &&
      !bitsAt F x 3)=true) → (out F x).isNone := by
    intro h
    cases o : out F x with
    | none => rfl
    | some d =>
      have p := step (d:=d) (by simp [o])
      fin_cases d <;> simp_all
  have code : starCode (N k) x.1.val x.2.val (sampled x (bitsAt F x)) (out F x)=
      starCode (N k) x.1.val x.2.val (neighbor F x) (out F x) := by
    unfold starCode
    apply congrArg minimum; funext g
    have eq (d : Nat) := sampled_bits F x (⟨direction (invers g) d,by unfold direction; omega⟩ : Fin 4)
    simp only [eq]
  simpa only [Keys.star,code] using pass iso

theorem scatter_price {A : Type} [Fintype A] (D : Chart) (i : Fin D.rows.size) (f : A → Nat) :
    lhs D (scatter D (index D) f) i=∑ a, lookupPrice D i (index D) (f a) := by
  unfold lhs scatter
  simp_rw [mul_sum]; rw [sum_comm]
  apply sum_congr rfl; intro a _
  cases e : locate D (index D) (f a) with
  | none => simp [lookupPrice,e]
  | some j => simp [lookupPrice,e]

theorem starRow {D : Chart} (F : Finset (Site k)) (o : Site k → Option (Fin 4))
    (i : Fin D.rows.size) (h : onlyStars D i) :
    lhs D (physicalVector D F o) i=∑ x, lookupPrice D i (index D) (Keys.star F o x) := by
  have kill {j : Fin D.cols.size} (non : 2≤D.cols[j].key%8) : coeff i D.cols[j].terms=0 := by
    have z := Array.all_eq_true_iff_forall_mem.mp h _ (Array.getElem_mem j.isLt)
    simp only [Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq] at z
    exact z.resolve_left (not_lt.mpr non)
  have no (key : Nat) (non : 2≤key%8) : lookupPrice D i (index D) key=0 := by
    unfold lookupPrice; cases e : locate D (index D) key with
    | none => rfl
    | some j => change coeff i D.cols[j].terms*_=0; rw [kill (j:=j) ((locate_key e).symm ▸ non),zero_mul]
  have a (p : FacePos k) : lookupPrice D i (index D) (face F p)=0 := by
    apply no; unfold face faceCode keyAt; omega
  have b (t : Fin 8 × J k × J k) : lookupPrice D i (index D) (line F t.1 t.2.1 t.2.2)=0 := by
    apply no; unfold line; dsimp only; omega
  have c (p : PatchPos k) : lookupPrice D i (index D) (patch F p)=0 := by
    apply no; unfold patch patchCode; omega
  have add (u v : Fin D.cols.size → Int) : lhs D (fun j => u j+v j) i=lhs D u i+lhs D v i := by
    simp [lhs,mul_add,sum_add_distrib]
  have aux : lhs D (fun j : Fin D.cols.size =>
      if D.cols[j].key%8=5 then complete F (D.cols[j].key/8) else 0) i=0 := by
    apply sum_eq_zero; intro j _
    dsimp only
    split <;> rename_i q
    · rw [kill (by omega : 2≤D.cols[j].key%8),zero_mul]
    · simp
  unfold physicalVector counts
  rw [add,add,add,add,aux]
  simp only [scatter_price,a,b,c,sum_const_zero,add_zero]

theorem realizedRow19 (F : Finset (Site 6)) (acy : (G F).IsAcyclic) :
    ∃ i : Fin chart19.rows.size, i.val=1928 ∧ chart19.rows[i].source=4675 ∧
      rowHolds chart19.rows[i].sense (2*lhs chart19 (physicalVector chart19 F (out F)) i)
        (8*chart19.rows[i].rhs.atStep 0) := by
  obtain ⟨i,hi,src,sense,rhs⟩ := meta19
  refine ⟨i,hi,src,?_⟩
  rw [sense,rhs,starRow F _ i (hi ▸ support19)]
  simp only [hi,physical_price chart19 F acy _ check19,←mul_sum,←Nat.cast_sum,physical_events_sum F acy]
  rfl

end GridGraphs.NoPitch.Budget
