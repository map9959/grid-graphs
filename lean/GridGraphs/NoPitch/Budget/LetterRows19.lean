import GridGraphs.NoPitch.Budget.Flow19

namespace GridGraphs.NoPitch.LocalBoard19
open Budget PitchCut Keys GridGraphs.NoPitch.Dual Finset FaceRows
attribute [local irreducible] chart19

def letterNo (a : Letter) := 1+4*a.l.toNat+2*a.z.toNat+a.r.toNat
def slotNo (r j : Fin 7) (a : Letter) := (7*r.val+j.val)*9+letterNo a
def letterTable (D : Chart) : Array Terms := Id.run do
  let mut tab : Array Terms := Array.replicate 442 []
  for c in D.cols do
    if c.key%8==3 then
      let n := c.key/8
      let p := n/8100
      let idx := (p/1024/3*7+p%32/3)*9+n%90/2%9
      for (i,v) in c.terms do
        if lineLetters i && v>0 then
          let ts := tab[idx]?.getD []
          if !(ts.contains (i,1)) then tab := tab.setIfInBounds idx ((i,1)::ts)
  return tab
def letterStamp (A : Array Terms) (r j : Fin 7) (a : Letter) := A[slotNo r j a]?.getD []
def asSite (r j : Fin 7) : X := (teeth 6 r,teeth 6 j)
def rotatedLetter (g : Fin 8) (f : Bool) (bits : Fin 4 → Bool) : Letter :=
  ⟨bits (Fin.ofNat 4 (direction (invers g) 2)),f,bits (Fin.ofNat 4 (direction (invers g) 0))⟩
def fromSite (A : Array Terms) (x : X) (g : Fin 8) (f : Bool) (bits : Fin 4 → Bool) :=
  let y := small 19 g x
  if y.1.val%3=0 ∧ y.2.val%3=0 then
    letterStamp A (owner y.1) (owner y.2) (rotatedLetter g f bits) else []
def starStamp (A : Array Terms) (x : X) (f : Bool) (bits : Fin 4 → Bool) :=
  (List.finRange 8).flatMap fun g => fromSite A x g f bits
def letterCheck (D : Chart) :=
  let w := contribution D (index D) (prices D lineLetters)
  let A := letterTable D
  decide (∀ (r j : Fin 7), ∀ s∈LineKeys.states j.val, ∀ a : Letter, LineKeys.allowedStep j.val s a →
    balanced (w (LineKeys.key r j.val s (advance s a)) ++ negTerms (letterStamp A r j a))) &&
  decide (∀ (x : X) (bits : Fin 4 → Bool) (f : Bool) (o : Option (Fin 4)),
    permissible x bits f o → (∀ d, bits d → (probe x d.val).isSome) →
    balanced (w (localStar x f bits o) ++ starStamp A x f bits))
def starLineOnly (D : Chart) := D.cols.all fun c => c.key%8<2 || c.key%8==3 ||
    c.terms.all (fun t => !lineLetters t.1)
private theorem check : letterCheck chart19 := by native_decide
private theorem support : starLineOnly chart19 := by native_decide
private theorem metaInfo : ∀ i : Fin chart19.rows.size, lineLetters i → chart19.rows[i].rhs=⟨0,0,0⟩ := by native_decide

private theorem vmem (F : Finset X) (g : Fin 8) (p : X) : p∈view F g ↔ small 19 (invers g) p∈F := by
  have a : ∀ (g : Fin 8) (p : X), small 19 (invers g) (small 19 g p)=p := by native_decide
  have b : ∀ (g : Fin 8) (p : X), small 19 g (small 19 (invers g) p)=p := by native_decide
  constructor
  · intro m; obtain ⟨y,m,rfl⟩ := mem_image.mp m; rwa [a]
  · intro m; exact b g p ▸ mem_image_of_mem (small 19 g) m

private def leftProbe (r j : Fin 7) : Option X :=
  if j.val=0 then none else some (teeth 6 r,Fin.ofNat 19 (3*j.val-1))
private def rightProbe (r j : Fin 7) : Option X :=
  if j.val=6 then none else some (teeth 6 r,Fin.ofNat 19 (3*j.val+1))

private theorem slot_letter (F : Finset X) (r j : Fin 7) :
    L F r j=⟨(leftProbe r j).any (fun x => decide (x∈F)),decide (asSite r j∈F),
    (rightProbe r j).any (fun x => decide (x∈F))⟩ := by
  fin_cases j <;> simp [L,letter,leftProbe,rightProbe,asSite,bit,N] <;> first | rfl | exact ⟨rfl,Iff.rfl⟩

private theorem rot_agrees (F : Finset X) (g : Fin 8) (r j : Fin 7) :
    let x := small 19 (invers g) (asSite r j)
    rotatedLetter g (decide (x∈F)) (bitsAt F x)=L (view F g) r j := by
  let x := small 19 (invers g) (asSite r j)
  have geom : ∀ (g : Fin 8) (r j : Fin 7), let x := small 19 (invers g) (asSite r j)
    probe (k:=6) x (Fin.ofNat 4 (direction (invers g) 2)).val=(leftProbe r j).map (small 19 (invers g)) ∧
    probe (k:=6) x (Fin.ofNat 4 (direction (invers g) 0)).val=(rightProbe r j).map (small 19 (invers g)) := by
      native_decide
  rw [slot_letter]
  simp only [rotatedLetter,bitsAt,(geom g r j).1,(geom g r j).2,Option.any_map,vmem]

private theorem stamp_sum (F : Finset X) (A : Array Terms) (g : Fin 8) (i : Nat) :
    (∑ x, coeff i (fromSite A x g (decide (x∈F)) (bitsAt F x)))=
      ∑ r : Fin 7, ∑ j : Fin 7, coeff i (letterStamp A r j (L (view F g) r j)) := by
  let f (x : X) := coeff i (fromSite A x g (decide (x∈F)) (bitsAt F x))
  let e (z : Fin 7 × Fin 7) := small 19 (invers g) (asSite z.1 z.2)
  have inj : ∀ g : Fin 8, Function.Injective (fun z : Fin 7 × Fin 7 => small 19 (invers g) (asSite z.1 z.2)) := by
    have inv : ∀ (g : Fin 8) (x : X), small 19 g (small 19 (invers g) x)=x := by native_decide
    intro g x y eq
    have z := (Function.LeftInverse.injective (inv g)) eq
    exact Prod.ext ((teeth 6).injective (congrArg Prod.fst z)) ((teeth 6).injective (congrArg Prod.snd z))
  have rep : ∀ (g : Fin 8) (x : X), let y := small 19 g x
    y.1.val%3=0 → y.2.val%3=0 → small 19 (invers g) (asSite (owner y.1) (owner y.2))=x := by native_decide
  have z : ∑ x, f x=∑ x ∈ univ.image e, f x := by
    symm; apply sum_subset (subset_univ _); intro x _ notMem
    unfold f fromSite; dsimp only
    split <;> rename_i h
    · exact False.elim (notMem (mem_image.mpr ⟨(owner (small 19 g x).1,owner (small 19 g x).2),mem_univ _,rep _ _ h.1 h.2⟩))
    · rfl
  change ∑ x, f x=_
  rw [z,sum_image (inj g).injOn,Fintype.sum_prod_type]
  apply sum_congr rfl; intro r _
  apply sum_congr rfl; intro j _
  have geo : ∀ (g : Fin 8) (r j : Fin 7), let y := small 19 g (small 19 (invers g) (asSite r j))
    (y.1.val%3=0 ∧ y.2.val%3=0) ∧ owner y.1=r ∧ owner y.2=j := by native_decide
  simp only [f,fromSite,if_pos (geo g r j).1,(geo g r j).2.1,(geo g r j).2.2]
  rw [rot_agrees F g r j]

theorem flatCoeff {B : Type} (i : Nat) (f : B → Terms) (l : List B) :
    coeff i (l.flatMap f)=(l.map fun x => coeff i (f x)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [coeff_append,ih]

theorem finCoeff {n : Nat} (i : Nat) (f : Fin n → Terms) :
    coeff i ((List.finRange n).flatMap f)=∑ j, coeff i (f j) := by
  rw [flatCoeff,←List.sum_toFinset _ (List.nodup_finRange n)]; simp

private theorem letter_rows (D : Chart) (checkD : letterCheck D) (supportD : starLineOnly D)
    (F : Finset X) (acy : (G F).IsAcyclic) (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v))
    (i : Fin D.rows.size) (h : lineLetters i) : lhs D (physicalVector D F (out F)) i=0 := by
  let w := lookupPrice D i (index D)
  let A := letterTable D
  have st (x : X) : w (Keys.star F (out F) x)=
      -(∑ g, coeff i (fromSite A x g (decide (x∈F)) (bitsAt F x))) := by
    have bound (d : Fin 4) (hd : bitsAt F x d) : (probe x d.val).isSome := by
      cases e : probe x d.val <;> simp_all [bitsAt]
    have s := of_decide_eq_true (Bool.and_eq_true_iff.mp checkD).2 x _ _ _ (physical_perm F acy x) bound
    have e := zero_of_balanced _ s i
    rw [coeff_append,sig_price _ _ _ h,star_agrees] at e
    simp only [starStamp,finCoeff] at e
    exact eq_neg_of_add_eq_zero_left e
  have ln (p : Fin 8 × Fin 7 × Fin 7) : w (line F p.1 p.2.1 p.2.2)=
      coeff i (letterStamp A p.2.1 p.2.2 (L (view F p.1) p.2.1 p.2.2)) := by
    have hs := LineKeys.physical_step _ _ (LineKeys.rotated_no_pitch F np p.1 (teeth 6 p.2.1)) p.2.2
    have z := of_decide_eq_true (Bool.and_eq_true_iff.mp checkD).1 p.2.1 p.2.2 _ hs.1 _ hs.2
    have e := zero_of_balanced _ z i
    rw [coeff_append,coeff_neg,sig_price _ _ _ h] at e
    exact eq_of_sub_eq_zero e
  have kill {j : Fin D.cols.size} (n : 2≤D.cols[j].key%8) (p : D.cols[j].key%8≠3) :
      coeff i D.cols[j].terms=0 := by
    have z := Array.all_eq_true_iff_forall_mem.mp supportD _ (Array.getElem_mem j.isLt)
    simp only [Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true,Bool.not_eq_true'] at z
    have absent := z.resolve_left (not_or.mpr ⟨not_lt.mpr n,p⟩)
    apply List.sum_eq_zero; intro t ht; obtain ⟨a,m,rfl⟩ := List.mem_map.mp ht
    have ne : a.1≠i.val := fun e => by have := absent a m; rw [e,h] at this; contradiction
    simp [ne]
  have no (key : Nat) (n : 2≤key%8) (p : key%8≠3) : w key=0 := by
    unfold w lookupPrice
    cases e : locate D (index D) key with
    | none => rfl
    | some j => change coeff i D.cols[j].terms*_=0; rw [kill (j:=j) ((locate_key e).symm ▸ n) ((locate_key e).symm ▸ p),zero_mul]
  have fa (p : FacePos 6) : w (face F p)=0 := by apply no <;> unfold face faceCode keyAt <;> omega
  have pa (p : P) : w (patch F p)=0 := by apply no <;> unfold patch patchCode <;> omega
  have add (u v : Fin D.cols.size → Int) : lhs D (fun j => u j+v j) i=lhs D u i+lhs D v i := by
    simp [lhs,mul_add,sum_add_distrib]
  have aux : lhs D (fun j : Fin D.cols.size =>
      if D.cols[j].key%8=5 then complete F (D.cols[j].key/8) else 0) i=0 := by
    apply sum_eq_zero; intro j _; dsimp only; split <;> rename_i q
    · rw [kill (j:=j) (by omega) (by omega),zero_mul]
    · simp
  have zero : lhs D (physicalVector D F (out F)) i=0 := by
    unfold physicalVector counts; rw [add,add,add,add,aux]
    simp only [scatter_price]
    change (∑ x, w (Keys.star F (out F) x))+(∑ p, w (face F p))+
      (∑ p : Fin 8 × Fin 7 × Fin 7, w (line F p.1 p.2.1 p.2.2))+(∑ p, w (patch F p))+0=0
    simp only [st,ln,fa,pa,sum_const_zero,add_zero,sum_neg_distrib]
    rw [sum_comm (s:=univ (α:=X)) (t:=univ (α:=Fin 8))]
    simp only [stamp_sum F A _ i]
    simp only [Fintype.sum_prod_type,neg_add_cancel]
  exact zero

theorem letter_rows19 (F : Finset X) (acy : (G F).IsAcyclic) (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v))
    (i : Fin chart19.rows.size) (h : lineLetters i) :
    2*lhs chart19 (physicalVector chart19 F (out F)) i=8*chart19.rows[i].rhs.atStep 0 := by
  rw [letter_rows _ check support F acy np i h,metaInfo i h]; rfl

end GridGraphs.NoPitch.LocalBoard19
