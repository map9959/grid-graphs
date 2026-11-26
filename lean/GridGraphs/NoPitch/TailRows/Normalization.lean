import GridGraphs.NoPitch.TailRows.NormChecks
import GridGraphs.NoPitch.TailRows.Letters

/-! The base chart verifies the *local coefficient* of each normalization
row. Its frequency on a larger board must be counted there: the eight
symmetries permute that board's sites (or its patch origins), and
`NormShape.count` evaluates the resulting fine-label fibre at that width.
In particular no multiplicity is transferred from the base board. -/

namespace GridGraphs.NoPitch.TailRows
open PitchCut Keys Budget FaceRows LocalBoard19 GridGraphs.NoPitch.Dual TailCoverage Finset
attribute [local irreducible] chart58 chart61

private theorem patch_key {k b} {p : PatchPos k} {q : PatchPos b} (v : ∀ g, patchFine p g=patchFine q g)
    (a : Nine) : patchCode p a=patchCode q a := by
  unfold patchCode
  have e (g : Fin 8) := v g
  unfold patchFine at e
  simp only [e]

private theorem orbit_card {n : Nat} [NeZero n] (h : Nat) (pat : List Nat) :
    (∑ x : Fin n × Fin n, orbitMass (fun g => let p := transform g n x.1 x.2; fine n h p.1 p.2) pat)=
      8*((univ.filter fun p : Fin n × Fin n => fine n h p.1 p.2=pat).card:Int) := by
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  have v (g : Fin 8) (x : Fin n × Fin n) :
      ((small n g x).1.val,(small n g x).2.val)=transform g n x.1 x.2 := by
    have r := x.1.isLt; have c := x.2.isLt
    fin_cases g <;> norm_num [small,transform,Fin.ofNat,Prod.ext_iff] <;>
      (try simp (disch := omega) only [Nat.mod_eq_of_lt,true_and,and_true]) <;> first | trivial | omega
  have inv (g : Fin 8) (x : Fin n × Fin n) : small n (invers g) (small n g x)=x := by
    have r := x.1.isLt; have c := x.2.isLt
    fin_cases g <;> norm_num [small,transform,invers,Fin.ofNat,Prod.ext_iff,Fin.ext_iff] <;>
      (try simp (disch := omega) only [Nat.mod_eq_of_lt,true_and,and_true]) <;> first | trivial | omega
  let f (p : Fin n × Fin n) : Int := if fine n h p.1 p.2=pat then 1 else 0
  have each (g : Fin 8) : (∑ x : Fin n × Fin n, if fine n h (transform g n x.1 x.2).1
      (transform g n x.1 x.2).2=pat then (1:Int) else 0)=∑ p, f p := by
    let e := Equiv.ofBijective (small n g) (Finite.injective_iff_bijective.mp (Function.LeftInverse.injective (inv g)))
    have eq (x : Fin n × Fin n) := v g x
    simp_rw [←eq]
    exact e.sum_comp f
  unfold orbitMass; rw [sum_comm]; simp only [each,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp [f]

private theorem stars_size {k} (pat : List Nat) :
    (∑ x : Site k, orbitMass (starFine x) pat)=
      8*((univ.filter fun p : Site k => fine (N k) 8 p.1 p.2=pat).card:Int) := by
  have e (g : Fin 8) (x : Site k) : starFine x g=
      fine (N k) 8 (transform g (N k) x.1 x.2).1 (transform g (N k) x.1 x.2).2 := by
    unfold starFine; rw [←turn_values]
  simpa only [orbitMass,e] using (orbit_card (n:=N k) 8 pat)

private theorem norm_lhs {k} (D : Chart) (B : Array NormShape) (ok : supported D (normal B))
    (F : Finset (Site k)) (i : Fin D.rows.size) (h : normal B i) :
    lhs D (physicalVector D F (out F)) i=
      (∑ x, lookupPrice D i (index D) (Keys.star F (out F) x))+∑ p, lookupPrice D i (index D) (patch F p) := by
  have kill {j : Fin D.cols.size} (n : 2≤D.cols[j].key%8) (p : D.cols[j].key%8≠4) :
      coeff i D.cols[j].terms=0 := by
    have z := Array.all_eq_true_iff_forall_mem.mp ok _ (Array.getElem_mem j.isLt)
    simp only [Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true,Bool.not_eq_true'] at z
    have absent := z.resolve_left (not_or.mpr ⟨not_lt.mpr n,p⟩)
    apply List.sum_eq_zero; intro t ht; obtain ⟨a,m,rfl⟩ := List.mem_map.mp ht
    have ne : a.1≠i.val := fun e => by have := absent a m; rw [e,h] at this; contradiction
    simp [ne]
  have no (key : Nat) (n : 2≤key%8) (p : key%8≠4) : lookupPrice D i (index D) key=0 := by
    unfold lookupPrice; cases e : locate D (index D) key with
    | none => rfl
    | some j => change coeff i D.cols[j].terms*_=0; rw [kill (j:=j) ((locate_key e).symm ▸ n) ((locate_key e).symm ▸ p),zero_mul]
  have fa (p : FacePos k) : lookupPrice D i (index D) (face F p)=0 := by apply no <;> unfold face faceCode keyAt <;> omega
  have ln (p : Fin 8 × J k × J k) : lookupPrice D i (index D) (line F p.1 p.2.1 p.2.2)=0 := by
    apply no <;> unfold line <;> dsimp only <;> omega
  have add (u v : Fin D.cols.size → Int) : lhs D (fun j => u j+v j) i=lhs D u i+lhs D v i := by
    simp [lhs,mul_add,sum_add_distrib]
  have aux : lhs D (fun j : Fin D.cols.size =>
      if D.cols[j].key%8=5 then complete F (D.cols[j].key/8) else 0) i=0 := by
    apply sum_eq_zero; intro j _; dsimp only; split <;> rename_i q
    · rw [kill (j:=j) (by omega) (by omega),zero_mul]
    · simp
  unfold physicalVector GridGraphs.NoPitch.Dual.counts; rw [add,add,add,add,aux]
  simp only [scatter_price,fa,ln,sum_const_zero,add_zero]

private theorem count_at (v : NormShape) (valid : v.Valid) (n h u : Nat)
    (nEq : n=v.n+6*u) (hEq : h=v.collar) :
    2*((univ.filter fun p : Fin n × Fin n => fine n h p.1 p.2=v.pattern).card:Int)=v.polynomial.atStep u := by
  subst n h; exact v.count valid u

theorem lifted_norm {k} (hk : 19≤k) (D : Chart) (B : Array NormShape)
    (ok : normCert D (if k%2=1 then 19 else 20) B) (valid : ∀ j : Fin B.size, B[j.val]!.Valid)
    (F : Finset (Site k)) (acy : (G F).IsAcyclic) (i : Fin D.rows.size) (h : normal B i) :
    rowHolds D.rows[i].sense (2*lhs D (physicalVector D F (out F)) i)
      (8*D.rows[i].rhs.atStep ((k-19)/2 : Nat)) := by
  obtain ⟨p,patches⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨p,stars⟩ := Bool.and_eq_true_iff.mp p
  obtain ⟨sup,info⟩ := Bool.and_eq_true_iff.mp p
  have bound := h
  simp only [normal,Bool.and_eq_true,decide_eq_true_eq] at bound
  let j : Fin B.size := ⟨i.val-1,by omega⟩
  have ij : j.val+1=i.val := by dsimp [j]; omega
  let v := B[j.val]!
  obtain ⟨_,sense,rhs,kind⟩ := of_decide_eq_true info j
  simp only [ij] at sense rhs
  change D.rows[i].sense=0 at sense
  change D.rows[i].rhs=v.polynomial at rhs
  have st (x : Site k) : lookupPrice D i (index D) (Keys.star F (out F) x)=
      if v.collar=8 then orbitMass (starFine x) v.pattern else 0 := by
    obtain ⟨y,ty⟩ := type_rep hk x
    have p := Bool.and_eq_true_iff.mp (of_decide_eq_true stars y)
    have bal := of_decide_eq_true p.2 _ _ _ (type_adm ty (physical_admissible F acy x))
    have z := zero_of_balanced _ bal i
    rw [coeff_append,coeff_neg,sig_price _ _ _ h,←type_key ty,physical_sKey] at z
    have res := of_decide_eq_true p.1 j; rw [ij] at res
    have vs : starFine x=starFine y := congrArg (fun t => t.2.1) ty
    rw [vs]; exact (eq_of_sub_eq_zero z).trans res
  have pa (p : PatchPos k) : lookupPrice D i (index D) (patch F p)=
      if v.collar=7 then orbitMass (patchFine p) v.pattern else 0 := by
    obtain ⟨q,eq⟩ := patch_rep hk p
    have both := Bool.and_eq_true_iff.mp (of_decide_eq_true patches q)
    have bal := of_decide_eq_true both.2 _ (legal_patch F hk acy p)
    have z := zero_of_balanced _ bal i
    rw [coeff_append,coeff_neg,sig_price _ _ _ h,←patch_key eq] at z
    have res := of_decide_eq_true both.1 j; rw [ij] at res
    rw [funext eq]; exact (eq_of_sub_eq_zero z).trans res
  rw [sense,norm_lhs D B sup F i h]; simp only [rowHolds,if_true,st,pa,rhs]
  let u := (k-19)/2
  let b := if k%2=1 then 19 else 20
  have nEq : N k=N b+6*u := by unfold N b u; split <;> omega
  change (v.collar=8 ∧ v.n=N b) ∨ (v.collar=7 ∧ v.n=N b-2) at kind
  rcases kind with ⟨c,n⟩|⟨c,n⟩
  · simp only [c,if_true,if_false,show ¬(8=7) by decide,sum_const_zero,add_zero,stars_size]
    have count := count_at v (valid j) (N k) 8 u (by omega) c.symm
    change _=8*v.polynomial.atStep u; linarith only [count]
  · haveI : NeZero (N k-2) := ⟨by unfold N; omega⟩
    simp only [c,if_true,if_false,show ¬(7=8) by decide,sum_const_zero,zero_add]
    rw [show (∑ p : PatchPos k, orbitMass (patchFine p) v.pattern)=_ from orbit_card (n:=N k-2) 7 v.pattern]
    have count := count_at v (valid j) (N k-2) 7 u (by dsimp [b] at *; unfold N at *; split at n <;> omega) c.symm
    change _=8*v.polynomial.atStep u; linarith only [count]

def normBuckets (k : Nat) := if k%2=1 then buckets58 else buckets61
theorem normalization_tail {k : Nat} (hk : 19≤k) (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (i : Fin (tailChart k).rows.size) (h : normal (normBuckets k) i) :
    rowHolds (tailChart k).rows[i].sense (2*lhs (tailChart k) (physicalVector (tailChart k) F (out F)) i)
      (8*(tailChart k).rows[i].rhs.atStep ((k-19)/2 : Nat)) := by
  apply lifted_norm hk _ _ _ _ F acy i h
  · by_cases odd : k%2=1 <;> simp [tailChart,normBuckets,odd,norm58,norm61]
  · by_cases odd : k%2=1
    · unfold normBuckets; rw [if_pos odd]; exact shapes58
    · unfold normBuckets; rw [if_neg odd]; exact shapes61

theorem upper_of_overlap_rows {k : Nat} (hk : 19≤k) (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (rows : ∀ r, ¬Pitch F (teeth k r)) (cols : ∀ r, ¬Pitch (trans F) (teeth k r))
    (rest : ∀ i : Fin (tailChart k).rows.size, (tailChart k).rows[i].sense=0 →
      ¬selected k i → ¬letterSelected k i → ¬normal (normBuckets k) i →
      2*lhs (tailChart k) (physicalVector (tailChart k) F (out F)) i =
        8*(tailChart k).rows[i].rhs.atStep ((k-19)/2 : Nat)) : F.card ≤ squareScore (N k) := by
  apply upper_of_remaining hk F acy rows cols
  intro i sense nf
  by_cases l : letterSelected k i
  · have e := letters_tail hk F acy rows cols i l (((k-19)/2 : Nat):Int); rw [sense] at e; exact e
  by_cases n : normal (normBuckets k) i
  · have e := normalization_tail hk F acy i n; rw [sense] at e; exact e
  exact rest i sense nf l n

def outstandingCount (D : Chart) (flow letters norm : Nat → Bool) :=
  ((List.range D.rows.size).filter fun i => D.rows[i]!.sense==0 && !flow i && !letters i && !norm i).length
theorem remaining_counts : outstandingCount chart58 flow58 letters58 (normal buckets58)=3071 ∧
    outstandingCount chart61 flow61 letters61 (normal buckets61)=3059 := by native_decide

end GridGraphs.NoPitch.TailRows
