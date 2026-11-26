import GridGraphs.NoPitch.Budget.Normalization19
import GridGraphs.NoPitch.LineKeys19

namespace GridGraphs.NoPitch.LocalBoard19
open Budget PitchCut Keys GridGraphs.NoPitch.Dual Finset FaceRows
attribute [local irreducible] chart19

def flowRow (i : Nat) := (2317 ≤ i && i ≤ 2356) || (2374 ≤ i && i ≤ 2385) ||
  (2405 ≤ i && i ≤ 2438) || (2477 ≤ i && i ≤ 2528) || (2562 ≤ i && i ≤ 2627) ||
  (2651 ≤ i && i ≤ 2696) || (2733 ≤ i && i ≤ 2789)
def lineLetters (i : Nat) := 2285 ≤ i && i ≤ 2789 && !flowRow i
def stampKey (r : Fin 7) (j : Nat) (s : State) := (r.val*7+j)*90+state s

/-- Infer candidate state stamps from positive column entries. The
transition check below verifies them independently on the DFA. -/
def potentialTable (D : Chart) : Array Terms := Id.run do
  let mut a : Array Terms := Array.replicate 4410 []
  for c in D.cols do
    if c.key%8==3 then
      let n := c.key/8
      let p := n/8100
      let idx := ((p/1024/3)*7+p%32/3)*90+n%90
      for (i,v) in c.terms do
        if flowRow i && v>0 && idx<a.size then
          let ts := a[idx]?.getD []
          if !(ts.contains (i,1)) then a := a.setIfInBounds idx ((i,1)::ts)
  return a

def stamp (A : Array Terms) (r : Fin 7) (j : Nat) (s : State) : Terms :=
  if j=0 ∨ j=7 then [] else A[stampKey r (j-1) s]?.getD []
def negTerms (ts : Terms) : Terms := ts.map fun (i,v) => (i,-v)
def flowCheck (D : Chart) :=
  let w := contribution D (index D) (prices D flowRow)
  let a := potentialTable D
  decide (∀ (r j : Fin 7), ∀ s∈LineKeys.states j.val, ∀ l : Letter, LineKeys.allowedStep j.val s l →
    let t := advance s l
    balanced (w (LineKeys.key r j.val s t) ++ stamp a r j.val s ++ negTerms (stamp a r (j.val+1) t)))
def flowSupport (D : Chart) := D.cols.all fun c => c.key%8==3 || c.terms.all (fun t => !flowRow t.1)
def flowMeta (D : Chart) := decide (∀ i : Fin D.rows.size, flowRow i → D.rows[i].rhs=⟨0,0,0⟩)

private theorem step19 : flowCheck chart19 := by native_decide
private theorem sup19 : flowSupport chart19 := by native_decide
private theorem meta19 : flowMeta chart19 := by native_decide

theorem coeff_append (i : Nat) (a b : Terms) : coeff i (a++b)=coeff i a+coeff i b := by simp [coeff]
theorem coeff_neg (i : Nat) (a : Terms) : coeff i (negTerms a)= -coeff i a := by
  induction a with
  | nil => simp [coeff,negTerms]
  | cons t ts ih => rcases t with ⟨j,c⟩; by_cases h : j=i <;> simp_all [coeff,negTerms,add_comm]

theorem line_only_lhs {k : Nat} {D : Chart} (F : Finset (Site k)) (o : Site k → Option (Fin 4)) (i : Fin D.rows.size)
    (sel : Nat → Bool) (pos : sel i) (ok : D.cols.all fun c => c.key%8==3 || c.terms.all (fun t => !sel t.1)) :
    lhs D (physicalVector D F o) i=∑ p : Fin 8 × J k × J k,
      lookupPrice D i (index D) (line F p.1 p.2.1 p.2.2) := by
  have kill {j : Fin D.cols.size} (n : D.cols[j].key%8≠3) : coeff i D.cols[j].terms=0 := by
    have h := Array.all_eq_true_iff_forall_mem.mp ok _ (Array.getElem_mem j.isLt)
    simp only [Bool.or_eq_true,beq_iff_eq,List.all_eq_true,Bool.not_eq_true'] at h
    have z := h.resolve_left n
    apply List.sum_eq_zero; intro v hv
    obtain ⟨p,m,rfl⟩ := List.mem_map.mp hv
    have ne : p.1≠i.val := fun e => by have := z p m; rw [e,pos] at this; contradiction
    simp [ne]
  have zero (v : Nat) (n : v%8≠3) : lookupPrice D i (index D) v=0 := by
    unfold lookupPrice; cases e : locate D (index D) v with
    | none => rfl
    | some j => change coeff i D.cols[j].terms*_=0; rw [kill (j:=j) ((locate_key e).symm ▸ n),zero_mul]
  have a (p : FacePos k) : lookupPrice D i (index D) (face F p)=0 := by
    apply zero; unfold face faceCode keyAt; omega
  have b (p : Site k) : lookupPrice D i (index D) (Keys.star F o p)=0 := by
    apply zero; unfold Keys.star; cases decide (p∈F) <;> simp
  have c (p : PatchPos k) : lookupPrice D i (index D) (patch F p)=0 := by
    apply zero; unfold patch patchCode; omega
  have add (u v : Fin D.cols.size → Int) : lhs D (fun j => u j+v j) i=lhs D u i+lhs D v i := by
    simp [lhs,mul_add,sum_add_distrib]
  have aux : lhs D (fun j : Fin D.cols.size =>
      if D.cols[j].key%8=5 then complete F (D.cols[j].key/8) else 0) i=0 := by
    apply sum_eq_zero; intro j _; dsimp only; split <;> rename_i h
    · rw [kill (j:=j) (by omega),zero_mul]
    · simp
  unfold physicalVector counts
  rw [add,add,add,add,aux]
  simp only [scatter_price,a,b,c,sum_const_zero,add_zero,zero_add]

theorem flow19 (F : Finset X) (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v))
    (o : X → Option (Fin 4)) (i : Fin chart19.rows.size) (h : flowRow i) :
    2*lhs chart19 (physicalVector chart19 F o) i=8*chart19.rows[i].rhs.atStep 0 := by
  let value (g : Fin 8) (r : Fin 7) (j : Nat) :=
    coeff i (stamp (potentialTable chart19) r j (prefixState (view F g) (teeth 6 r) j))
  have atStep (g : Fin 8) (r j : Fin 7) : lookupPrice chart19 i (index chart19) (line F g r j)=
      value g r (j.val+1)-value g r j.val := by
    have hs := LineKeys.physical_step (view F g) (teeth 6 r) (LineKeys.rotated_no_pitch F np g _) j
    have eq := of_decide_eq_true step19 r j _ hs.1 _ hs.2
    have e := zero_of_balanced _ eq i
    simp only [coeff_append,coeff_neg,sig_price chart19 flowRow i h] at e
    change lookupPrice chart19 i (index chart19) (line F g r j)+value g r j.val+
      -value g r (j.val+1)=0 at e
    omega
  rw [line_only_lhs F o i flowRow h sup19,of_decide_eq_true meta19 i h]
  simp only [Fintype.sum_prod_type,atStep]
  have tel (v : Nat → Int) : (∑ j : Fin 7, (v (j.val+1)-v j.val))=v 7-v 0 := by
    simp [Fin.sum_univ_succ,Fin.val_succ]; ring
  have z (g r) : value g r 7-value g r 0=0 := rfl
  simp only [tel,z,sum_const_zero,mul_zero]; rfl

end GridGraphs.NoPitch.LocalBoard19
