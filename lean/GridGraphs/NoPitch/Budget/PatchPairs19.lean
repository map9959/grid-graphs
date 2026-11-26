import GridGraphs.NoPitch.Budget.EdgeRows19

namespace GridGraphs.NoPitch.LocalBoard19
open Budget PitchCut Keys GridGraphs.NoPitch.Dual Finset FaceRows
attribute [local irreducible] chart19
def pairFamily (i : Nat) := 1164 ≤ i && i ≤ 1927
def nearPatch (p : P) (d : Fin 4) : Option P :=
  let r : Int := p.1.val+(if d=1 then 1 else if d=3 then -1 else 0)
  let c : Int := p.2.val+(if d=0 then 1 else if d=2 then -1 else 0)
  if h : 0≤r ∧ 0≤c ∧ r.toNat<17 ∧ c.toNat<17 then some (⟨_,h.2.2.1⟩,⟨_,h.2.2.2⟩) else none
def sampleQ (z : Fin 4) (j : Fin 6) : Q :=
  let d := z.val%2
  (Fin.ofNat 3 (j.val/(2+d)+(if z=1 then 1 else 0)),
    Fin.ofNat 3 (j.val%(2+d)+(if z=0 then 1 else 0)))
def word6 (a : Nine) (g : Fin 8) (z : Fin 4) :=
  ∑ j : Fin 6, (a (small 3 (invers g) (sampleQ z j))).toNat*2^j.val
def pairSign (T : Table) (p q : P) (a : Nine) (g : Fin 8) (d : Fin 4) : Signs :=
  let z := dirView g d
  let word := word6 a g z
  if z.val<2 then (event T (small 17 g p) (small 17 g q) z.val word,[])
  else ([],event T (small 17 g q) (small 17 g p) (z.val-2) word)
def pairSide (T : Table) (p : P) (a : Nine) (d : Fin 4) := match nearPatch p d with
  | none => ([],[])
  | some q => combine ((List.finRange 8).map fun g => pairSign T p q a g d)
def pairStamp (T : Table) (p : P) (a : Nine) := combine ((List.finRange 4).map fun d => pairSide T p a d)
def pairCheck (D : Chart) :=
  let w := contribution D (index D) (prices D pairFamily)
  let tab := tagMap pairTokens 1164
  decide (∀ p a, legal a →
    let s := pairStamp tab p a
    balanced (w (patchCode p a) ++ negTerms s.1 ++ s.2))
private theorem pairReplay : pairCheck chart19 := by native_decide

private def reverseSide (x : P × Fin 4) := match nearPatch x.1 x.2 with
  | none => x
  | some q => (q,opp x.2)
private theorem opposite : ∀ (p : P) (d : Fin 4) q, nearPatch p d=some q → nearPatch q (opp d)=some p := by native_decide
private theorem adjacent_samples :
    ∀ (p : P) (d : Fin 4), ∀ q∈nearPatch p d, ∀ (g : Fin 8) (j : Fin 6),
      site p (small 3 (invers g) (sampleQ (dirView g d) j))=
      site q (small 3 (invers g) (sampleQ (dirView g (opp d)) j)) := by native_decide
private theorem pair_anti (F : Finset X) (T : Table) (p q : P) (d : Fin 4) (e : nearPatch p d=some q)
    (i : Nat) (g : Fin 8) :
    coefSigns i (pairSign T p q (patchMask F p) g d)= -coefSigns i (pairSign T q p (patchMask F q) g (opp d)) := by
  have same : word6 (patchMask F p) g (dirView g d)=word6 (patchMask F q) g (dirView g (opp d)) := by
    apply sum_congr rfl; intro j _
    have eq := adjacent_samples p d q (by simp [e]) g j
    change (decide (site p _∈F)).toNat*_= (decide (site q _∈F)).toNat*_
    rw [eq]
  have dg : ∀ g d, (dirView g (opp d)).val=((dirView g d).val+2)%4 := by decide +kernel
  unfold coefSigns pairSign; dsimp only; rw [same]
  simp only [dg]; have lt := (dirView g d).isLt; generalize (dirView g d).val=z at *
  interval_cases z <;> simp [coeff]

private theorem pair_rows (D : Chart) (replay : pairCheck D) (support : supported D pairFamily)
    (star0 : D.cols.all (fun c => 2≤c.key%8 || c.terms.all (fun p => !pairFamily p.1)))
    (F : Finset X) (acy : (G F).IsAcyclic) (i : Fin D.rows.size) (sel : pairFamily i) :
    lhs D (physicalVector D F (out F)) i=0 := by
  let T := tagMap pairTokens 1164
  let amt (z : P × Fin 4) := coefSigns i (pairSide T z.1 (patchMask F z.1) z.2)
  have atPatch (p : P) : lookupPrice D i (index D) (patch F p)=∑ d, amt (p,d) := by
    have z := of_decide_eq_true replay p _ (patch_legal F acy p)
    have e := zero_of_balanced _ z i
    rw [coeff_append,coeff_append,coeff_neg,sig_price _ _ _ sel] at e
    change _=∑ d, coefSigns i (pairSide T p (patchMask F p) d)
    rw [←combine_fin]; unfold coefSigns; unfold pairStamp at e
    change lookupPrice D i (index D) (patch F p)+ -_+_=0 at e
    let s := pairStamp T p (patchMask F p)
    change lookupPrice D i (index D) (patch F p)=coeff i s.1-coeff i s.2
    change lookupPrice D i (index D) (patch F p)+ -coeff i s.1+coeff i s.2=0 at e
    omega
  have anti (p : P × Fin 4) : amt p= -amt (reverseSide p) := by
    rcases p with ⟨p,d⟩; cases e : nearPatch p d with
    | none => simp [amt,pairSide,reverseSide,e,coefSigns,coeff]
    | some q =>
      simp only [amt,reverseSide,e,pairSide,opposite p d q e,combine_fin]
      rw [←sum_neg_distrib]; apply sum_congr rfl; intro g _; exact pair_anti F T p q d e i g
  have inv : Function.Involutive reverseSide := by unfold Function.Involutive; native_decide
  let equiv : P × Fin 4 ≃ P × Fin 4 := ⟨_,_,inv,inv⟩
  have bij : (∑ p, amt (reverseSide p))=∑ p, amt p := equiv.sum_comp amt
  have z := sum_congr (s₁:=univ) rfl (fun p _ => anti p)
  rw [sum_neg_distrib,bij] at z
  change (∑ p, amt p)= -(∑ p, amt p) at z
  have zero (x : X) : lookupPrice D i (index D) (Keys.star F (out F) x)=0 := by
    unfold lookupPrice
    cases e : locate D (index D) (Keys.star F (out F) x) with
    | none => rfl
    | some j =>
      have ne : ¬2≤D.cols[j].key%8 := by rw [locate_key e]; unfold Keys.star; cases decide (x∈F) <;> simp
      have v := Array.all_eq_true_iff_forall_mem.mp star0 _ (Array.getElem_mem j.isLt)
      simp only [Bool.or_eq_true,decide_eq_true_eq,List.all_eq_true,Bool.not_eq_true'] at v
      have absent := v.resolve_left ne
      change coeff i D.cols[j].terms*_=0
      apply mul_eq_zero_of_left
      apply List.sum_eq_zero; intro t ht
      obtain ⟨p,m,rfl⟩ := List.mem_map.mp ht
      have neq : p.1≠i.val := fun eq => Bool.noConfusion (sel.symm.trans (eq ▸ absent p m))
      simp [neq]
  rw [star_patch_lhs support _ _ i sel]
  simp only [zero,sum_const_zero,zero_add,atPatch,←Fintype.sum_prod_type amt]
  change (∑ p, amt p)=0; omega

theorem pair_rows19 (F : Finset X) (acy : (G F).IsAcyclic) (i : Fin chart19.rows.size) (sel : pairFamily i) :
    2*lhs chart19 (physicalVector chart19 F (out F)) i=8*chart19.rows[i].rhs.atStep 0 := by
  have metaInfo : ∀ i : Fin chart19.rows.size, pairFamily i → chart19.rows[i].rhs=⟨0,0,0⟩ := by native_decide
  have support : supported chart19 pairFamily := by native_decide
  have star0 : chart19.cols.all (fun c => 2≤c.key%8 || c.terms.all (fun p => !pairFamily p.1)) := by native_decide
  rw [pair_rows chart19 pairReplay support star0 F acy i sel,metaInfo i sel]; rfl

end GridGraphs.NoPitch.LocalBoard19
