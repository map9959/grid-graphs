import GridGraphs.NoPitch.Budget.OverlapKeys19

namespace GridGraphs.NoPitch.LocalBoard19
open Budget PitchCut Keys GridGraphs.NoPitch.Dual Finset FaceRows
attribute [local irreducible] chart19

theorem coeff_combine (i : Nat) (l : List Signs) :
    coefSigns i (combine l)=(l.map (coefSigns i)).sum := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    simp only [combine,List.flatMap_cons,coefSigns,coeff_append,List.map_cons,List.sum_cons] at ih ⊢
    omega
theorem combine_fin {n : Nat} (i : Nat) (f : Fin n → Signs) :
    coefSigns i (combine ((List.finRange n).map f))=∑ d, coefSigns i (f d) := by
  rw [coeff_combine,List.map_map,←List.sum_toFinset _ (List.nodup_finRange n)]
  simp

private theorem geom : ∀ (x y : X) (d : Fin 4), probe x d.val=some y →
    probe y (opp d).val=some x ∧ (∀ e : Fin 4, probe x e.val=some y → e=d) := by native_decide
private theorem arrow (F : Finset X) {x y : X} {d : Fin 4} (h : probe x d.val=some y) :
    out F x=some d ↔ parent F x=y := by
  constructor
  · intro e
    have p := out_points F x d (by simp [e]); rw [h] at p; exact (Option.some.inj p).symm
  · intro e
    cases o : out F x with
    | none => have := (out_none F x).mp o; exact False.elim ((probe_adj x y d h).ne (this.symm.trans e))
    | some z =>
      have m := out_points F x z (by simp [o]); rw [e] at m
      rw [(geom _ _ _ h).2 _ m]

private theorem directed (F : Finset X) (acy : (G F).IsAcyclic) (x y : X) (d : Fin 4)
    (h : probe x d.val=some y) (forced : x∈F ∨ y∈F) :
    (out F y==some (opp d))= !(out F x==some d) := by
  have adj : (G F).Adj x y := ⟨probe_adj _ _ _ h,forced⟩
  have covers := CapBill.parent_covers _ (sectionRoot F) acy adj
  change parent F x=y ∨ parent F y=x at covers
  have unique : parent F x=y → parent F y≠x := by
    intro a b
    have step (v : X) (ne : parent F v≠v) := (CapBill.parent_step _ (sectionRoot F)
      (mt (CapBill.parent_fix _ _ v).mpr ne)).2
    have p := step x (a ▸ adj.ne.symm); have q := step y (b ▸ adj.ne)
    change CapBill.depth _ (parent F x)<_ at p
    change CapBill.depth _ (parent F y)<_ at q
    rw [a] at p; rw [b] at q; omega
  apply Bool.eq_iff_iff.mpr
  simp [arrow F h,arrow F (geom _ _ _ h).1]
  tauto

def back (p : X × Fin 4) := match probe p.1 p.2.val with
  | none => p
  | some y => (y,opp p.2)
private theorem invol : Function.Involutive back := by unfold Function.Involutive; native_decide

private theorem reverse_event (T : Table) (i : Nat) (x y : X) (d : Fin 4) (f h a b : Bool)
    (ok : f || h → b= !a) (g : Fin 8) :
    coefSigns i (edgePos T x y g d f h a)= -coefSigns i (edgePos T y x g (opp d) h f b) := by
  have wd : ∀ (a b h f : Bool), (f || h → b= !a) →
      edgeWord f h a=edgeWord f h (!b) ∧ edgeWord h f (!a)=edgeWord h f b := by decide +kernel
  have eq := wd a b h f ok
  have dg : ∀ g d, (dirView g (opp d)).val=((dirView g d).val+2)%4 := by decide +kernel
  unfold coefSigns edgePos
  simp only [dg]
  have lt := (dirView g d).isLt
  generalize (dirView g d).val=z at *
  interval_cases z <;> simp [coeff,eq.1,eq.2]

theorem edge_rows19 (F : Finset X) (acy : (G F).IsAcyclic) (i : Fin chart19.rows.size) (h : edgeFamily i) :
    2*lhs chart19 (physicalVector chart19 F (out F)) i=8*chart19.rows[i].rhs.atStep 0 := by
  have info : ∀ i : Fin chart19.rows.size, edgeFamily i → chart19.rows[i].rhs=⟨0,0,0⟩ := by native_decide
  have support : ∀ i : Fin chart19.rows.size, edgeFamily i → onlyStars chart19 i := by native_decide
  let T := tagMap edgeTokens 13
  let amt (p : X × Fin 4) := coefSigns i (aroundEdge T p.1 p.2 (decide (p.1∈F)) (bitsAt F p.1) (out F p.1))
  have eq (x : X) : lookupPrice chart19 i (index chart19) (Keys.star F (out F) x)=∑ d, amt (x,d) := by
    have z := of_decide_eq_true edgeCheck19 x (decide (x∈F)) (bitsAt F x) (out F x) (physical_perm F acy x)
    have e := zero_of_balanced _ z i
    rw [coeff_append,coeff_append,coeff_neg,star_agrees,sig_price _ _ _ h] at e
    change _=∑ d, coefSigns i (aroundEdge T x d _ _ _) 
    rw [←combine_fin]
    unfold coefSigns; unfold aroundStar at e; dsimp only [T] at *; omega
  have anti (p : X × Fin 4) : amt p= -amt (back p) := by
    rcases p with ⟨x,d⟩
    cases e : probe x d.val with
    | none => simp [amt,aroundEdge,back,e,coefSigns,coeff]
    | some y =>
      have ey := (geom _ _ _ e).1
      simp only [amt,back,aroundEdge,e,ey,combine_fin,bitsAt,Option.any_some]
      rw [←sum_neg_distrib]
      apply sum_congr rfl; intro g _
      apply reverse_event
      intro p
      exact directed F acy x y d e (by simpa using p)
  let e : X × Fin 4 ≃ X × Fin 4 := ⟨back,back,invol,invol⟩
  have bij : (∑ p, amt (back p))=∑ p, amt p := e.sum_comp amt
  have z := sum_congr (s₁:=univ) rfl (fun p _ => anti p)
  rw [sum_neg_distrib,bij] at z
  rw [starRow F _ i (support i h),info i h]
  simp only [eq,←Fintype.sum_prod_type amt]
  change 2*(∑ p, amt p)=0
  change (∑ p, amt p)= -(∑ p, amt p) at z
  omega

end GridGraphs.NoPitch.LocalBoard19
