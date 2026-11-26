import GridGraphs.NoPitch.TailRows.IncidenceViews

namespace GridGraphs.NoPitch.TailRows.Incidence
open PitchCut Keys Budget LocalBoard19 Finset GridGraphs.NoPitch.Dual FaceRows
variable {k : Nat}

private theorem probeGeom (x y : Site k) (d : Fin 4) (h : probe x d.val=some y) :
    probe y (opp d).val=some x ∧ ∀ e : Fin 4, probe x e.val=some y → e=d := by
  simpa only [shift_probe] using geom x y d ((shift_probe x d).trans h)
private theorem arrow (F : Finset (Site k)) {x y : Site k} {d : Fin 4} (h : probe x d.val=some y) :
    out F x=some d ↔ parent F x=y := by
  constructor
  · intro e
    have p := out_points F x d (by simp [e]); rw [h] at p; exact (Option.some.inj p).symm
  · intro e
    cases o : out F x with
    | none => have := (out_none F x).mp o; exact False.elim ((probe_adj x y d h).ne (this.symm.trans e))
    | some z =>
      have m := out_points F x z (by simp [o]); rw [e] at m
      rw [(probeGeom _ _ _ h).2 _ m]
private theorem directed (F : Finset (Site k)) (acy : (G F).IsAcyclic) (x y : Site k) (d : Fin 4)
    (h : probe x d.val=some y) (forced : x∈F ∨ y∈F) :
    (out F y==some (opp d))= !(out F x==some d) := by
  have adj : (G F).Adj x y := ⟨probe_adj _ _ _ h,forced⟩
  have covers := CapBill.parent_covers _ (sectionRoot F) acy adj
  change parent F x=y ∨ parent F y=x at covers
  have unique : parent F x=y → parent F y≠x := by
    intro a b
    have step (v : Site k) (ne : parent F v≠v) := (CapBill.parent_step _ (sectionRoot F)
      (mt (CapBill.parent_fix _ _ v).mpr ne)).2
    have p := step x (a ▸ adj.ne.symm); have q := step y (b ▸ adj.ne)
    change CapBill.depth _ (parent F x)<_ at p
    change CapBill.depth _ (parent F y)<_ at q
    rw [a] at p; rw [b] at q; omega
  apply Bool.eq_iff_iff.mpr
  simp [arrow F h,arrow F (probeGeom _ _ _ h).1]; tauto

noncomputable def edgeAmt (B : Book) (F : Finset (Site k)) (i : Nat) (x : Site k) (d : Fin 4) :=
  ∑ g, coeff i (edgeAt B (starFine x) d g (decide (x∈F)) (bitsAt F x d) (out F x==some d))
theorem edge_sum (hk : 19≤k) (B : Book) (F : Finset (Site k)) (acy : (G F).IsAcyclic) (i : Nat) :
    (∑ x, ∑ d, edgeAmt B F i x d)=0 := by
  have big : 40≤N k := by unfold N; omega
  have res : (N k+8)%3=0 := by unfold N; omega
  let amt (z : Site k × Fin 4) := edgeAmt B F i z.1 z.2
  change (∑ x, ∑ d, amt (x,d))=0
  rw [←Fintype.sum_prod_type amt]; apply cancel
  · intro p d h; apply sum_eq_zero; intro g _
    change coeff i (edgeAt B (fineViews 8 p) d g _ _ _)=0
    simp [edgeAt,port_none p g d big (h:=8) (Or.inr rfl) h,lookup,coeff,negTerms]
  · intro p q d h
    have hr := (geom _ _ _ h).1
    change (∑ g, _) = -(∑ g, _)
    rw [←sum_neg_distrib]; apply sum_congr rfl; intro g _
    change coeff i (edgeAt B (fineViews 8 p) d g _ _ _)= -coeff i (edgeAt B (fineViews 8 q) (opp d) g _ _ _)
    have f := h; have r := hr; rw [shift_probe] at f r
    have wd : ∀ (a b h f : Bool), (f || h → b= !a) →
        edgeWord f h a=edgeWord f h (!b) ∧ edgeWord h f (!a)=edgeWord h f b := by decide
    have eq := wd (out F p==some d) (out F q==some (opp d)) (decide (q∈F)) (decide (p∈F))
      (fun m => directed F acy _ _ _ f (by simpa using m))
    simp only [edgeAt,bitsAt,f,r,Option.any_some,port_some p q g d big (Or.inr rfl) res h,
      port_some q p g (opp d) big (Or.inr rfl) res hr,dirReverse]
    have lt := (dirView g d).isLt; generalize (dirView g d).val=z at *
    interval_cases z <;> simp [coeff_neg,eq.1,eq.2]

def atSite (p : PatchPos k) (q : Q) : Site k :=
  (⟨p.1.val+q.1.val,by have := p.1.isLt; have := q.1.isLt; omega⟩,
   ⟨p.2.val+q.2.val,by have := p.2.isLt; have := q.2.isLt; omega⟩)
theorem mask_at (F : Finset (Site k)) (p : PatchPos k) (q : Q) :
    patchMask F p q=decide (atSite p q∈F) := by
  apply congrArg (fun x => decide (x∈F)); apply Prod.ext <;> apply Fin.ext <;>
    exact Nat.mod_eq_of_lt (by first | exact (atSite p q).1.isLt | exact (atSite p q).2.isLt)

theorem samples : ∀ (g : Fin 8) (d : Fin 4) (j : Fin 6),
    let a := small 3 (invers g) (sampleQ (dirView g d) j)
    let b := small 3 (invers g) (sampleQ (dirView g (opp d)) j)
    (a.1.val:Int)=dr d+b.1.val ∧ (a.2.val:Int)=dc d+b.2.val := by decide +kernel
theorem word_same (F : Finset (Site k)) (p q : PatchPos k) (d : Fin 4) (g : Fin 8) (h : shift p d=some q) :
    word6 (patchMask F p) g (dirView g d)=word6 (patchMask F q) g (dirView g (opp d)) := by
  have xy := (shift_iff _ _ _).mp h
  apply sum_congr rfl; intro j _
  have s := samples g d j
  have eq : atSite p (small 3 (invers g) (sampleQ (dirView g d) j)) =
      atSite q (small 3 (invers g) (sampleQ (dirView g (opp d)) j)) := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp only [atSite] <;> dsimp only at s <;> omega
  simp only [mask_at,eq]
def pairAmt (B : Book) (F : Finset (Site k)) (i : Nat) (p : PatchPos k) (d : Fin 4) :=
  ∑ g, coeff i (pairAt B (patchFine p) d g (patchMask F p))
theorem pair_sum (hk : 19≤k) (B : Book) (F : Finset (Site k)) (i : Nat) :
    (∑ p, ∑ d, pairAmt B F i p d)=0 := by
  have big : 40≤N k-2 := by unfold N; omega
  have res : (N k-2+7)%3=0 := by unfold N; omega
  haveI : NeZero (N k-2) := ⟨by omega⟩
  let amt (z : PatchPos k × Fin 4) := pairAmt B F i z.1 z.2
  change (∑ p, ∑ d, amt (p,d))=0
  rw [←Fintype.sum_prod_type amt]; apply cancel
  · intro p d h; apply sum_eq_zero; intro g _
    simp only [pairAt,patch_views,port_none p g d big (Or.inl rfl) h,lookup]
    split <;> rfl
  · intro p q d h
    have hr := (geom _ _ _ h).1
    change (∑ g, _) = -(∑ g, _)
    rw [←sum_neg_distrib]; apply sum_congr rfl; intro g _
    simp only [pairAt,patch_views,port_some p q g d big (Or.inl rfl) res h,
      port_some q p g (opp d) big (Or.inl rfl) res hr,word_same F p q d g h,dirReverse]
    have lt := (dirView g d).isLt; generalize (dirView g d).val=z at *
    interval_cases z <;> simp [coeff_neg]
end GridGraphs.NoPitch.TailRows.Incidence
