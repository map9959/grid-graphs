import GridGraphs.NoPitch.TailRows.CellSums
import GridGraphs.NoPitch.FiniteRows.Near

namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Keys Budget FaceRows LocalBoard19 GridGraphs.NoPitch.Dual Finset TailRows TailRows.Incidence
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

theorem edge_small (hk : 7≤k) (B : Book) (F : Finset (Site k)) (acy : (G F).IsAcyclic) (i : Nat) :
    (∑ x, ∑ d, edgeAmt B F i x d)=0 := by
  have big : 20≤N k := by unfold N; omega
  have res : (N k+8)%3=0 := by unfold N; omega
  let amt (z : Site k × Fin 4) := edgeAmt B F i z.1 z.2
  change (∑ x, ∑ d, amt (x,d))=0
  rw [←Fintype.sum_prod_type amt]; apply cancel
  · intro p d h; apply sum_eq_zero; intro g _
    change coeff i (edgeAt B (fineViews 8 p) d g _ _ _)=0
    simp [edgeAt,port_none_small p g d big (h:=8) (Or.inr rfl) h,lookup,coeff,negTerms]
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
    simp only [edgeAt,bitsAt,f,r,Option.any_some,port_some_small p q g d big (Or.inr rfl) res h,
      port_some_small q p g (opp d) big (Or.inr rfl) res hr,dirReverse]
    have lt := (dirView g d).isLt; generalize (dirView g d).val=z at *
    interval_cases z <;> simp [coeff_neg,eq.1,eq.2]

theorem pair_small (hk : 7≤k) (B : Book) (F : Finset (Site k)) (i : Nat) :
    (∑ p, ∑ d, pairAmt B F i p d)=0 := by
  have big : 20≤N k-2 := by unfold N; omega
  have res : (N k-2+7)%3=0 := by unfold N; omega
  haveI : NeZero (N k-2) := ⟨by omega⟩
  let amt (z : PatchPos k × Fin 4) := pairAmt B F i z.1 z.2
  change (∑ p, ∑ d, amt (p,d))=0
  rw [←Fintype.sum_prod_type amt]; apply cancel
  · intro p d h; apply sum_eq_zero; intro g _
    simp only [pairAt,patch_views,port_none_small p g d big (Or.inl rfl) h,lookup]
    split <;> rfl
  · intro p q d h
    have hr := (geom _ _ _ h).1
    change (∑ g, _) = -(∑ g, _)
    rw [←sum_neg_distrib]; apply sum_congr rfl; intro g _
    simp only [pairAt,patch_views,port_some_small p q g d big (Or.inl rfl) res h,
      port_some_small q p g (opp d) big (Or.inl rfl) res hr,word_same F p q d g h,dirReverse]
    have lt := (dirView g d).isLt; generalize (dirView g d).val=z at *
    interval_cases z <;> simp [coeff_neg]
theorem cell_agree_small (hk : 7≤k) (B : Book) (F : Finset (Site k)) (p : PatchPos k) (q : Q) (g : Fin 8) :
    socketAt B (starFine (atSite p q)) q g (decide (atSite p q∈F)) (bitsAt F (atSite p q))=
    plugAt B (patchFine p) q g (patchMask F p) := by
  have n : 20≤N k-2 := by unfold N; omega
  haveI : NeZero (N k-2) := ⟨by omega⟩
  let a := small (N k-2) g p
  let z := small 3 g q
  let x := atSite a z
  have r := z.1.isLt; have c := z.2.isLt
  have u : (x.1.val:Int)=a.1.val+z.1.val := by simp [x,atSite]
  have v : (x.2.val:Int)=a.2.val+z.2.val := by simp [x,atSite]
  have h := (valid_small x (r:= -(z.1.val:Int)) (c:= -(z.2.val:Int)) (m:=N k-2)
    (dn:= -2) (Or.inr rfl) (by omega) (by omega) (by omega)).2
    (by have := a.1.isLt; have := a.2.isLt; omega)
  rw [plugAt,cell_word,socketAt,patch_views]
  apply congrArg (fun key => lookup B.S key _)
  unfold socket plug starFine turn fineViews; rw [turn_site]
  change (if valid 8 (fine (N k) 8 x.1 x.2) _ _ _ then _ else _)=_
  rw [if_pos h]
  have s : (N k+8)%3=0 := by unfold N; omega
  have t : (N k-2+7)%3=0 := by unfold N; omega
  change some (eventKey (moved 8 (fine (N k) 8 x.1 x.2) _ _ _) (moved 8 (fine (N k) 8 x.1 x.2) _ _ _) _) =
    some (eventKey (moved 7 (fine (N k-2) 7 a.1 a.2) _ _ _) (moved 7 (fine (N k-2) 7 a.1 a.2) _ _ _) _)
  rw [moved_small x a (r:= -(z.1.val:Int)) (c:= -(z.2.val:Int)) (dn:= -2) (Or.inr rfl) s (by omega) (by omega) (by omega) (by omega) (by omega),
    moved_small x x (Or.inr rfl) s (by omega) (by omega) (by omega) (by omega) (by decide),
    moved_small a a (Or.inl rfl) t n (by omega) (by omega) (by omega) (by decide),
    moved_small a x (Or.inl rfl) t n u v (by omega) (by omega)]

theorem cell_absent_small (hk : 7≤k) (B : Book) (x : Site k) (q : Q) (g : Fin 8) (f bits)
    (no : ¬∃ p : PatchPos k, atSite p q=x) : socketAt B (starFine x) q g f bits=[] := by
  have n : 20≤N k-2 := by unfold N; omega
  haveI : NeZero (N k-2) := ⟨by omega⟩
  let z := small 3 g q
  let y := small (N k) g x
  have r := z.1.isLt; have c := z.2.isLt
  have h : ¬valid 8 (fine (N k) 8 y.1 y.2) (-(z.1.val:Int)) (-(z.2.val:Int)) (-2) := by
    intro v
    have a := (valid_small y (m:=N k-2) (dn:= -2) (Or.inr rfl) (by omega) (by omega) (by omega)).mp v
    let p : PatchPos k := (⟨y.1.val-z.1.val,by omega⟩,⟨y.2.val-z.2.val,by omega⟩)
    have e : atSite p z=y := by apply Prod.ext <;> apply Fin.ext <;> dsimp [p,atSite] <;> omega
    have eq := congrArg (small (N k) (invers g)) e
    rw [turn_site] at eq
    apply no; exact ⟨_,by simpa only [y,z,inverse] using eq⟩
  unfold socketAt socket
  change lookup _ (if valid 8 (fine (N k) 8 y.1 y.2) _ _ _ then _ else none) _=[]
  rw [if_neg h]; rfl

theorem cell_small (hk : 7≤k) (B : Book) (F : Finset (Site k)) (i : Nat) :
    (∑ x, ∑ q, socketAmt B F i x q)=∑ p, ∑ q, plugAmt B F i p q := by
  rw [sum_comm (s:=univ (α:=Site k)),sum_comm (s:=univ (α:=PatchPos k))]
  apply sum_congr rfl; intro q _
  let e (p : PatchPos k) := atSite p q
  have inj : Function.Injective e := by
    intro a b h
    have r := congrArg (fun x : Site k => x.1.val) h; have c := congrArg (fun x : Site k => x.2.val) h
    dsimp [e,atSite] at r c
    apply Prod.ext <;> apply Fin.ext <;> omega
  have z : ∑ x, socketAmt B F i x q=∑ x ∈ univ.image e, socketAmt B F i x q := by
    symm; apply sum_subset (subset_univ _); intro x _ no; apply sum_eq_zero; intro g _
    rw [cell_absent_small hk B x q g _ _ (by simpa [e] using no)]; rfl
  rw [z,sum_image inj.injOn]; simp only [e,socketAmt,plugAmt,cell_agree_small hk]

end GridGraphs.NoPitch.FiniteRows
