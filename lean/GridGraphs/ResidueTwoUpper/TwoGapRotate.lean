import GridGraphs.ResidueTwoUpper.TwoGapNormalize

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Exchange
open ResidueZero Stencil Words BoundarySix.Connected Finset SimpleGraph

private def rot {n} (v : GridVertex n n) : GridVertex n n := (v.2,v.1.rev)
private def rotSet {n} (F : Finset (GridVertex n n)) := univ.filter fun x => rot x∈F
private theorem rotated {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (acy : (Bonds F).IsAcyclic)
    (words : ∀ c, physicalWord hn F c∈[3,7,12,13]) :
    (Bonds (rotSet F)).IsAcyclic ∧ (rotSet F).card=F.card ∧
    ∀ i : Fin 4, signature hn (rotSet F) i=signature hn F (i+1) := by
  have inj : Function.Injective (rot (n:=n)) := by
    intro x y h; have X := congrArg Prod.fst h; have Y := congrArg Prod.snd h
    exact Prod.ext (Fin.rev_injective Y) X
  have map {x y : GridVertex n n} (g : (gridGraph n n).Adj x y) : (gridGraph n n).Adj (rot x) (rot y) := by
    have R := x.1.isLt; have K := y.1.isLt
    change adjacent _ _ _ _ at g ⊢
    simp only [adjacent,Fin.ext_iff,rot,Fin.rev] at g ⊢; omega
  have kept (x) (hx : x∈rotSet F) : rot x∈F := (mem_filter.mp hx).2
  let h : Bonds (rotSet F) →g Bonds F := ⟨rot,fun e => ⟨map e.1,e.2.imp (kept _) (kept _)⟩⟩
  refine ⟨acy.comap h inj,?_,?_⟩
  · apply card_bij (fun x _ => rot x) (fun _ hx => (mem_filter.mp hx).2) (fun _ _ _ _ eq => inj eq)
    intro x hx
    have pre : rot (x.2.rev,x.1)=x := by simp [rot]
    exact ⟨(x.2.rev,x.1),mem_filter.mpr ⟨mem_univ _,by rwa [pre]⟩,pre⟩
  · intro i
    -- Rotation interchanges the physical horizontal/vertical bit pairs,
    -- but the digits use cyclic local axes.
    have bits' (b : Bool) (j : Fin 3) : bits hn (rotSet F) (cornerNo i,b) j=
        bits hn F (cornerNo (i+1),!b) j := by
      have eq : rot (atArm hn (cornerNo i,b) j).1=(atArm hn (cornerNo (i+1),!b) j).1 := by
        have J := j.isLt
        fin_cases i <;> cases b <;> ext <;> simp [rot,atArm,cornerNo,loc,Fin.rev] <;> omega
      simp [bits,rotSet,eq]
    -- The relabeling formula needs the four legal words, so a mere
    -- acyclic mask is insufficient here.
    let T := cornerNo (i+1)
    let B (a : Bool) (j : Fin 3) : Fin 2 := ⟨bits hn F (T,a) j,by unfold bits; cases decide ((atArm hn (T,a) j).1∈F) <;> decide⟩
    let D (w : Nat) : Fin 4 := if w=3 then 0 else if w=7 then 1 else if w=12 then 2 else 3
    let read (t : Corner) (w : Nat) := if t.1=t.2 then D w else (⟨((D w).val+2)%4,Nat.mod_lt _ (by decide)⟩ : Fin 4)
    have tab : ∀ (z : Fin 4) (a b d e : Fin 2), (8*a.val+4*b.val+2*d.val+e.val)∈[3,7,12,13] →
        read (cornerNo z) (8*d.val+4*e.val+2*a.val+b.val)=read (cornerNo (z+1)) (8*a.val+4*b.val+2*d.val+e.val) := by native_decide
    have eq : physicalWord hn (rotSet F) (cornerNo i)=8*(B true 1).val+4*(B true 2).val+2*(B false 1).val+(B false 2).val := by
      unfold physicalWord; rw [bits' false 1,bits' false 2,bits' true 1,bits' true 2]; rfl
    change read (cornerNo i) (physicalWord hn (rotSet F) (cornerNo i))=read T (physicalWord hn F T)
    rw [eq]; exact tab i (B false 1) (B false 2) (B true 1) (B true 2) (words T)

/-- The representative is realized by a rotated *physical mark set* with
the same exceptional score. No symmetry hypothesis on the interior. -/
theorem canonical_witness {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) :
    ∃ M : Finset (GridVertex (35+42*u) (35+42*u)), (Bonds M).IsAcyclic ∧
      M.card=440+1020*u+588*u^2 ∧ (perimeterHoles M).card=2 ∧
      packed (signature (by omega) M)∈[code4 0 0 1 1,code4 0 1 0 1] := by
  have hn : 35≤35+42*u := by omega
  obtain ⟨L,forest,sz,gaps,j,form⟩ := normal_forms F acy score two
  have walk (k : Nat) : ∃ M : Finset (GridVertex (35+42*u) (35+42*u)),
      (Bonds M).IsAcyclic ∧ M.card=L.card ∧ ∀ i, signature hn M i=signature hn L (i+Fin.ofNat 4 k) := by
    induction k with
    | zero => exact ⟨L,forest,rfl,by simp⟩
    | succ k ih =>
      obtain ⟨M,f,h,w⟩ := ih
      obtain ⟨P,_,_,_,_,_,good,_⟩ := Frame.frame_of_score u M f (h.trans sz)
      obtain ⟨a,b,c⟩ := rotated hn M f (physicalWord_ok hn M P good)
      refine ⟨rotSet M,a,b.trans h,fun i => (c i).trans ((w (i+1)).trans ?_)⟩
      congr 1; apply Fin.ext; simp only [Fin.val_add,Fin.val_ofNat]; omega
  obtain ⟨M,f,h,w⟩ := walk j.val
  have eq : signature hn M=moved (signature hn L) ⟨j.val,by omega⟩ := by
    funext i; rw [w]; unfold moved
    simp only [if_pos (show j.val<4 from j.isLt)]
    congr 1; apply Fin.ext; simp [Fin.val_add,Fin.val_natCast]
  have normal : packed (signature hn M)∈[code4 0 0 1 1,code4 0 1 0 1] := by
    rw [eq]; simpa using form
  refine ⟨M,f,h.trans sz,?_,normal⟩
  obtain ⟨P,_,step,_,_,_,good,_⟩ := Frame.frame_of_score u M f (h.trans sz)
  rw [exact_holes hn M (corners_marked u M f (h.trans sz)) (fun x => (Frame.star_geometry hn M P step x (good _)).1),
    card_image_of_injective _ (gapEdge_inj hn)]
  have cnt : ∀ v : Fin 4 → Fin 4, packed v∈[code4 0 0 1 1,code4 0 1 0 1] →
      (∑ i, if (v i).val%2=0 then 1 else 0 : Nat)=2 := by native_decide
  have cnt' := cnt _ normal
  have perm (f : Corner → Nat) : ∑ i : Fin 4, f (cornerNo i)=∑ x : Corner, f x := by
    rw [Fintype.sum_prod_type]; simp [Fin.sum_univ_four,cornerNo,add_comm,add_left_comm,add_assoc]
  change (∑ i, if (digit hn M (cornerNo i)).val%2=0 then 1 else 0 : Nat)=2 at cnt'
  rw [perm (fun x => if (digit hn M x).val%2=0 then 1 else (0:Nat))] at cnt'
  simp_rw [gaps_at hn M _ (physicalWord_ok hn M P good _)] at cnt'
  rw [←Fintype.sum_prod_type (fun x : Arm => if x∈Words.gaps hn M then 1 else (0:Nat))] at cnt'
  simpa using cnt'

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Exchange
