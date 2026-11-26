import GridGraphs.ResidueTwoUpper.ExceptionalGapReduction
import GridGraphs.Accounting.BoundarySix.Connected.TwoGaps

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Words
open ResidueZero Stencil GridGraphs.ResidueTwoUpper.Exceptional.Frame BoundarySix.Connected Finset

abbrev Corner := Bool × Bool -- far row, far column
abbrev Arm := Corner × Bool -- false = horizontal, true = vertical
def loc (n : Nat) (far : Bool) (j : Nat) := if far then n-1-j else j
def atArm {n : Nat} (hn : 35≤n) (s : Arm) (j : Fin 3) : PerimeterVertex n :=
  ⟨(⟨loc n s.1.1 (if s.2 then j.val else 0),by
      have := j.isLt; unfold loc; split_ifs <;> omega⟩,
    ⟨loc n s.1.2 (if s.2 then 0 else j.val),by
      have := j.isLt; unfold loc; split_ifs <;> omega⟩),by
    unfold IsGridBoundary loc; cases s with | mk c arm => cases c with
    | mk r k => cases arm <;> cases r <;> cases k <;> dsimp <;> omega⟩

def gapEdge {n} (hn : 35≤n) (s : Arm) := s(atArm hn s 1,atArm hn s 2)

private theorem unique_site {n} (hn : 35≤n) (s t : Arm) (i j : Fin 3)
    (_hi : i.val≠0) (hj : j.val≠0) (h : atArm hn s i=atArm hn t j) : s=t ∧ i=j := by
  have A := congrArg (fun x : PerimeterVertex n => x.1.1.val) h
  have B := congrArg (fun x : PerimeterVertex n => x.1.2.val) h
  rcases s with ⟨⟨r,c⟩,a⟩; rcases t with ⟨⟨R,C⟩,b⟩
  have iv := i.isLt; have jv := j.isLt
  cases a <;> cases b <;> cases r <;> cases R <;> cases c <;> cases C <;>
    dsimp [atArm,loc] at A B ⊢ <;> simp [Fin.ext_iff] <;> omega

theorem gapEdge_inj {n} (hn : 35≤n) : Function.Injective (gapEdge hn) := by
  intro s t eq
  rcases Sym2.eq_iff.mp eq with h|h
  all_goals exact (unique_site hn _ _ _ _ (by decide) (by decide) h.1).1

def bits {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (a : Arm) (j : Fin 3) :=
  (decide ((atArm hn a j).1∈F)).toNat
def physicalWord {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (c : Corner) :=
  8*bits hn F (c,false) 1 + 4*bits hn F (c,false) 2 +
    2*bits hn F (c,true) 1 + bits hn F (c,true) 2

private def origin {n} (hn : 35≤n) (c : Corner) : origins n :=
  (⟨loc (n-2) c.1 0,by unfold loc; split_ifs <;> omega⟩,
   ⟨loc (n-2) c.2 0,by unfold loc; split_ifs <;> omega⟩)

theorem physicalWord_ok {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (P)
    (good : ∀ x, allGood F P x) (c : Corner) : physicalWord hn F c ∈ [3,7,12,13] := by
  let a := origin hn c
  have corner : isCorner a := by
    rcases c with ⟨r,k⟩; cases r <;> cases k <;> dsimp [a,origin,isCorner,loc] <;> omega
  have hw := (patch_geometry hn F P a (good (.inr a))).2 corner
  have bitEq (q : Fin 9) (s : Arm) (j : Fin 3) (h : coord a+offset q=coord (atArm hn s j).1) :
      bit (maskAt F a) q=bits hn F s j := by
    have b := patch_bit F a.1.val a.2.val (by have := a.1.isLt; omega) (by have := a.2.isLt; omega) q
    change bit (maskAt F a) q=(marked F (coord a+offset q)).toNat at b
    rw [b,h,marked_at]; rfl
  have sample (arm : Bool) (j : Fin 3) :
      let r := if arm then j.val else 0
      let k := if arm then 0 else j.val
      bit (maskAt F a) (3*(if (coord a).1=0 then r else 2-r)+(if (coord a).2=0 then k else 2-k))=
        bits hn F (c,arm) j := by
    dsimp only
    have b := j.isLt
    apply bitEq (q:=⟨_,by split_ifs <;> omega⟩)
    rcases c with ⟨r,k⟩
    cases r <;> cases k <;> cases arm <;> fin_cases j <;>
      ext <;> simp [a,coord,origin,loc,offset,atArm] <;> omega
  unfold word at hw
  unfold physicalWord
  rw [←sample false 1,←sample false 2,←sample true 1,←sample true 2]
  exact hw

def gaps {n} (hn : 35≤n) (F : Finset (GridVertex n n)) :=
  univ.filter fun a : Arm => (atArm hn a 1).1∉F ∧ (atArm hn a 2).1∉F

theorem exact_holes {n} (hn : 35≤n) (F : Finset (GridVertex n n))
    (corners : ∀ v, isCorner v → v∈F) (line : ∀ v, straight n (coord v) → v∈F) :
    perimeterHoles F=(gaps hn F).image (gapEdge hn) := by
  classical
  ext e; induction e using Sym2.inductionOn with
  | _ x y =>
    rw [mem_perimeterHoles_pair,mem_image]
    constructor
    · rintro ⟨adj,hx,hy⟩
      have near (v : PerimeterVertex n) (no : v.1∉F) :
          ∃ s : Arm, v=atArm hn s 1 ∨ v=atArm hn s 2 := by
        have f := mt (line v.1) no; have c := mt (corners v.1) no; have bd := v.2
        rcases v with ⟨⟨r,k⟩,vb⟩
        have hr := r.isLt; have hk := k.isLt
        simp only [straight,depthAt,depth,coord,isCorner,IsGridBoundary] at f c bd
        refine ⟨((decide (r.val>2),decide (k.val>2)),decide (k.val=0 ∨ k.val+1=n)),?_⟩
        simp only [Subtype.ext_iff,Prod.ext_iff,Fin.ext_iff,atArm,loc,decide_eq_true_eq]
        split_ifs <;> dsimp <;> omega
      obtain ⟨s,hs⟩ := near x hx; obtain ⟨t,ht⟩ := near y hy
      have same (a b : Arm) (i j : Fin 3) (hi : 0 < i.val) (hj : 0 < j.val)
          (h : (gridGraph n n).Adj (atArm hn a i).1 (atArm hn b j).1) : a=b ∧ i≠j := by
        change adjacent _ _ _ _ at h
        rcases a with ⟨⟨r,c⟩,p⟩; rcases b with ⟨⟨R,C⟩,q⟩
        have iv := i.isLt; have jv := j.isLt
        cases p <;> cases q <;> cases r <;> cases R <;> cases c <;> cases C <;>
          simp only [adjacent,Fin.ext_iff,atArm,loc] at h; all_goals dsimp at h; all_goals simp [Fin.ext_iff] <;> omega
      rcases hs with rfl|rfl <;> rcases ht with rfl|rfl <;>
        obtain ⟨rfl,ne⟩ := same _ _ _ _ (by decide) (by decide) adj
      all_goals first
        | exact (ne rfl).elim
        | exact ⟨s,mem_filter.mpr ⟨mem_univ _,hx,hy⟩,rfl⟩
        | exact ⟨s,mem_filter.mpr ⟨mem_univ _,hy,hx⟩,Sym2.eq_swap ..⟩
    · rintro ⟨a,ha,eq⟩
      obtain ⟨_,p,q⟩ := mem_filter.mp ha
      have edge : (gridGraph n n).Adj (atArm hn a 1).1 (atArm hn a 2).1 := by
        rcases a with ⟨⟨r,c⟩,b⟩; change adjacent _ _ _ _
        cases r <;> cases c <;> cases b <;> simp [adjacent,atArm,loc,Fin.ext_iff] <;> omega
      rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨edge,p,q⟩
      · exact ⟨edge.symm,q,p⟩

/-- The digits of `odd_frames.PAT`, in clockwise local coordinates. -/
def digit {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (c : Corner) : Fin 4 :=
  let w := physicalWord hn F c
  let h : Fin 4 := if w=3 then 0 else if w=7 then 1 else if w=12 then 2 else 3
  if c.1=c.2 then h else ⟨(h.val+2)%4,by omega⟩

def cornerNo : Fin 4 → Corner := ![(false,false),(false,true),(true,true),(true,false)]
def signature {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (i : Fin 4) := digit hn F (cornerNo i)
def packed (w : Fin 4 → Fin 4) := 64*(w 0).val+16*(w 1).val+4*(w 2).val+(w 3).val
def moved (w : Fin 4 → Fin 4) (g : Fin 8) (i : Fin 4) : Fin 4 :=
  if g.val<4 then w ⟨(i.val+g.val)%4,by omega⟩ else
    let d := w ⟨(g.val+4-i.val)%4,by omega⟩
    ⟨(d.val+2)%4,by omega⟩
def repCode (w : Fin 4 → Fin 4) := ((List.ofFn fun g => packed (moved w g)).foldl min 255)
def code4 (a b c d : Nat) := 64*a+16*b+4*c+d
def adjacentList := [code4 0 0 1 1,code4 0 0 1 3,code4 0 0 3 1,code4 0 0 3 3,
  code4 0 1 1 2,code4 0 1 3 2,code4 0 2 1 1,code4 0 2 1 3,code4 0 2 3 1,code4 0 3 1 2]
def oppositeList := [code4 0 1 0 1,code4 0 1 0 3,code4 0 1 2 1,code4 0 1 2 3,code4 0 3 0 3]

private theorem word_check (w : Fin 4 → Fin 4) (h : (univ.filter fun i => (w i).val%2=0).card=2) :
    repCode w ∈ (if (w 0).val%2=(w 2).val%2 then oppositeList else adjacentList) := by
  exact (by native_decide : ∀ v : Fin 4 → Fin 4,
    (univ.filter fun i => (v i).val%2=0).card=2 →
    repCode v ∈ (if (v 0).val%2=(v 2).val%2 then oppositeList else adjacentList)) w h

theorem gaps_at {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (c : Corner)
    (hw : physicalWord hn F c ∈ [3,7,12,13]) :
    (if (digit hn F c).val%2=0 then 1 else 0 : Nat) = ∑ a : Bool, if (c,a)∈gaps hn F then 1 else 0 := by
  have sumBool (f : Bool → Nat) : ∑ b, f b=f false+f true := by simp [Finset.sum_insert,add_comm]
  rw [sumBool]
  simp only [digit,physicalWord,bits,gaps,mem_filter,mem_univ,true_and,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
  by_cases a : (atArm hn (c,false) 1).1∈F <;> by_cases b : (atArm hn (c,false) 2).1∈F <;>
    by_cases d : (atArm hn (c,true) 1).1∈F <;> by_cases e : (atArm hn (c,true) 2).1∈F <;>
    by_cases t : c.1=c.2 <;> simp [a,b,d,e,t] at hw ⊢

/-- Classification of the *actual* two missing perimeter edges of a score
witness. Opposite gaps are distinguished before any frame exchange. -/
theorem physical_classes (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) :
    let w := signature (n:=35+42*u) (by omega) F
    (univ.filter fun i => (w i).val%2=0).card=2 ∧
    repCode w ∈ (if (w 0).val%2=(w 2).val%2 then oppositeList else adjacentList) := by
  obtain ⟨P,_,step,_,_,_,good,_⟩ := frame_of_score u F acy score
  have hn : 35≤35+42*u := by omega
  have eq := exact_holes hn F (corners_marked u F acy score)
    (fun v => (star_geometry hn F P step v (good (.inl v))).1)
  rw [eq,card_image_of_injective _ (gapEdge_inj hn)] at two
  have fil (D : Finset Arm) : (∑ x : Arm, if x∈D then 1 else 0 : Nat)=D.card := by simp
  have sum := fil (gaps hn F)
  rw [Fintype.sum_prod_type] at sum
  simp_rw [←gaps_at hn F _ (physicalWord_ok hn F P good _)] at sum
  have eqSum (f : Corner → Nat) : ∑ i : Fin 4, f (cornerNo i)=∑ x : Corner, f x := by
    rw [Fintype.sum_prod_type]; simp [Fin.sum_univ_four,cornerNo,add_comm,add_left_comm,add_assoc]
  let w := signature hn F
  have num : (univ.filter fun i => (w i).val%2=0).card=2 := by
    calc
      _ = ∑ i : Fin 4, (if (w i).val%2=0 then 1 else 0 : Nat) := by simp
      _ = _ := (eqSum _).trans (sum.trans two)
  exact ⟨num,word_check w num⟩

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Words
