import GridGraphs.ResidueTwoUpper.OneGap.L7Chart

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.L7
open ResidueZero Stencil TwoGap.Words BoundarySix.Connected Finset
open GridGraphs.ResidueTwoUpper.Exceptional.Frame

def corner (v : View) : Corner := (v.rowFar,v.colFar)
def otherEnd (v : View) : Corner :=
  if v.swap then (!v.rowFar,v.colFar) else (v.rowFar,!v.colFar)
def nearBit {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (c : Corner) (arm : Bool) (j : Fin 3) :=
  decide ((atArm hn (c,arm) j).1∈F)

private theorem closedEnd {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (c : Corner)
    (ok : physicalWord hn F c∈[3,7,12,13])
    (closed : ∀ b, (c,b)∉gaps hn F) (b : Bool) :
    nearBit hn F c b 2=true ∧ nearBit hn F c (!b) 2=true ∧
      nearBit hn F c (!b) 1 = !(nearBit hn F c b 1) := by
  have a := closed false; have d := closed true
  unfold physicalWord bits at ok
  simp only [gaps,mem_filter,mem_univ,true_and] at a d
  unfold nearBit
  cases b <;>
    by_cases e : (atArm hn (c,false) 1).1∈F <;> by_cases f : (atArm hn (c,false) 2).1∈F <;>
    by_cases g : (atArm hn (c,true) 1).1∈F <;> by_cases h : (atArm hn (c,true) 2).1∈F <;>
    simp_all

def rim {n} (F : Finset (GridVertex n n)) (v : View) (sw far : Bool) :=
  ∀ r j : Nat, r<7 → j<n → ∀ b, preset n sw far r j=some b → marked F (view v n r j)=b

set_option maxHeartbeats 2500000 in
theorem realize_on {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (v : View) (s : Bool)
    (keep : Nat → Prop) (corners : ∀ x,isCorner x → x∈F) (line : ∀ x,straight n (coord x) → x∈F)
    (empty : ∀ x,depthAt n (coord x)=1 → x∉F)
    (nearJ : ∀ i : Fin 3, i.val≠0 → keep i.val → nearBit hn F (corner v) v.swap i=s)
    (nearR : ∀ i : Fin 3, i.val≠0 → keep 0 → nearBit hn F (corner v) (!v.swap) i=(!s))
    (cl : ∀ b, (otherEnd v,b)∉gaps hn F)
    (word : physicalWord hn F (otherEnd v)∈[3,7,12,13]) :
    ∃ far, ∀ r j : Nat, keep j → r<7 → j<n → ∀ b, preset n s far r j=some b → marked F (view v n r j)=b := by
  let far := nearBit hn F (otherEnd v) v.swap 1
  obtain ⟨fj,fr,f1⟩ := closedEnd hn F (otherEnd v) word cl v.swap
  have A (i : Fin 3) : coord (atArm hn (corner v,v.swap) i).1=view v n 0 i.val := by
    cases v with | mk x y t => cases t <;> cases x <;> cases y <;>
      ext <;> simp [corner,coord,atArm,loc,view,reflect] <;> omega
  have B (i : Fin 3) : coord (atArm hn (corner v,!v.swap) i).1=view v n i.val 0 := by
    cases v with | mk x y t => cases t <;> cases x <;> cases y <;>
      ext <;> simp [corner,coord,atArm,loc,view,reflect] <;> omega
  have C (i : Fin 3) : coord (atArm hn (otherEnd v,v.swap) i).1=view v n 0 ((n:Int)-1-i.val) := by
    cases v with | mk x y t => cases t <;> cases x <;> cases y <;>
      ext <;> simp [otherEnd,coord,atArm,loc,view,reflect] <;> omega
  have D (i : Fin 3) : coord (atArm hn (otherEnd v,!v.swap) i).1=view v n i.val ((n:Int)-1) := by
    cases v with | mk x y t => cases t <;> cases x <;> cases y <;>
      ext <;> simp [otherEnd,coord,atArm,loc,view,reflect] <;> omega
  have calcBit {p : Pos} {c : Corner} {b : Bool} {i : Fin 3}
      (e : coord (atArm hn (c,b) i).1=p) : marked F p=nearBit hn F c b i := by
    rw [←e,marked_at]; rfl
  refine ⟨far,?_⟩
  intro r j kept hr hj b e
  let x := onSite (view v n r j) (inside_view v (by omega : r<n) hj)
  have ex : coord x=view v n r j := coord_onSite ..
  have geo : depthAt n (coord x)=min (r:Int) (min (j:Int) (n-1-j)) ∧
      max (depth (n-1) (coord x).1) (depth (n-1) (coord x).2)=
        max (r:Int) (min (j:Int) (n-1-j)) ∧
      (isCorner x ↔ r=0 ∧ (j=0 ∨ j+1=n)) := by
    unfold isCorner; have xr := congrArg Prod.fst ex; have xc := congrArg Prod.snd ex
    rw [ex]
    cases v with | mk a k s => cases a <;> cases k <;> cases s <;>
      simp [depthAt,depth,coord,view,reflect] at xr xc ⊢ <;> omega
  have normal (bd : r=0 ∨ j=0 ∨ j+1=n) (nonarm :
      (r=0 → j≠1 ∧ j≠2 ∧ j+2≠n ∧ j+3≠n) ∧
      (j=0 ∨ j+1=n → r≠1 ∧ r≠2)) : marked F (view v n r j)=true := by
    rw [←ex,marked_at,decide_eq_true_eq]
    by_cases cr : isCorner x
    · exact corners _ cr
    · apply line; unfold straight
      push_cast [Nat.cast_sub (by omega : 1≤n)]
      rw [geo.1,geo.2.1]
      have nc : ¬(r=0 ∧ (j=0 ∨ j+1=n)) := fun e => cr (geo.2.2.mpr e)
      rcases bd with rfl|rfl|last
      · have hh := nonarm.1 rfl
        constructor <;> omega
      · have hh := nonarm.2 (.inl rfl)
        constructor <;> omega
      · have hh := nonarm.2 (.inr last)
        constructor <;> omega
  unfold preset at e
  by_cases rz : r=0
  · subst r
    simp only [if_pos rfl] at e
    rcases eq_or_ne j 1 with rfl|n1
    · simpa using (calcBit (A 1)).trans ((nearJ 1 (by decide) kept).trans (by simpa using e))
    rcases eq_or_ne j 2 with rfl|n2
    · simpa using (calcBit (A 2)).trans ((nearJ 2 (by decide) kept).trans (by simpa using e))
    by_cases far1 : j+2=n
    · have z : (j:Int)=n-1-(1:Fin 3).val := by omega
      rw [z]; refine (calcBit (C 1)).trans ?_
      simpa [far,n1,n2,far1] using e
    by_cases far2 : j+3=n
    · have z : (j:Int)=n-1-(2:Fin 3).val := by omega
      rw [z]; refine ((calcBit (C 2)).trans fj).trans ?_
      simpa [n1,n2,show j+2≠n by omega] using e
    rw [normal (Or.inl rfl) (by omega)]
    simpa [n1,n2,far1] using e
  · by_cases jz : j=0 ∨ j+1=n
    · rcases jz with rfl|end'
      · rcases eq_or_ne r 1 with rfl|n1
        · simpa using (calcBit (B 1)).trans ((nearR 1 (by decide) kept).trans (by simpa [rz] using e))
        rcases eq_or_ne r 2 with rfl|n2
        · simpa using (calcBit (B 2)).trans ((nearR 2 (by decide) kept).trans (by simpa [rz] using e))
        rw [normal (by omega) (by omega)]
        simpa [rz,n1,n2] using e
      · have zz : (j:Int)=n-1 := by omega
        by_cases h1 : r=1
        · subst r; rw [zz]; refine ((calcBit (D 1)).trans f1).trans ?_
          simpa [rz,show j≠0 by omega,end',far] using e
        by_cases h2 : r=2
        · subst r; rw [zz]; refine ((calcBit (D 2)).trans fr).trans ?_
          simpa [show j≠0 by omega,end'] using e
        rw [normal (by omega) (by omega)]
        simpa [rz,show j≠0 by omega,end',h1] using e
    · by_cases ring : r=1 ∨ j=1 ∨ j+2=n
      · have z := empty x (by omega)
        rw [←ex,marked_at]; simpa [z,rz,show j≠0 by omega,show j+1≠n by omega,ring] using e
      · simp [rz,show j≠0 by omega,show j+1≠n by omega,ring] at e

private theorem realize {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (v : View) (s : Bool)
    (corners : ∀ x,isCorner x → x∈F) (line : ∀ x,straight n (coord x) → x∈F)
    (empty : ∀ x,depthAt n (coord x)=1 → x∉F)
    (nearJ : ∀ i : Fin 3, i.val≠0 → nearBit hn F (corner v) v.swap i=s)
    (nearR : ∀ i : Fin 3, i.val≠0 → nearBit hn F (corner v) (!v.swap) i=(!s))
    (cl : ∀ b, (otherEnd v,b)∉gaps hn F)
    (word : physicalWord hn F (otherEnd v)∈[3,7,12,13]) :
    ∃ far, rim F v s far := by
  obtain ⟨f,h⟩ := realize_on hn F v s (fun _ => True) corners line empty
    (fun i hi _ => nearJ i hi) (fun i hi _ => nearR i hi) cl word
  exact ⟨f,fun r j => h r j trivial⟩

theorem pair_rim {n} (hn : 35≤n) (F : Finset (GridVertex n n))
    (corners : ∀ x,isCorner x → x∈F) (line : ∀ x,straight n (coord x) → x∈F)
    (empty : ∀ x,depthAt n (coord x)=1 → x∉F)
    (word : ∀ c, physicalWord hn F c∈[3,7,12,13]) (one : (perimeterHoles F).card=1) :
    ∃ v f g, rim F v false f ∧ rim F (turnView v) true g := by
  classical
  rw [exact_holes hn F corners line,card_image_of_injective _ (gapEdge_inj hn)] at one
  obtain ⟨⟨c,b⟩,eq⟩ := card_eq_one.mp one
  have hole : (c,b)∈gaps hn F := eq ▸ mem_singleton_self _
  obtain ⟨_,h1,h2⟩ := mem_filter.mp hole
  have other : ∀ i : Fin 3, i.val≠0 → nearBit hn F c (!b) i=true := by
    have ok := word c
    unfold physicalWord bits at ok
    intro i
    cases b <;> fin_cases i <;> simp_all [nearBit] <;>
      by_cases x : (atArm hn (c,false) 1).1∈F <;> by_cases y : (atArm hn (c,false) 2).1∈F <;>
      by_cases z : (atArm hn (c,true) 1).1∈F <;> by_cases k : (atArm hn (c,true) 2).1∈F <;> simp_all
  let v : View := ⟨c.1,c.2,b⟩
  have vac : ∀ i : Fin 3, i.val≠0 → nearBit hn F c b i=false := by
    intro i; fin_cases i <;> simp [nearBit,h1,h2]
  have closed (w : View) (ne : otherEnd w≠c) (b' : Bool) : (otherEnd w,b')∉gaps hn F := by
    rw [eq,mem_singleton]; exact fun e => ne (congrArg Prod.fst e)
  have nec : otherEnd v≠c ∧ otherEnd (turnView v)≠c := by
    rcases c with ⟨x,y⟩; cases x <;> cases y <;> cases b <;> decide
  obtain ⟨f,hf⟩ := realize hn F v false corners line empty vac other (closed _ nec.1) (word _)
  obtain ⟨g,hg⟩ := realize hn F (turnView v) true corners line empty other
    (by simpa [turnView,v,corner] using vac) (closed _ nec.2) (word _)
  exact ⟨v,f,g,hf,hg⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.L7
