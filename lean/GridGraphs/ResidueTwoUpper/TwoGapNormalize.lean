import GridGraphs.ResidueTwoUpper.TwoGapFlip

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Exchange
open ResidueZero Stencil Words Box BoundarySix.Connected Finset

private theorem armRule {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (c t : Corner)
    (a o : Bool) (j : Fin 3) (_nz : j.val≠0) :
    bits hn (exchange c o F) (t,a) j=bits hn F (t,if t=c then !a else a) j := by
  let v := (atArm hn (t,a) j).1
  have J := j.isLt
  by_cases same : t=c
  · subst t
    have mem : box c o v := by
      rcases c with ⟨r,k⟩; cases r <;> cases k <;> cases a <;>
        dsimp [box,axes,near,v,atArm,loc] <;> omega
    have eq : flip c v=(atArm hn (c,!a) j).1 := by
      rcases c with ⟨r,k⟩; cases r <;> cases k <;> cases a <;> ext <;>
        simp [flip,atArm,v,loc,Fin.rev] <;> omega
    change (decide (v∈exchange c o F)).toNat=_
    simp [bits,exchange,mem,eq]
  · have notIn : ¬box c o v := by
      rcases c with ⟨r,k⟩; rcases t with ⟨x,y⟩
      cases r <;> cases k <;> cases x <;> cases y <;> cases a <;>
        dsimp [box,axes,near,v,atArm,loc] at * <;> first | exact False.elim (same rfl) | omega
    change (decide (v∈exchange c o F)).toNat=_
    simp [bits,exchange,notIn,same,v] at *

private theorem normal_step {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (c : Corner) :
    let hn : 35≤35+42*u := by omega
    let M := exchange c (opened hn F c) F
    (perimeterHoles M).card=2 ∧
    ∀ t, (digit hn M t).val=(if t=c then ((digit hn F t).val+2)%4 else (digit hn F t).val) := by
  have hn : 35≤35+42*u := by omega
  let o := opened hn F c
  let M := exchange c o F
  have forest := exchange_forest F acy score two c
  have sz : M.card=440+1020*u+588*u^2 := (card_exchange ..).trans score
  obtain ⟨P,_,step,_,_,_,good,_⟩ := Frame.frame_of_score u F acy score
  obtain ⟨Q,_,next,_,_,_,post,_⟩ := Frame.frame_of_score u M forest sz
  have act (t : Corner) : (digit hn M t).val=(if t=c then ((digit hn F t).val+2)%4 else (digit hn F t).val) := by
    have old := physicalWord_ok hn F P good t
    have B (a : Bool) (j : Fin 3) (nz : j.val≠0) := armRule hn F c t a o j nz
    have repl : physicalWord hn M t =
        8*bits hn F (t,if t=c then true else false) 1 +4*bits hn F (t,if t=c then true else false) 2 +
        2*bits hn F (t,if t=c then false else true) 1 + bits hn F (t,if t=c then false else true) 2 := by
      unfold physicalWord; rw [B false 1 (by decide),B false 2 (by decide),B true 1 (by decide),B true 2 (by decide)]; rfl
    let D (z : Nat) : Fin 4 := if z=3 then 0 else if z=7 then 1 else if z=12 then 2 else 3
    let read (b : Bool) (z : Nat) := if b then (D z).val else ((D z).val+2)%4
    have digit_eq (L : Finset _) : (digit hn L t).val = read (decide (t.1=t.2)) (physicalWord hn L t) := by
      by_cases h : t.1=t.2 <;> simp [digit,read,D,h]
    rw [digit_eq M,digit_eq F]
    rw [repl]; by_cases same : t=c
    · simp only [if_pos same]; unfold physicalWord at old ⊢
      have bound (a : Bool) (j : Fin 3) : bits hn F (t,a) j<2 := by
        unfold bits; cases decide ((atArm hn (t,a) j).1∈F) <;> decide
      have tab : ∀ (a b d e : Fin 2) (x : Bool),
          (8*a.val+4*b.val+2*d.val+e.val)∈[3,7,12,13] →
          read x (8*d.val+4*e.val+2*a.val+b.val)=(read x (8*a.val+4*b.val+2*d.val+e.val)+2)%4 := by native_decide
      exact tab ⟨_,bound false 1⟩ ⟨_,bound false 2⟩ ⟨_,bound true 1⟩ ⟨_,bound true 2⟩ _ old
    · simp [same,physicalWord]
  have holes (L : Finset (GridVertex (35+42*u) (35+42*u))) (O : _ → _)
      (legal : (Bonds L).IsAcyclic) (card : L.card=440+1020*u+588*u^2)
      (s : ∀ x, O x≠x → (Bonds L).Adj x (O x)) (g : ∀ x, Frame.allGood L O x) :
      (perimeterHoles L).card=∑ t : Corner, if (digit hn L t).val%2=0 then 1 else 0 := by
    rw [exact_holes hn L (corners_marked u L legal card) (fun x => (Frame.star_geometry hn L O s x (g _)).1),
      card_image_of_injective _ (gapEdge_inj hn)]
    simp_rw [gaps_at hn L _ (physicalWord_ok hn L O g _)]
    rw [←Fintype.sum_prod_type (fun x : Arm => if x∈gaps hn L then 1 else (0:Nat))]; simp
  refine ⟨?_,act⟩
  change (perimeterHoles M).card=2
  rw [←two,holes M Q forest sz next post,holes F P acy score step good]
  apply sum_congr rfl; intro t _
  rw [act]; split_ifs <;> omega

/-- Independent physical exchanges at all four corners. Preserves the
score and the *locations of the two open corners*, including opposite
corners. The resulting actual digits are 0 (open) and 1 (closed). -/
theorem normalize {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) :
    ∃ L : Finset (GridVertex (35+42*u) (35+42*u)), (Bonds L).IsAcyclic ∧
      L.card=440+1020*u+588*u^2 ∧ (perimeterHoles L).card=2 ∧
      ∀ c, (digit (by omega) L c).val=(digit (by omega) F c).val%2 := by
  have hn : 35≤35+42*u := by omega
  have run (s : Finset Corner) : ∃ L : Finset (GridVertex (35+42*u) (35+42*u)),
      (Bonds L).IsAcyclic ∧ L.card=440+1020*u+588*u^2 ∧ (perimeterHoles L).card=2 ∧
      ∀ c, (digit hn L c).val=if c∈s then (digit hn F c).val%2 else (digit hn F c).val := by
    induction s using Finset.induction_on with
    | empty => exact ⟨F,acy,score,two,by simp⟩
    | @insert c s fresh ih =>
      obtain ⟨L,hL,sc,gap,done⟩ := ih
      have prev := done c; rw [if_neg fresh] at prev
      by_cases small : (digit hn L c).val<2
      · refine ⟨L,hL,sc,gap,?_⟩
        intro t; rw [done]; by_cases eq : t=c
        · subst t; simp [fresh,←prev,Nat.mod_eq_of_lt small]
        · simp [eq]
      · let M := exchange c (opened hn L c) L
        obtain ⟨g,act⟩ := normal_step L hL sc gap c
        refine ⟨M,exchange_forest L hL sc gap c,(card_exchange ..).trans sc,g,?_⟩
        intro t; rw [act]; by_cases eq : t=c
        · subst t; have lim := (digit hn L c).isLt; simp [←prev]; omega
        · simp [eq,done]
  obtain ⟨L,a,b,d,h⟩ := run univ
  exact ⟨L,a,b,d,by simpa using h⟩

/-- Only the adjacent-open and opposite-open normalized charts remain.
An arbitrary successful exchange need not literally produce `0011` at
the original NW corner; the representative below uses cyclic rotation. -/
theorem normal_forms {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) :
    ∃ L : Finset (GridVertex (35+42*u) (35+42*u)), (Bonds L).IsAcyclic ∧
      L.card=440+1020*u+588*u^2 ∧ (perimeterHoles L).card=2 ∧
      ∃ rotation : Fin 4, let v := moved (signature (by omega) L) ⟨rotation.val,by omega⟩
      packed v=code4 0 0 1 1 ∨ packed v=code4 0 1 0 1 := by
  obtain ⟨L,a,b,d,norm⟩ := normalize F acy score two
  refine ⟨L,a,b,d,?_⟩
  have counted := (physical_classes u L a b d).1
  have form : ∀ w : Fin 4 → Fin 4, (∀ i, (w i).val<2) →
      (univ.filter fun i => (w i).val%2=0).card=2 →
      ∃ j : Fin 4, let v := moved w ⟨j.val,lt_trans j.isLt (by decide : 4<8)⟩
      packed v=code4 0 0 1 1 ∨ packed v=code4 0 1 0 1 := by native_decide
  apply form _ _ counted
  intro i; unfold signature; rw [norm]; omega

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Exchange
