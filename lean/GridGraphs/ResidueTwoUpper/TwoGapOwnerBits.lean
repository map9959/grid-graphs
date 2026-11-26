import GridGraphs.ResidueTwoUpper.TwoGapLocalOwners

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
open SimpleGraph ResidueZero

abbrev Agent {n} (F : Finset (GridVertex n n)) := {x // isolated F x} ⊕ Cell n
def locAgent {n} {F : Finset (GridVertex n n)} : Agent F → Pos ⊕ Pos :=
  Sum.elim (fun x => .inl (coord x.1)) (fun f => .inr (coord f))
private theorem loc_inj {n} {F : Finset (GridVertex n n)} : Function.Injective (@locAgent n F) := by
  rintro (x|x) (y|y) eq <;> simp only [locAgent,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,
    Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at eq ⊢
  · exact Subtype.ext (coord_injective eq)
  · exact coord_injective eq

private def slots (p : Pos) (v : Bool) : Fin 4 → Pos ⊕ Pos :=
  ![.inl p,.inl (edgeBase p v),.inr p,.inr (cellDir p (if v then 0 else 1))]
private theorem slots_inj (p : Pos) (v : Bool) : Function.Injective (slots p v) := by
  obtain ⟨r,c⟩ := p; intro i j eq
  cases v <;> fin_cases i <;> fin_cases j <;> simp [slots,edgeBase,cellDir] at eq ⊢ <;> omega

private theorem gridKey {n : Nat} (p : Pos) (v : Bool) (hp : inside n p) (hq : inside n (edgeBase p v)) :
    ∃ e : GridEdge n n, key e=(p,v) := by
  obtain ⟨r,c⟩ := p; cases v <;> simp [inside,edgeBase] at hp hq
  · exact ⟨.horizontal ⟨⟨r.toNat,by omega⟩,⟨c.toNat,by omega⟩⟩,by simp [key]; omega⟩
  · exact ⟨.vertical ⟨⟨r.toNat,by omega⟩,⟨c.toNat,by omega⟩⟩,by simp [key]; omega⟩
private theorem key_coords {n} (e : GridEdge n n) :
    coord e.primalEndpoints.1=(key e).1 ∧ coord e.primalEndpoints.2=edgeBase (key e).1 (key e).2 := by
  cases e <;> simp [coord,key,edgeBase,horizontalPrimalEndpoints,verticalPrimalEndpoints]

theorem blank_iff {n} (hn : 2≤n) (F : Finset (GridVertex n n)) (x : GridVertex n n) :
    isolated F x ↔ (!marked F (coord x) && (List.range 4).all (fun d => !marked F (shift (coord x) d)))=true := by
  simp only [marked_at,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,List.mem_range,decide_eq_false_iff_not]
  constructor
  · intro iso
    constructor
    · intro mark
      let j : Fin n := if x.2.val=0 then ⟨1,by omega⟩ else ⟨x.2.val-1,by have := x.2.isLt; omega⟩
      have grid : (gridGraph n n).Adj x (x.1,j) := by
        change adjacent _ _ _ _; unfold adjacent; left; refine ⟨rfl,?_⟩; dsimp [j]; split_ifs <;> dsimp <;> omega
      exact iso _ ⟨grid,Or.inl mark⟩
    · intro d hd; apply Bool.eq_false_iff.mpr; intro m
      obtain ⟨y,hy,eq⟩ := Finset.mem_image.mp (show shift (coord x) d∈F.image coord by simpa [marked] using m)
      have grid : (gridGraph n n).Adj x y := by
        change adjacent _ _ _ _; simp only [adjacent,Fin.ext_iff]
        interval_cases d <;> simp [shift,coord,Prod.ext_iff] at eq <;> omega
      exact iso _ ⟨grid,Or.inr hy⟩
  · rintro ⟨no,nb⟩ y edge
    have mark := edge.2.resolve_left no
    have hd : outDir x y<4 := by unfold outDir; rw [if_neg edge.ne]; split_ifs <;> decide
    have e := nb _ hd
    rw [shift_out edge.1,marked_at] at e
    simp [show y∈F from mark] at e

noncomputable def literal {n} {F : Finset (GridVertex n n)} (own : Agent F → GridEdge n n)
    (s : Pos ⊕ Pos) (k : Pos × Bool) : Bool := by
  classical
  exact decide (∃ a, locAgent a=s ∧ key (own a)=k)

theorem owner_field {n} (hn : 2≤n) (F : Finset (GridVertex n n)) (acy : (Bonds F).IsAcyclic)
    (root : GridVertex n n) (active : ¬isolated F root)
    (reach : ∀ x y, (Bonds F).Adj x y → (Bonds F).Reachable root x) :
    ∃ ext fs, OwnerField n (marked F) ext fs := by
  classical
  obtain ⟨own,inj,pe,ce,cover⟩ := free_matching hn F acy root active reach
  let ext (p : Pos) (d : Nat) := literal own (.inl p) (port p d)
  let fs (p : Pos) (d : Nat) := literal own (.inr p) (side p d)
  have lit (l k) : literal own l k=true ↔ ∃ a, locAgent a=l ∧ key (own a)=k := by simp [literal]
  have unique {s a b k l} (ha : locAgent (F:=F) a=s) (hb : locAgent b=s)
      (x : key (own a)=k) (y : key (own b)=l) : k=l := by
    have eq := loc_inj (ha.trans hb.symm); subst b; exact x.symm.trans y
  refine ⟨ext,fs,⟨?_,?_,?_,?_,?_⟩⟩
  · intro p hp
    let x := onSite p hp
    have cx : coord x=p := coord_onSite ..
    constructor
    · rw [←cx,←blank_iff hn F]
      constructor
      · intro h
        let v := (⟨x,h⟩ : {v // isolated F v})
        obtain ⟨d,ok,_⟩ := port_inc _ x (pe v)
        exact ⟨d,(lit ..).mpr ⟨.inl v,rfl,ok⟩⟩
      · rintro ⟨i,b⟩
        obtain ⟨a,l,_⟩ := (lit ..).mp b
        cases a with
        | inl a => exact coord_injective (Sum.inl.inj l) ▸ a.2
        | inr f => contradiction
    · intro i j a b; obtain ⟨s,h,e⟩ := (lit ..).mp a; obtain ⟨t,k,g⟩ := (lit ..).mp b
      exact (distinct_ports p).1 (unique h k e g)
  · intro p hp
    have cast : (n:Int)-1=((n-1:Nat):Int) := by omega
    rw [cast] at hp
    let f := onSite p hp
    have cx : coord f=p := coord_onSite ..
    constructor
    · constructor
      · intro _; obtain ⟨d,ok,_⟩ := side_inc _ f (ce f)
        exact ⟨d,(lit ..).mpr ⟨.inr f,congrArg Sum.inr cx,cx ▸ ok⟩⟩
      · simp
    · intro i j a b; obtain ⟨s,h,e⟩ := (lit ..).mp a; obtain ⟨t,k,g⟩ := (lit ..).mp b
      exact (distinct_ports p).2 (unique h k e g)
  · intro p off d; apply Bool.eq_false_iff.mpr; intro yes
    obtain ⟨v,loc,_⟩ := (lit ..).mp yes
    cases v with
    | inl v => contradiction
    | inr f =>
      have h := coord_inside f
      exact off (by rw [←Sum.inr.inj loc,show (n:Int)-1=((n-1:Nat):Int) by omega]; exact h)
  · intro p _ d off; apply Bool.eq_false_iff.mpr; intro yes
    obtain ⟨a,eq,kk⟩ := (lit ..).mp yes
    have bounds := key_coords (own a)
    rw [kk] at bounds
    have A := coord_inside (own a).primalEndpoints.1; have B := coord_inside (own a).primalEndpoints.2
    rw [bounds.1] at A; rw [bounds.2] at B
    fin_cases d <;> simp [port,edgeBase,shift] at off A B <;> first | exact Bool.noConfusion (off.symm.trans A) | exact Bool.noConfusion (off.symm.trans B)
  · intro p v a b
    have entry (i : Fin 4) : picks ext fs p v i=literal own (slots p v i) (p,v) := by
      obtain ⟨r,c⟩ := p; cases v <;> fin_cases i <;> simp [picks,ext,fs,slots,cellDir,edgeBase,port,side]
    obtain ⟨e,hk⟩ := gridKey p v a b
    have ⟨fst,snd⟩ := key_coords e; rw [hk] at fst snd
    have hit : (!(marked F p || marked F (edgeBase p v)))=true ↔ ∃ x, own x=e := by
      dsimp only at fst snd; rw [←snd,←fst,marked_at,marked_at,cover]
      simp
    constructor
    · rw [hit]; constructor
      · rintro ⟨x,h⟩
        have select : ∃ i : Fin 4, locAgent x=slots p v i := by
          cases x with
          | inl x =>
            have inc := pe x; rw [h] at inc
            rcases inc with l|l
            · exact ⟨0,by cases v <;> simpa [slots,locAgent,←l] using congrArg (Sum.inl (β:=Pos)) fst⟩
            · exact ⟨1,by cases v <;> simpa [slots,locAgent,←l] using congrArg (Sum.inl (β:=Pos)) snd⟩
          | inr f =>
            have inc := ce f; rw [h] at inc
            obtain ⟨d,l,_⟩ := side_inc e f inc
            rw [hk] at l
            obtain ⟨r,c⟩ := f
            fin_cases d <;> cases v <;> simp [side,coord,Prod.ext_iff] at l
            all_goals first
              | solve | refine ⟨2,?_⟩; simp [slots,locAgent,coord,Prod.ext_iff]; omega
              | solve | refine ⟨3,?_⟩; simp [slots,locAgent,cellDir,coord,Prod.ext_iff]; omega
        obtain ⟨i,hi⟩ := select
        exact ⟨i,by rw [entry]; exact (lit ..).mpr ⟨x,hi,h ▸ hk⟩⟩
      · rintro ⟨i,hi⟩; rw [entry] at hi; obtain ⟨x,_,eq⟩ := (lit ..).mp hi
        exact ⟨x,key_inj (eq.trans hk.symm)⟩
    · intro i j h g; rw [entry] at h g
      obtain ⟨s,hs,es⟩ := (lit ..).mp h; obtain ⟨t,ht,et⟩ := (lit ..).mp g
      have eq := inj (key_inj (es.trans et.symm)); subst t
      exact slots_inj p v (hs.symm.trans ht)

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
