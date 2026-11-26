import GridGraphs.ResidueTwoUpper.TwoGapPhysicalField

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
open ResidueZero Stencil Words BoundarySix.Connected

private theorem rimTests (u q : Nat) (x : GridVertex (35+42*u) (35+42*u)) :
    let r := rimDatum (11+14*(u:Int)) q x.2.val x.1.val
    (r.2.1<5 → IsGridBoundary x) ∧
      (r.2.2=true → x.1.val=2 ∧ 3≤x.2.val ∧ x.2.val+3≤34+42*u ∧ x.2.val≠2+3*q) := by
  let z := 3*(11+14*(u:Int))+1
  have R := x.1.isLt; have K := x.2.isLt
  have nz (t : Int) (ht : 0≤t) : 0≤clip t := by unfold clip; omega
  have pos : ¬min (min (clip (x.1.val:Int)) (clip (z-x.1.val))) (min (clip x.2.val) (clip (z-x.2.val)))<0 := by
    have := nz _ (Int.natCast_nonneg x.1.val); have := nz _ (Int.natCast_nonneg x.2.val)
    have := nz (z-x.1.val) (by dsimp [z]; omega); have := nz (z-x.2.val) (by dsimp [z]; omega); omega
  unfold rimDatum; dsimp only; rw [if_neg pos]; dsimp only
  constructor
  · intro h; unfold IsGridBoundary
    split_ifs at h <;> unfold clip at * <;> omega
  · simp only [decide_eq_true_eq]; unfold clip; omega

private theorem atoms {u q} {F : Finset (GridVertex (35+42*u) (35+42*u))} {P}
    (C : North.Chart F P (2+3*q)) (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (x : GridVertex (35+42*u) (35+42*u)) :
    let p := coord x; let f := (decide (x∈F)).toNat; let nb := neighbours F p; let o := outDir x (P x)
    let a := representative 23 (4+14*(u:Int)) p
    o<5 ∧ starOK 23 a f nb o ∧ (if p.1=0 ∧ p.2=0 then o=4 else o=4 → f=0 ∧ nb=0) ∧
      twoOrbitStar 23 a f nb o=(if p.1=0 ∧ p.2=2+3*(q:Int) then full else 0) := by
  dsimp only
  have atP := transported (k:=11+14*(u:Int)) (by omega) (coord x) (decide (x∈F)).toNat (neighbours F (coord x)) (outDir x (P x)) 0
  rw [show (11+14*(u:Int))-7=4+14*u by ring,show 3*(11+14*(u:Int))+2=((35+42*u:Nat):Int) by push_cast; ring] at atP
  refine ⟨outDir_lt ..,atP.2.1 ▸ starOK_physical F acy x (P x) (fun ne => C.step _ ne.symm),?_,?_⟩
  · have fix : P (nw u)=nw u := North.rc_inj (C.perimeter (nw u) (Or.inl rfl))
    split_ifs with xy
    · have eq : x=nw u := by apply coord_injective; exact Prod.ext xy.1 xy.2
      simp [eq,fix,outDir]
    · intro four
      have same : P x=x := by by_contra ne; unfold outDir at four; rw [if_neg (Ne.symm ne)] at four; split_ifs at four <;> contradiction
      have isolated' : isolated F x := fun y e => xy (by
        have eq := Frame.isolated_fixed P C.arrows fix (all_active_reachable u F acy score e).1 same
        rw [←eq]; exact ⟨rfl,rfl⟩)
      have h := (blank_iff (by omega) F x).mp isolated'
      simp only [marked_at,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,List.all_eq_true,List.mem_range] at h
      refine ⟨by simp [h.1],?_⟩
      unfold neighbours; have eq : (fun d : Fin 4 => marked F (shift (coord x) d.val))=fun _ => false :=
        funext fun d => h.2 _ d.isLt
      rw [eq]; decide
  · obtain ⟨v,hv,wd,zero⟩ := C.sole
    rw [←atP.1]
    split_ifs with pos
    · have eq : x=v := North.rc_inj (by rw [hv]; apply Prod.ext <;> dsimp [North.rc,coord] at * <;> omega)
      exact eq ▸ wd
    · exact zero (.inl x) (by intro h; obtain rfl := Sum.inl.inj h
                              apply pos; have h := Prod.mk.inj hv; simp only [coord,North.rc] at h ⊢; omega)

private theorem arcs {n} {F : Finset (GridVertex n n)} {P : GridVertex n n → GridVertex n n}
    {s : Field} (g : Global F P s) (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (arr : ∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) (p : Pos) (inp : inside n p) (d : Fin 4)
    (inq : inside n (shift p d)) :
    let z := shift p d; let rev : Fin 4 := ⟨(d.val+2)%4,by omega⟩
    ((s.dir p=d.val ∨ s.dir z=rev.val) ↔ (s.mark p || s.mark z)=true) ∧
      ¬(s.dir p=d.val ∧ s.dir z=rev.val) := by
  let x := onSite p inp; let y := onSite _ inq
  have X : coord x=p := coord_onSite ..; have Y : coord y=shift p d := coord_onSite ..
  let rev : Fin 4 := ⟨(d.val+2)%4,by omega⟩
  have f : shift (coord x) d=coord y := by rw [X,Y]
  have b : shift (coord y) rev=coord x := by rw [X,Y]; fin_cases d <;> simp [shift,rev]
  dsimp only; rw [←Y,←X,g.dirs,g.marks,lift_coord,lift_coord,marked_at,marked_at]
  change ((outDir x (P x)=d.val ∨ outDir y (P y)=rev.val) ↔ _) ∧ ¬(_ ∧ outDir y (P y)=rev.val)
  rw [arrow_point step x y d f,arrow_point step y x rev b]
  simp only [Bool.or_eq_true,decide_eq_true_eq]
  have grid := step_grid d f
  have ne := grid.ne
  have ifA : P x=y → (Bonds F).Adj x y := fun e => e ▸ step _ (by simpa [e] using ne.symm)
  have ifB : P y=x → (Bonds F).Adj x y := fun e => (e ▸ step _ (by simpa [e] using ne)).symm
  constructor
  · constructor
    · exact fun h => (h.elim ifA ifB).2
    · intro h; by_cases b : P y=x; exact Or.inr b; exact Or.inl ((arr _ _ ⟨grid,h⟩).mpr b)
  · exact fun ⟨e,h⟩ => (arr _ _ (ifA e)).mp e h

private theorem turnAt {n} {F : Finset (GridVertex n n)} {P : GridVertex n n → GridVertex n n}
    {s : Field} (g : Global F P s) (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (p : Pos) (h : inside n p) (d e : Fin 4) (a : s.dir p=d) (b : s.dir (shift p d)=e) :
    s.sheet (shift p d)=xor (s.sheet p) (wrap d e) := by
  let x := onSite p h
  have X : coord x=p := coord_onSite ..
  rw [←X,g.dirs,lift_coord] at a
  have ne : P x≠x := by intro eq; rw [eq] at a; simp [outDir] at a; have := d.isLt; omega
  have move := shift_out (step x ne).1; rw [X,a] at move
  rw [move,g.dirs,lift_coord] at b
  have ny : P (P x)≠P x := by intro eq; rw [eq] at b; simp [outDir] at b; have := e.isLt; omega
  rw [move,←X,←a,←b]; exact g.turns x (P x) (P (P x)) rfl ne.symm rfl ny.symm

private theorem patch_eq {n} {F : Finset (GridVertex n n)} {P s} (g : Global F P s)
    (i j : Int) (p : Pos) (a : origins n) (eq : coord a=shiftAt i j p) :
    patchAt (pull s i j) p=(maskAt F a).val := by
  have inj : ∀ u v : Fin 512, (∀ q : Fin 9, bit u q=bit v q) → u=v := by native_decide
  let v := fun b : Fin 9 => s.mark (shiftAt i j (plus3 p b))
  refine congrArg Fin.val (inj ⟨packed9 v,(packed_iff v).1⟩ (maskAt F a) ?_)
  intro b
  have bits := patch_bit F a.1.val a.2.val (by have := a.1.isLt; omega) (by have := a.2.isLt; omega) b
  change bit (maskAt F a) b=(marked F (coord a+offset b)).toNat at bits
  change bit (packed9 v) b=_
  rw [(packed_iff v).2 b,bits]; unfold v; rw [g.marks,offsetAt,eq]

set_option maxHeartbeats 600000 in
theorem physical_box {u q} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by omega) F)=code4 0 0 1 1) {P}
    (C : North.Chart F P (2+3*q)) {s : Field} (g : Global F P s) (i j : Int) :
    Local (sig (11+14*(u:Int)) q i j) (pull s i j) := by
  let n := 35+42*u
  let k : Int := 11+14*u
  let A := shiftAt i j
  let S := sig k q i j
  let l := pull s i j
  have N : 3*k+2=(n:Int) := by dsimp [k,n]; push_cast; ring
  have on (p : Pos) : onB S p=inside n (A p) := by simp [onB,S,sig,A,N]
  have cell (p : Pos) : cellB S p=inside ((n:Int)-1) (A p) := by simp [cellB,S,sig,A,N]
  have valid {p} (h : core S p) : inside n (A p) := on p ▸ h.2
  have mk (p : Pos) : l.mark p=marked F (A p) := congrFun g.marks (A p)
  have xy {p : Pos} (hp : core S p) : ∃ x : GridVertex n n, coord x=A p :=
    ⟨onSite _ (valid hp),coord_onSite ..⟩
  have dir {p} {x : GridVertex n n} (eq : coord x=A p) : l.dir p=outDir x (P x) := by
    change s.dir (A p)=_; rw [←eq,g.dirs,lift_coord]
  have nb (p : Pos) : nbrAt l p=neighbours F (A p) := by
    unfold nbrAt neighbours; congr 1; funext d; rw [mk]; exact congrArg (marked F) (move i j p d)
  have rim {p} {x : GridVertex n n} (eq : coord x=A p) :
      rimAt S p=rimDatum k q x.2.val x.1.val := by change rimDatum k q (A p).2 (A p).1=_; rw [←eq]; rfl
  change Local S l
  constructor
  · intro p _ off; rw [mk]; exact Bool.eq_false_iff.mpr (fun h => off (by rw [on]; exact marked_inside h))
  · intro p hp b h; obtain ⟨x,eq⟩ := xy hp
    rw [mk,←eq,marked_at]; exact chart_marks F acy score canon x q b (rim eq ▸ h)
  · intro p hp h; obtain ⟨x,eq⟩ := xy hp; rw [dir eq,rim eq]
    exact North.parent_field C rfl x ((rimTests u q x).1 (rim eq ▸ h))
  · intro p hp hr hc; obtain ⟨x,eq⟩ := xy hp
    have X := x.1.isLt; have Y := x.2.isLt
    have exp : starPos S p=representative 23 (4+14*(u:Int)) (coord x) := by
      change representative 23 (k-7) (A p)=_; rw [←eq,show k-7=4+14*(u:Int) by dsimp [k]; ring]
    rw [exp] at hr hc; simp [representative,rep,coord] at hr hc
    have c : isCorner x := by unfold isCorner; split_ifs at hr hc <;> omega
    rw [mk,←eq,marked_at]; exact decide_eq_true (corners_marked u F acy score x c)
  · intro p hp guard marked'; obtain ⟨x,eq⟩ := xy hp
    obtain ⟨r,lo,hi,ne⟩ := (rimTests u q x).2 (rim eq ▸ guard)
    rw [mk,←eq,marked_at,decide_eq_true_eq] at marked'
    have eqx : x=(⟨2,by dsimp [n]; omega⟩,x.2) := Prod.ext (Fin.ext r) rfl
    have ar := North.tooth_arrow C acy score canon x.2 ⟨lo,hi⟩ ne (by rw [←eqx]; exact marked')
    rw [dir eq]
    have e : P x=(⟨1,by omega⟩,x.2) := (congrArg P eqx).trans ar
    have ne : x≠P x := by intro h; have H := congrArg (fun w : GridVertex n n => w.1.val) (h.trans e); dsimp at H; omega
    unfold outDir; rw [if_neg ne,e]; simp only [Fin.lt_def,lt_self_iff_false,if_false,r]; decide
  · intro p hp; obtain ⟨x,eq⟩ := xy hp
    have W := atoms C acy score x
    dsimp only; rw [dir eq,nb,mk,←eq,marked_at]
    change _ ∧ starOK 23 (representative 23 (k-7) (A p)) _ _ _ ∧
      (if decide ((A p).1=0 ∧ (A p).2=0) then _ else _) ∧ twoOrbitStar 23 (representative 23 (k-7) (A p)) _ _ _=
        (if decide ((A p).1=0 ∧ (A p).2=2+3*(q:Int)) then full else 0)
    rw [←eq,show k-7=4+14*(u:Int) by dsimp [k]; ring]; simpa only [decide_eq_true_eq] using W
  · intro p _ all
    have lim (b : Fin 9) : inside n (A p+offset b) := by rw [←offsetAt]; exact (on _ ▸ all b)
    have h0 := lim 0; have h8 := lim 8
    simp [inside,offset] at h0 h8
    have inside' : inside ((n-2:Nat):Int) (A p) := by simp only [inside,Bool.and_eq_true,decide_eq_true_eq]; dsimp [A] at *; omega
    let a : origins n := onSite (A p) inside'
    have ea : coord a=A p := coord_onSite ..
    have eqm := patch_eq g i j p a ea
    obtain ⟨_,_,_,zero⟩ := C.sole
    have bill := zero (.inr a) (by intro eq; cases eq)
    change twoOrbitPatch n (coord a) (maskAt F a)=0 at bill
    change maskOK (patchAt (pull s i j) p)=true ∧ _
    rw [eqm]; refine ⟨physical_mask_ok F acy ..,?_⟩
    have trans := (transported (k:=k) (by dsimp [k]; omega) (coord a) 0 0 4 (maskAt F a)).2.2
    change twoOrbitPatch 23 (representative 21 (k-7) (A p)) _=0
    rw [←ea,←trans,N]; exact bill
  · intro p hp d next'; have h := arcs g C.step C.arrows (A p) (valid hp) d
    simp only [arc,l,pull,Function.comp_apply,move] at *
    apply h; rw [on] at next'; exact move i j p d ▸ next'
  · intro p hp d e a b
    change s.dir (A p)=_ at a; change s.dir (shiftAt i j (shift p d))=_ at b
    rw [move] at b; change s.sheet (shiftAt i j (shift p d))=_
    rw [move]; exact turnAt g C.step (A p) (valid hp) d e a b
  · intro p hp
    simpa only [l,pull,Function.comp_apply,move,A] using g.owners.sites (A p) (valid hp)
  · intro p _ cp; exact g.owners.cells (A p) (cell p ▸ cp)
  · intro p _ cp; exact g.owners.outer (A p) (cell p ▸ cp)
  · intro p hp d o
    apply g.owners.missing _ (valid hp) d; intro bad; apply o
    rw [on]; change inside n (shiftAt i j (shift p d))=true; rwa [move]
  · intro p hp v b
    have eq : picks l.ext l.fs p v=picks s.ext s.fs (A p) v := by
      funext d; cases v <;> fin_cases d <;> simp [picks,l,pull,base_move,cell_move,A,Function.comp_def]
    rw [eq]; change zeroOrOne (!(s.mark (A p) || s.mark (shiftAt i j (edgeBase p v)))) _
    rw [base_move]; apply g.owners.edges _ v (valid hp); rw [←base_move]; exact on _ ▸ b

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
