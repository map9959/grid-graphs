import GridGraphs.ResidueTwoUpper.TwoGapExchange

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Exchange
open ResidueZero Stencil SimpleGraph Finset Words Box BoundarySix.Connected

def axes {n} (c : Corner) (v : GridVertex n n) : Nat × Nat :=
  (loc n c.1 v.1.val,loc n c.2 v.2.val)
def flip {n} (c : Corner) (v : GridVertex n n) : GridVertex n n :=
  if c.1=c.2 then v.swap else (v.2.rev,v.1.rev)
private theorem invol {n} (c : Corner) (v : GridVertex n n) : flip c (flip c v)=v := by
  unfold flip; split_ifs <;> simp
private theorem flipAxes {n} (c : Corner) (v : GridVertex n n) : axes c (flip c v)=(axes c v).swap := by
  have R := v.1.isLt; have K := v.2.isLt
  rcases c with ⟨a,b⟩; cases a <;> cases b <;> ext <;> simp [axes,loc,flip,Fin.rev] <;> omega
private theorem axes_inj {n} (c : Corner) : Function.Injective (axes (n:=n) c) := by
  intro v w eq; have R := v.1.isLt; have K := v.2.isLt; have X := w.1.isLt; have Y := w.2.isLt
  rcases c with ⟨a,b⟩; cases a <;> cases b <;> simp [axes,loc,Prod.ext_iff,Fin.ext_iff] at eq ⊢ <;> omega
private theorem siteAxes {n} (hn : 35≤n) (c : Corner) (p : Site) :
    axes c (site hn c p.1 p.2)=(p.1.val,p.2.val) := by
  have R := p.1.isLt; have K := p.2.isLt
  rcases c with ⟨a,b⟩; cases a <;> cases b <;> ext <;> dsimp [axes,site,loc] <;> omega
def near (opened : Bool) (r k : Nat) := (r≤2 ∧ k≤2 ∧ (opened=true ∨ r≠2 ∨ k≠2)) ∨
  (r=3 ∧ k=0 ∨ r=0 ∧ k=3) ∨ (opened=true ∧ (r=3 ∧ k=2 ∨ r=2 ∧ k=3))
instance (o : Bool) (r k : Nat) : Decidable (near o r k) := by unfold near; infer_instance
def box {n} (c : Corner) (o : Bool) (v : GridVertex n n) := near o (axes c v).1 (axes c v).2
instance {n} (c : Corner) (o : Bool) (v : GridVertex n n) : Decidable (box c o v) := by unfold box; infer_instance
private theorem flipBox {n} (c : Corner) (o : Bool) (v : GridVertex n n) : box c o (flip c v) ↔ box c o v := by
  unfold box; rw [flipAxes]; dsimp; unfold near; tauto

def exchange {n} (c : Corner) (o : Bool) (F : Finset (GridVertex n n)) :=
  univ.filter fun x => (if box c o x then flip c x else x)∈F
theorem card_exchange {n} (c : Corner) (o : Bool) (F : Finset (GridVertex n n)) :
    (exchange c o F).card=F.card := by
  let f (x : GridVertex n n) := if box c o x then flip c x else x
  have inv (x) : f (f x)=x := by by_cases b : box c o x <;> simp [f,b,flipBox,invol]
  exact card_bij (fun x _ => f x) (fun _ hx => (mem_filter.mp hx).2)
    (fun _ _ _ _ e => (Function.LeftInverse.injective inv) e)
    (fun x hx => ⟨f x,mem_filter.mpr ⟨mem_univ _,by change f (f x)∈F; rwa [inv]⟩,inv _⟩)

def port (p : Site) := p=(0,3) ∨ p=(3,0)
instance (p : Site) : Decidable (port p) := by unfold port; infer_instance
private theorem interface : ∀ (c : Corner) (m : Fin 512) (w : Fin 16),
    w.val∈[3,7,12,13] →
    let o := decide (w.val=3 ∨ w.val=12)
    (o=true → separated c m) → (o=false → innerBit c m 2 2=0) →
    ∀ p q : Site, near o p.1 p.2 → ¬near o q.1 q.2 → touch p q →
    (port p ∧ cell c w m p.1 p.2=cell c w m p.2 p.1) ∨
      (cell c w m p.1 p.2=0 ∧ cell c w m p.2 p.1=0 ∧ cell c w m q.1 q.2=0) := by
  native_decide

private theorem boxAdj {n} (c : Corner) (x y : GridVertex n n) (h : (gridGraph n n).Adj x y) :
    let a := axes c x; let b := axes c y
    (a.1=b.1 ∧ (a.2+1=b.2 ∨ b.2+1=a.2)) ∨ (a.2=b.2 ∧ (a.1+1=b.1 ∨ b.1+1=a.1)) := by
  have R := x.1.isLt; have K := x.2.isLt; have X := y.1.isLt; have Y := y.2.isLt
  change adjacent _ _ _ _ at h
  rcases c with ⟨a,b⟩; cases a <;> cases b <;> dsimp [axes,loc]
  all_goals simp only [adjacent,Fin.ext_iff] at h; omega
private theorem flipAdj {n} (c : Corner) (x y : GridVertex n n) (h : (gridGraph n n).Adj x y) :
    (gridGraph n n).Adj (flip c x) (flip c y) := by
  have R := x.1.isLt; have K := x.2.isLt; have X := y.1.isLt; have Y := y.2.isLt
  change adjacent _ _ _ _ at h ⊢
  simp only [adjacent,Fin.ext_iff] at h ⊢; unfold flip; split_ifs <;> dsimp [Fin.rev] <;> omega

def opened {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (c : Corner) :=
  decide (physicalWord hn F c=3 ∨ physicalWord hn F c=12)

set_option maxHeartbeats 700000 in
/-- Exchange either open orientation, or either closed orientation, at
one specified physical corner. The exterior edges stay in place. -/
theorem exchange_forest {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (c : Corner) :
    (Bonds (exchange c (opened (by omega) F c) F)).IsAcyclic := by
  classical
  let n := 35+42*u
  have hn : 35≤n := by dsimp [n]; omega
  let w := physicalWord hn F c
  let m := maskAt F (origin (by omega) c 2 2)
  let o := opened hn F c
  let reg := box (n:=n) c o
  let S (p : Site) := site hn c p.1 p.2
  let M := exchange c o F
  obtain ⟨P,_,step,_,_,_,good,_⟩ := Frame.frame_of_score u F acy score
  have value (p : Site) : cell c w m p.1 p.2=(decide (S p∈F)).toNat :=
    cell_physical hn F c (corners_marked u F acy score)
      (fun x => (Frame.star_geometry hn F P step x (good (.inl x))).1)
      (fun x => (Frame.star_geometry hn F P step x (good (.inl x))).2.1) _ _
  have legal := physicalWord_ok hn F P good c
  have lim : w<16 := by change w∈_ at legal; simp only [List.mem_cons,List.not_mem_nil,or_false] at legal; omega
  have check := interface c m ⟨w,lim⟩ legal
  have sep (h : o=true) : separated c m := by
    apply decide_eq_true; intro r k rk
    have t := open_triangle F acy score two c (of_decide_eq_true h) r k rk
    let p : Site := (⟨2+r.val,by omega⟩,⟨2+k.val,by omega⟩)
    have V := value p; dsimp [p] at V
    simp [cell,show ¬(2+r.val=1 ∨ 2+k.val=1) by omega] at V
    rw [V]; split_ifs with z
    · simp [S,t.mpr z]
    · simp [S,mt t.mp z]
  have closed (h : o=false) : innerBit c m 2 2=0 := by
    have no := mt (corner_tooth F acy score two c).mp (of_decide_eq_false h)
    have V := value (2,2)
    change innerBit c m 2 2=(decide (site hn c 2 2∈F)).toNat at V
    simpa [no] using V
  have ins (x) (h : reg x) : x∈M ↔ flip c x∈F := by simp [M,exchange,h,reg] at *
  have out (x) (h : ¬reg x) : x∈M ↔ x∈F := by simp [M,exchange,h,reg] at *
  have flipS (p : Site) : flip c (S p)=S p.swap := by
    apply axes_inj c; rw [flipAxes,siteAxes hn c p,siteAxes hn c p.swap]; rfl
  have meet {x y} (grid : (gridGraph n n).Adj x y) (hx : reg x) (hy : ¬reg y) :
      ((x=S (0,3) ∨ x=S (3,0)) ∧ (x∈M ↔ x∈F)) ∨ (x∉F ∧ x∉M ∧ y∉F) := by
    let a := axes c x; let b := axes c y
    have nearA : near o a.1 a.2 := hx
    have g := boxAdj c x y grid
    change (a.1=b.1 ∧ (a.2+1=b.2 ∨ b.2+1=a.2)) ∨ (a.2=b.2 ∧ (a.1+1=b.1 ∨ b.1+1=a.1)) at g
    have mx : a.1≤3 ∧ a.2≤3 := by unfold near at nearA; omega
    let p : Site := (⟨a.1,by omega⟩,⟨a.2,by omega⟩)
    let q : Site := (⟨b.1,by omega⟩,⟨b.2,by omega⟩)
    have X : x=S p := axes_inj c (by rw [siteAxes hn c p])
    have Y : y=S q := axes_inj c (by rw [siteAxes hn c q])
    have h := check sep closed p q hx hy (by simpa only [touch,adjacent,Fin.ext_iff] using g)
    have bits (t : Site) := value t
    have V : cell c w m p.2 p.1=(decide (S p.swap∈F)).toNat := bits p.swap
    rw [bits p,V,bits q] at h
    have same : x∈M ↔ S p.swap∈F := by rw [ins x hx,X,flipS]
    rcases h with ⟨pp,eq⟩|⟨px,px',qy⟩
    · left; refine ⟨pp.imp (fun h => X.trans (congrArg S h)) (fun h => X.trans (congrArg S h)),?_⟩
      rw [same,X]; by_cases m1 : S p∈F <;> by_cases m2 : S p.swap∈F <;> simp [m1,m2] at eq ⊢
    · right; rw [same,X,Y]; simpa using And.intro px (And.intro px' qy)
  let B := PitchCut.confined (Bonds F) reg
  let A := PitchCut.confined (Bonds M) reg
  let E : SimpleGraph (GridVertex n n) := (Bonds F) ⊓ Bᶜ
  have split (x y : GridVertex n n) : E.Adj x y ↔ (Bonds F).Adj x y ∧ ¬(reg x ∧ reg y) := by
    change (_ ∧ x≠y ∧ ¬((Bonds F).Adj x y ∧ reg x ∧ reg y)) ↔ _
    constructor
    · rintro ⟨e,_,h⟩; exact ⟨e,fun xy => h ⟨e,xy⟩⟩
    · rintro ⟨e,h⟩; exact ⟨e,e.ne,fun z => h z.2⟩
  have old : B⊔E=Bonds F := by
    ext x y
    change ((Bonds F).Adj x y ∧ reg x ∧ reg y) ∨ E.Adj x y ↔ _
    rw [split]; by_cases h : reg x ∧ reg y <;> simp only [h,and_true,and_false,not_true_eq_false,not_false_eq_true,or_false,false_or]
  have edges {x y} (g : (gridGraph n n).Adj x y) (h : ¬(reg x ∧ reg y)) :
      (x∈M ∨ y∈M) ↔ (x∈F ∨ y∈F) := by
    by_cases hx : reg x <;> by_cases hy : reg y
    · exact False.elim (h ⟨hx,hy⟩)
    · rw [out y hy]; rcases meet g hx hy with hh|hh
      · rw [hh.2]
      · simp [hh.1,hh.2.1]
    · rw [out x hx]; rcases meet g.symm hy hx with hh|hh
      · rw [hh.2]
      · simp [hh.1,hh.2.1]
    · rw [out x hx,out y hy]
  have updated : A⊔E=Bonds M := by
    ext x y
    change ((Bonds M).Adj x y ∧ reg x ∧ reg y) ∨ E.Adj x y ↔ _
    rw [split]; by_cases h : reg x ∧ reg y
    · simp only [h,and_true,and_false,not_true_eq_false,or_false]
    · change (((gridGraph n n).Adj x y ∧ (x∈M ∨ y∈M)) ∧ reg x ∧ reg y) ∨
          (((gridGraph n n).Adj x y ∧ (x∈F ∨ y∈F)) ∧ ¬(reg x ∧ reg y)) ↔
          (gridGraph n n).Adj x y ∧ (x∈M ∨ y∈M)
      by_cases g : (gridGraph n n).Adj x y
      · rw [edges g h]; simp only [h,and_false,false_or,not_false_eq_true,and_true]
      · simp [g]
  let f : A →g B := ⟨flip c, fun {x y} e =>
    ⟨⟨flipAdj c _ _ e.1.1,e.1.2.imp ((ins x e.2.1).mp) ((ins y e.2.2).mp)⟩,
      (flipBox c o x).mpr e.2.1,(flipBox c o y).mpr e.2.2⟩⟩
  rw [←updated]
  letI : LinearOrder (GridVertex n n) := LinearOrder.lift' toLex toLex.injective
  apply flip_two_ports A B E reg (S (0,3)) (S (3,0)) f (Function.LeftInverse.injective (invol c))
    (flipS (0,3)) (flipS (3,0)) (fun _ _ h => h.2.1) _ (old ▸ acy)
  intro x y e
  obtain ⟨bond,missing⟩ := (split x y).mp e
  refine ⟨fun h => missing h.2,fun hx => ?_⟩
  rcases meet bond.1 hx (fun hy => missing ⟨hx,hy⟩) with t|⟨nx,_,ny⟩
  · exact t.1
  · exact False.elim (bond.2.elim nx ny)

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Exchange
