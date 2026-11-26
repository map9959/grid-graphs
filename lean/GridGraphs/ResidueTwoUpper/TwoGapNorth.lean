import GridGraphs.ResidueTwoUpper.TwoGapChartMarks

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North
open ResidueZero Stencil Words BoundarySix.Connected

abbrev Pt := Nat × Nat
def rim (h : Nat) (p : Pt) := p.1=0 ∨ p.2=0 ∨ p.1=h ∨ p.2=h
def short (h : Nat) (p : Pt) := p.1=0 ∧ 2≤p.2 ∨ p.1=1 ∧ p.2=h
def hole (h : Nat) (p : Pt) := (p.1=0 ∧ (p.2=1 ∨ p.2=2)) ∨
  (p.2=h ∧ (p.1=1 ∨ p.1=2)) ∨ (p.1=h ∧ p.2+1=h) ∨ (p.2=0 ∧ p.1+1=h)
def rc {n} (v : GridVertex n n) : Pt := (v.1.val,v.2.val)
theorem rc_inj {n} : Function.Injective (rc (n:=n)) := by
  intro x y h; exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
theorem rim_iff {n} (x : GridVertex n n) : IsGridBoundary x ↔ rim (n-1) (rc x) := by
  have R := x.1.isLt; have K := x.2.isLt; unfold IsGridBoundary rim rc; dsimp; omega

private theorem lit {k x y : Int} (hx : 0≤x ∧ x≤3*k+1) (hy : 0≤y ∧ y≤3*k+1)
    (bd : x=0 ∨ y=0 ∨ x=3*k+1 ∨ y=3*k+1) :
    (rimDatum k 0 x y).1=some (decide (¬((y=0 ∧ (x=1 ∨ x=2)) ∨
      (x=3*k+1 ∧ (y=1 ∨ y=2)) ∨ (y=3*k+1 ∧ x+1=3*k+1) ∨ (x=0 ∧ y+1=3*k+1)))) := by
  have small (z i : Int) (h : 0 ≤ i ∧ i≤2) : clip z=i ↔ z=i := by unfold clip; omega
  have nn (z : Int) (h : 0≤z) : 0≤clip z := by unfold clip; omega
  have pos : ¬min (min (clip y) (clip (3*k+1-y))) (min (clip x) (clip (3*k+1-x)))<0 := by
    have := nn _ hx.1; have := nn _ hy.1; have := nn (3*k+1-y) (by omega); have := nn (3*k+1-x) (by omega); omega
  unfold rimDatum; dsimp only; rw [if_neg pos]
  simp only [small _ 0 (by decide),small _ 1 (by decide),small _ 2 (by decide)]
  rw [if_pos (by omega)]; congr 2; apply propext; omega

theorem marked_iff {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by omega) F)=code4 0 0 1 1)
    (x : GridVertex (35+42*u) (35+42*u)) (bd : IsGridBoundary x) :
    x∈F ↔ ¬hole (34+42*u) (rc x) := by
  have R := x.1.isLt; have K := x.2.isLt
  unfold IsGridBoundary at bd
  have h := lit (k:=11+14*(u:Int)) (x:=x.2.val) (y:=x.1.val) (by omega) (by omega) (by omega)
  have val := chart_marks F acy score canon x 0 _ h
  rw [decide_eq_decide] at val
  unfold hole rc; dsimp; exact val.trans (by omega)

-- The long path leads to NW. The short path runs east along the top
-- and then one step south at NE; its sink within the path is column d.
def parent (h d : Nat) (p : Pt) : Pt :=
  if p.1=0 then
    if p.2=0 then p else if p.2=1 then (0,0) else
    if p.2<d then (0,p.2+1) else if d<p.2 then (0,p.2-1) else (1,d)
  else if p.2=0 then (p.1-1,0) else if p.1=h then (h,p.2-1)
  else if p.1=1 then (0,h) else (p.1+1,h)
def level (h d : Nat) (p : Pt) :=
  if p.1=0 then (if p.2≤1 then p.2 else p.2-d+(d-p.2))
  else if p.2=0 then p.1 else if p.1=h then h+p.2
  else if p.1=1 then h-d+1 else 3*h-p.1
def edge (a b : Pt) :=
  a.1=b.1 ∧ (a.2+1=b.2 ∨ b.2+1=a.2) ∨ a.2=b.2 ∧ (a.1+1=b.1 ∨ b.1+1=a.1)
set_option maxHeartbeats 400000 in
private theorem descent {h d : Nat} (hh : 34≤h) (hd : 3≤d ∧ d<h)
    (p : Pt) (inside : p.1≤h ∧ p.2≤h) (bd : rim h p) (nr : p≠(0,0)) (nd : p≠(0,d)) :
    let q := parent h d p
    q.1≤h ∧ q.2≤h ∧ rim h q ∧ edge p q ∧ (¬hole h p ∨ ¬hole h q) ∧
    level h d q<level h d p ∧ (short h q ↔ short h p) := by
  rcases p with ⟨r,c⟩
  dsimp [parent]; change ¬(r,c)=(0,0) at nr; change ¬(r,c)=(0,d) at nd; simp only [Prod.mk.injEq] at nr nd
  unfold rim at bd; dsimp at bd inside
  split_ifs <;> dsimp [rim,edge,hole,short,level] <;> split_ifs <;> norm_num <;> omega

/-- Along either path all arrows point toward its specified end or exit.
The long-path conclusion alone requires no information on the exit. -/
theorem orient {n d : Nat} (hn : 35≤n) (hd : 3≤d ∧ d<n-1)
    (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (marks : ∀ x, IsGridBoundary x → (x∈F ↔ ¬hole (n-1) (rc x)))
    (arr : ∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x))
    (fix : ∀ x, rc x=(0,0) → P x=x)
    (x : GridVertex n n) (bd : IsGridBoundary x)
    (exit : short (n-1) (rc x) → ∀ y, rc y=(0,d) → rc (P y)=(1,d)) :
    rc (P x)=parent (n-1) d (rc x) := by
  let H := n-1
  let lev (v : GridVertex n n) := level H d (rc v)
  change rc (P x)=parent H d (rc x)
  induction heq : lev x using Nat.strong_induction_on generalizing x with
  | h l ih =>
    by_cases root : rc x=(0,0)
    · rw [fix x root,root]; rfl
    by_cases stop : rc x=(0,d)
    · have atExit := exit (by rw [stop]; unfold short; dsimp; omega) x stop
      rw [atExit,stop]; simp [parent,show d≠0 by omega,show d≠1 by omega]
    have bounded (v : GridVertex n n) : (rc v).1≤H ∧ (rc v).2≤H := by
      have R := v.1.isLt; have C := v.2.isLt; dsimp [H,rc]; omega
    let q := parent H d (rc x)
    obtain ⟨r,c,b,g,mark,lt,st⟩ := descent (h:=H) (by dsimp [H]; omega) hd (rc x) (bounded x) ((rim_iff x).mp bd) root stop
    let y : GridVertex n n := (⟨q.1,by dsimp [H,q] at *; omega⟩,⟨q.2,by dsimp [H,q] at *; omega⟩)
    have eq : rc y=q := rfl
    have by' : IsGridBoundary y := (rim_iff _).mpr b
    have grid : (gridGraph n n).Adj x y := by
      change adjacent _ _ _ _; simpa only [adjacent,Fin.ext_iff,edge,rc,y,q] using g
    have bond : (Bonds F).Adj x y := ⟨grid,mark.imp (marks x bd).mpr (marks y by').mpr⟩
    have low : lev y<l := by rw [←heq]; exact lt
    have par := ih (lev y) low y by' (fun hs => exit (st.mp hs)) rfl
    have ne : P y≠x := by
      intro bad
      by_cases r0 : rc y=(0,0)
      · exact grid.ne (bad ▸ fix y r0)
      by_cases s0 : rc y=(0,d)
      · have active : short H (rc x) := st.mp (show short H (rc y) by rw [s0]; unfold short; dsimp; omega)
        have off := exit active y s0
        rw [bad] at off; rw [off] at active
        unfold short at active; dsimp [H] at active; omega
      have down := (descent (h:=H) (by dsimp [H]; omega) hd (rc y) (bounded y) b r0 s0).2.2.2.2.2.1
      rw [←par,bad] at down
      change lev x<lev y at down; omega
    rw [(arr _ _ bond).mpr ne]; exact eq

structure Chart {u : Nat} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (P : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u)) (d : Nat) : Prop where
  ordinary : 3≤d ∧ d<34+42*u ∧ d≠32+42*u
  step : ∀ x, P x≠x → (Bonds F).Adj x (P x)
  arrows : ∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)
  perimeter : ∀ x, IsGridBoundary x → rc (P x)=parent (34+42*u) d (rc x)
  sole : ∃ v, rc v=(0,d) ∧ starSlack F P v=full ∧
    ∀ a : occurrence (35+42*u), a≠.inl v → weightAt F P a=0

theorem chart_of_0011 {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (canon : packed (signature (by omega) F)=code4 0 0 1 1) :
    ∃ P d, Chart F P d := by
  classical
  let n := 35+42*u; let H := 34+42*u
  have hn : 35≤n := by dsimp [n]; omega
  have Hn : n-1=H := by dsimp [H,n]; omega
  obtain ⟨P,fix,step,arr,_,a,wa,z⟩ := single_defect u F acy score
  have cm := corners_marked u F acy score
  have good := Frame.frame_checked Frame.stars_checked Frame.patches_checked u F P acy step cm
    (fun x => by by_cases e : x=a; exact Or.inr (e ▸ wa); exact Or.inl (z _ e))
  have split := Frame.gap_split hn F P ⟨nw u,Or.inl rfl⟩ cm
    (fun _ _ e => (all_active_reachable u F acy score e).1) fix step arr good a z
  obtain ⟨_,v,ex,rfl⟩ := split.resolve_left (by omega)
  let x := v.1; let y := P x
  have marks (t : GridVertex n n) (b : IsGridBoundary t) : t∈F ↔ ¬hole (n-1) (rc t) := by
    rw [Hn]; exact marked_iff F acy score canon t b
  have root (t : GridVertex n n) (h : rc t=(0,0)) : P t=t := by
    have eq : t=nw u := rc_inj h; exact eq ▸ fix
  have off : ¬IsGridBoundary y := (Finset.mem_filter.mp (show v∈Frame.exitSet P by simp [ex])).2
  have xy : (Bonds F).Adj x y := step x (fun h => off (by change IsGridBoundary (P x); rw [h]; exact v.2))
  have un : y∉F := (Frame.star_geometry hn F P step y (good _)).2.1
    ((Frame.inward_iff_off hn x y xy.1 v.2).mp off)
  have marked := (marks x v.2).mp (xy.2.resolve_right un)
  have go : short H (rc x) := by
    by_contra no
    have no' : ¬short (n-1) (rc x) := Hn ▸ no
    have pe := orient (d:=3) hn (by dsimp [n]; omega) F P marks arr root x v.2 (fun h => (no' h).elim)
    by_cases r : rc x=(0,0)
    · exact off (by change IsGridBoundary (P x); rw [root x r]; exact v.2)
    · have st : rc x≠(0,3) := by intro eq; apply no; rw [eq]; exact Or.inl ⟨rfl,by decide⟩
      have h := descent (h:=n-1) (d:=3) (by omega) (by omega) (rc x)
        (by have := x.1.isLt; have := x.2.isLt; dsimp [rc]; omega)
        ((rim_iff _).mp v.2) r st
      exact off ((rim_iff _).mpr (pe ▸ h.2.2.1))
  have grid := xy.1
  change adjacent _ _ x y at grid
  simp only [adjacent,Fin.ext_iff] at grid
  have X := x.1.isLt; have K := x.2.isLt; have Y := y.1.isLt; have C := y.2.isLt
  change x.1.val<n at X; change x.2.val<n at K; change y.1.val<n at Y; change y.2.val<n at C
  have o := off; unfold IsGridBoundary at o
  unfold short rc at go; unfold hole rc at marked
  dsimp only at go marked
  let d := x.2.val
  have location : rc x=(0,d) := by dsimp [rc,d]; congr 1; dsimp [H,n] at *; omega
  have head : rc y=(1,d) := by simp only [rc,d,Prod.mk.injEq]; dsimp [rc,d] at location; dsimp [n,H] at *; omega
  have bounds : 3≤d ∧ d<n-1 := by dsimp [d,n,H] at *; omega
  have wordNE : physicalWord hn F (false,true)=12 := by
    have valid := physicalWord_ok hn F P good (false,true)
    have dec : ∀ w : Fin 4 → Fin 4, packed w=code4 0 0 1 1 → w 1=0 := by native_decide
    have h := dec _ canon; change digit hn F (false,true)=0 at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at valid
    rcases valid with eq|eq|eq|eq <;> first | exact eq | simp [digit,eq] at h
  have foot := Box.no_open_foot_of_orientation F acy score two P v fix step arr ex (false,true) (Or.inr wordNE)
  rw [wordNE] at foot
  have dist : d≠32+42*u := by
    intro eq; apply foot; apply rc_inj; change rc x=_
    rw [location]; dsimp [Box.foot,Box.site,loc,rc]; congr 1; omega
  refine ⟨P,d,⟨⟨bounds.1,by change d<H; rw [←Hn]; exact bounds.2,dist⟩,step,arr,?_,⟨x,location,wa,z⟩⟩⟩
  intro t ht
  change rc (P t)=parent H d (rc t); rw [←Hn]
  apply orient hn bounds F P marks arr root t ht
  intro _ s hs; have eq : s=x := rc_inj (hs.trans location.symm)
  exact eq ▸ head

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North
