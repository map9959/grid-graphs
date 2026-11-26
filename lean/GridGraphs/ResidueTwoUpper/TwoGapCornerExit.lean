import GridGraphs.ResidueTwoUpper.TwoGapPendant

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Box
open ResidueZero Stencil Words BoundarySix.Connected SimpleGraph

abbrev Site := Fin 5 × Fin 5
def cross (p : Site) := p=(2,2) ∨ p=(1,2) ∨ p=(2,1) ∨ p=(2,3) ∨ p=(3,2)
instance (p : Site) : Decidable (cross p) := by unfold cross; infer_instance
def bd (p : Site) := p.1.val=0 ∨ p.2.val=0
instance (p : Site) : Decidable (bd p) := by unfold bd; infer_instance
def touch (p q : Site) := adjacent 5 5 p q
instance (p q : Site) : Decidable (touch p q) := by unfold touch adjacent; infer_instance

private theorem neighbors {n} (hn : 35≤n) (c : Corner) (p : Site) (hp : cross p)
    (y : GridVertex n n) (adj : (gridGraph n n).Adj (site hn c p.1 p.2) y) :
    ∃ q : Site, touch p q ∧ y=site hn c q.1 q.2 := by
  have lim : 1≤p.1.val ∧ p.1.val≤3 ∧ 1≤p.2.val ∧ p.2.val≤3 := by
    rcases hp with rfl|rfl|rfl|rfl|rfl <;> decide
  let r := loc n c.1 y.1.val; let k := loc n c.2 y.2.val
  have R := y.1.isLt; have K := y.2.isLt
  change adjacent n n _ _ at adj
  simp only [adjacent,site,Fin.ext_iff] at adj
  have key : r<5 ∧ k<5 ∧
      (p.1.val=r ∧ (p.2.val+1=k ∨ k+1=p.2.val) ∨
        p.2.val=k ∧ (p.1.val+1=r ∨ r+1=p.1.val)) ∧
      loc n c.1 r=y.1.val ∧ loc n c.2 k=y.2.val := by
    rcases c with ⟨a,b⟩; cases a <;> cases b <;> dsimp [r,k,loc] at adj ⊢ <;> omega
  exact ⟨(⟨r,key.1⟩,⟨k,key.2.1⟩),by simpa only [touch,adjacent,Fin.ext_iff] using key.2.2.1,
    Prod.ext (Fin.ext key.2.2.2.1.symm) (Fin.ext key.2.2.2.2.symm)⟩

private theorem bd_eq {n} (hn : 35≤n) (c : Corner) (p : Site) :
    IsGridBoundary (site hn c p.1 p.2) ↔ bd p := by
  have R := p.1.isLt; have K := p.2.isLt
  rcases c with ⟨a,b⟩; cases a <;> cases b <;> dsimp [IsGridBoundary,site,loc,bd] <;> omega

def foot (w : Nat) : Site := if w=3 then (2,0) else (0,2)
private theorem gateCheck : ∀ (c : Corner) (m : Fin 512) (b : Bool),
    let w := if b then 3 else 12
    separated c m → ∀ p q : Site, cross p → touch p q →
      (cell c w m p.1 p.2=1 ∨ cell c w m q.1 q.2=1) →
      cross q ∨ q=foot w := by native_decide

/-- The whole open-corner tooth component, after deleting the perimeter,
is contained in the five-site cross. Its only possible physical edge to
the perimeter lands at the surviving foot. -/
theorem open_gate {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (c : Corner)
    (opened : physicalWord (by omega) F c=3 ∨ physicalWord (by omega) F c=12) :
    let hn : 35≤35+42*u := by omega
    let atS := fun p : Site => site hn c p.1 p.2
    let gate := atS (foot (physicalWord hn F c))
    ∀ p : Site, cross p → ∀ y, (Bonds F).Adj (atS p) y →
      (∃ q : Site, cross q ∧ y=atS q) ∨ y=gate := by
  have hn : 35≤35+42*u := by omega
  obtain ⟨P,_,step,_,_,_,good,_⟩ := Frame.frame_of_score u F acy score
  have cm := corners_marked u F acy score
  have value := cell_physical hn F c cm (fun x => (Frame.star_geometry hn F P step x (good (.inl x))).1)
    (fun x => (Frame.star_geometry hn F P step x (good (.inl x))).2.1)
  let m := maskAt F (origin (by omega) c 2 2)
  let w := physicalWord hn F c
  have sep : separated c m := by
    apply decide_eq_true; intro r k h
    have t := open_triangle F acy score two c opened r k h
    have V := value ⟨2+r,by omega⟩ ⟨2+k,by omega⟩
    change cell c w m (2+r.val) (2+k.val)=_ at V
    simp [cell,show ¬(2+r.val=1 ∨ 2+k.val=1) by omega] at V
    rw [V]; split_ifs with z
    · simp [t.mpr z]
    · simp [mt t.mp z]
  dsimp only
  intro p hp y edge
  obtain ⟨q,touch,rfl⟩ := neighbors hn c p hp y edge.1
  have adj : cell c w m p.1 p.2=1 ∨ cell c w m q.1 q.2=1 := by
    rcases edge.2 with mark|mark
    · left; rw [value]; simpa using mark
    · right; rw [value]; simpa using mark
  have ch : cross q ∨ q=foot w := by
    rcases opened with a|a
    · change w=3 at a; rw [a] at adj ⊢; exact gateCheck c m true sep p q hp touch adj
    · change w=12 at a; rw [a] at adj ⊢; exact gateCheck c m false sep p q hp touch adj
  rcases ch with cr|rfl
  · exact Or.inl ⟨q,cr,rfl⟩
  · exact Or.inr rfl

private theorem path_out {V : Type*} {G : SimpleGraph V} {P : V → V}
    (arr : ∀ a b, G.Adj a b → (P a=b ↔ P b≠a))
    {s t : V} (p : G.Walk s t) (simple : p.IsPath) (fix : P t=t) (ne : s≠t) :
    P s=p.snd := by
  have trace {a b : V} (q : G.Walk a b) : q.IsPath → P b=b → a≠b → P a=q.snd := by
    induction q with
    | nil => simp
    | @cons a c b e q ih =>
      intro hp root _
      have nc : P c≠a := by
        by_cases cb : c=b
        · subst b; rw [root]; exact e.ne.symm
        · rw [ih hp.of_cons root cb]
          intro bad
          exact ((Walk.cons_isPath_iff e q).mp hp).2 (bad ▸ q.getVert_mem_support 1)
      simpa using (arr _ _ e).mpr nc
  exact trace p simple fix ne

/-- A witness can be rooted at NW with its exit at none of the eight
candidate surviving feet of an open corner. These are actual positions,
not just exclusions in a normalized or rerooted chart. -/
theorem no_open_foot_of_orientation {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2)
    (P : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u))
    (v : PerimeterVertex (35+42*u)) (fix : P (nw u)=nw u)
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (arr : ∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) (ex : Frame.exitSet P={v}) :
    ∀ c : Corner, let w := physicalWord (by omega) F c
      w=3 ∨ w=12 → v.1≠site (by omega) c (foot w).1 (foot w).2 := by
  classical
  have hn : 35≤35+42*u := by omega
  intro c; dsimp only
  intro op gate
  let w := physicalWord hn F c
  let atS := fun q : Site => site hn c q.1 q.2
  let X := fun y => ∃ p : Site, cross p ∧ y=atS p
  have off : ¬IsGridBoundary (P v.1) := (Finset.mem_filter.mp (show v∈Frame.exitSet P by simp [ex])).2
  have ne : P v.1≠v.1 := fun e => off (by rw [e]; exact v.2)
  have edge := step v.1 ne
  have geom : ∀ (c : Corner) (b : Bool),
      let f := foot (if b then 3 else 12)
      ∀ y : GridVertex (35+42*u) (35+42*u), ¬IsGridBoundary y →
        (gridGraph _ _).Adj (site hn c f.1 f.2) y →
        y=site hn c (if b then 2 else 1) (if b then 1 else 2) := by
    rintro ⟨r,k⟩ b
    cases b <;> cases r <;> cases k <;> dsimp only <;> intro y bd adj <;>
      change adjacent _ _ _ _ at adj <;>
      simp only [adjacent,site,foot,loc,Fin.ext_iff,IsGridBoundary,Prod.ext_iff] at adj bd ⊢ <;> norm_num at adj ⊢ <;>
      have R := y.1.isLt <;> have K := y.2.isLt <;> omega
  have start : X (P v.1) := by
    have e : (gridGraph _ _).Adj (atS (foot w)) (P v.1) := by
      exact Eq.subst (motive:=fun z => (gridGraph _ _).Adj z (P v.1)) gate edge.1
    rcases op with h|h
    · change w=3 at h; rw [h] at e; exact ⟨(2,1),by decide,geom c true _ off e⟩
    · change w=12 at h; rw [h] at e; exact ⟨(1,2),by decide,geom c false _ off e⟩
  obtain ⟨p,hp⟩ := (all_active_reachable u F acy score edge).1.symm.exists_isPath
  have vn : v.1≠nw u := fun e => ne (by rw [e]; exact fix)
  have directed := path_out arr p hp fix vn
  have nowhere (y) (h : X y) : ¬IsGridBoundary y := by
    obtain ⟨q,hq,rfl⟩ := h
    rw [bd_eq]; rcases hq with rfl|rfl|rfl|rfl|rfl <;> decide
  have sealed {x y} (hx : X x) (e : (Bonds F).Adj x y) : X y ∨ y=v.1 := by
    obtain ⟨q,hq,rfl⟩ := hx
    exact (open_gate F acy score two c op q hq y e).imp_right (fun h => h.trans gate.symm)
  have confined {a b} (q : (Bonds F).Walk a b) (ha : X a) (avoid : v.1∉q.support) : X b := by
    induction q with
    | nil => exact ha
    | cons e q ih =>
      have h := sealed ha e
      apply ih (h.resolve_right (fun eq => avoid (by simp [←eq,q.start_mem_support])))
      exact fun h => avoid (by simp [h])
  have confTail {s t} (q : (Bonds F).Walk s t) : s=v.1 → q.IsPath → s≠t → X q.snd → X t := by
    cases q with
    | nil => simp
    | cons e q =>
      rintro rfl path _ first
      rw [Walk.snd_cons] at first
      exact confined q first ((Walk.cons_isPath_iff e q).mp path).2
  exact nowhere _ (confTail p rfl hp vn (directed ▸ start)) (Or.inl rfl)

theorem no_open_foot {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) :
    let n := 35+42*u
    ∃ (P : GridVertex n n → GridVertex n n) (v : PerimeterVertex n),
      Frame.exitSet P={v} ∧ ∀ c : Corner,
      let w := physicalWord (by omega) F c
      w=3 ∨ w=12 → v.1≠site (by omega) c (foot w).1 (foot w).2 := by
  have hn : 35≤35+42*u := by omega
  classical
  obtain ⟨P,fix,step,arr,_,d,wd,zero⟩ := single_defect u F acy score
  have cm := corners_marked u F acy score
  have good := Frame.frame_checked Frame.stars_checked Frame.patches_checked u F P acy step cm
    (fun x => by by_cases e : x=d; exact Or.inr (e ▸ wd); exact Or.inl (zero _ e))
  have split := Frame.gap_split hn F P ⟨nw u,Or.inl rfl⟩ cm
    (fun _ _ e => (all_active_reachable u F acy score e).1) fix step arr good d zero
  obtain ⟨_,v,ex,_⟩ := split.resolve_left (by omega)
  exact ⟨P,v,ex,no_open_foot_of_orientation F acy score two P v fix step arr ex⟩

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Box
