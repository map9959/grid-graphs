import GridGraphs.ResidueTwoUpper.TwoGapFrontierEdges

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open SimpleGraph Finset ResidueZero Stencil

variable {u : Nat}
structure StepWindow (u l t : Nat) : Prop where
  lo : 3≤l
  hi : l+8+3≤high u
  time : t+1<high u

private theorem valid {l t} (W : StepWindow u l t) : l+8<Size u ∧ t+1<Size u := by
  obtain ⟨a,b,c⟩ := W; dsimp [high,Size] at *; omega

private theorem boxRow {l t r} (W : StepWindow u l t) (hr : r≤t+1) (i : Fin 9) :
    prefixBox l (t+1) (rowSite u l r i) ↔ 1≤r := by
  have rc := row_rc l r (by have := (valid W).2; omega) (valid W).1 i
  have := congrArg Prod.fst rc; have := congrArg Prod.snd rc
  dsimp [North.rc] at *
  unfold prefixBox; omega

private theorem interior {l t} (W : StepWindow u l t) {x : Board u} (box : prefixBox l (t+1) x) :
    ¬IsGridBoundary x := by
  obtain ⟨a,b,c⟩ := W; unfold prefixBox high at *
  change ¬(_=0 ∨ _+1=35+42*u ∨ _=0 ∨ _+1=35+42*u); omega

private theorem coords {l t r} (W : StepWindow u l t) (hr : r≤t+1) (i : Fin 9) :
    (rowSite u l r i).1.val=r ∧ (rowSite u l r i).2.val=l+i.val := by
  have h := row_rc l r (by have := (valid W).2; omega) (valid W).1 i
  exact Prod.mk.inj h

private theorem posHoriz {l t} (i : Fin 9) (hi : 0 < i.val) :
    rowPort u l t (directed i 1).1=rowSite u l (t+1) (prev i) := by
  have e : (directed i 1).1=newSlot (prev i) := Fin.ext (by change 9+i.val=10+(i.val-1); omega)
  rw [e,newPort]

private theorem grid_rc {v w : Board u} :
    (gridGraph (Size u) (Size u)).Adj v w ↔ North.edge (North.rc v) (North.rc w) := by
  change adjacent _ _ _ _ ↔ _
  simp [adjacent,North.edge,North.rc,Fin.ext_iff]

private theorem new_not_old {l t d} (F : Finset (Board u)) (W : StepWindow u l t)
    (i : Fin 9) (v : Board u) : ¬(built F d l t).Adj (rowSite u l (t+1) i) v := by
  rw [←newPort]; exact row_iso F d l t (valid W).1 (valid W).2 i v

theorem insertion_sound {l t d} (F : Finset (Board u)) (W : StepWindow u l t)
    (e : Pair) (mem : e∈insertions F d l t) :
    let p := rowPort u l t
    (built F d l (t+1)).Adj (p e.1) (p e.2) ∧ ¬(built F d l t).Adj (p e.1) (p e.2) := by
  obtain ⟨i,k,en,rfl⟩ := (row_mem ..).mp mem
  have y := coords W (r:=t+1) le_rfl i
  have iy := (boxRow W le_rfl i).mpr (Nat.succ_pos _)
  have ny := interior W iy
  fin_cases k
  · obtain ⟨nn,marks⟩ := (enabled0 F d l t i).mp en
    have x := coords W (r:=t) (by omega) i
    have ix := (boxRow W (r:=t) (by omega) i).mpr (by omega)
    dsimp only
    change (built F d l (t+1)).Adj (rowPort u l t ⟨i.val,_⟩) (rowPort u l t (newSlot i)) ∧
      ¬(built F d l t).Adj (rowPort u l t ⟨i.val,_⟩) (rowPort u l t (newSlot i))
    rw [oldPort,newPort]
    constructor
    · exact built_adj.mpr (.inl ⟨⟨grid_rc.mpr (Or.inr ⟨x.2.trans y.2.symm,Or.inl (by dsimp [North.rc]; omega)⟩),marks⟩,
        interior W ix,ny,ix,iy⟩)
    · exact fun h => new_not_old F W i _ h.symm
  · obtain ⟨nn,marks⟩ := (enabled1 F d l t i).mp en
    have x := coords W (r:=t+1) le_rfl (prev i)
    have ix := (boxRow W le_rfl (prev i)).mpr (Nat.succ_pos _)
    dsimp only
    have ph := posHoriz (u:=u) (l:=l) (t:=t) i nn
    change rowPort u l t ⟨9+i.val,by omega⟩=_ at ph
    change (built F d l (t+1)).Adj (rowPort u l t ⟨9+i.val,_⟩) (rowPort u l t (newSlot i)) ∧
      ¬(built F d l t).Adj (rowPort u l t ⟨9+i.val,_⟩) (rowPort u l t (newSlot i))
    rw [ph,newPort]
    constructor
    · exact built_adj.mpr (.inl ⟨⟨grid_rc.mpr (Or.inl ⟨x.1.trans y.1.symm,Or.inl (by dsimp [North.rc,prev] at *; omega)⟩),marks⟩,
        interior W ix,ny,ix,iy⟩)
    · exact new_not_old F W _ _
  · obtain ⟨mark,phase⟩ := (enabled2 F d l t i).mp en
    change (built F d l (t+1)).Adj (rowPort u l t (newSlot i)) (rowPort u l t 9) ∧
      ¬(built F d l t).Adj (rowPort u l t (newSlot i)) (rowPort u l t 9)
    rw [newPort,centerPort]
    have pin : rowSite u l (t+1) i∈pinSet F d := by
      apply mem_filter.mpr
      have := W.lo; have := W.hi
      exact ⟨mark,by omega,by omega,by omega⟩
    exact ⟨built_adj.mpr (.inr (.inr ⟨rfl,pin,iy,fun h => ny (h ▸ (show IsGridBoundary (nw u) from Or.inl rfl))⟩)),
      new_not_old F W _ _⟩

theorem built_monotone {l t d} (F : Finset (Board u)) : built F d l t ≤ built F d l (t+1) := by
  intro x y e
  have inc {x : Board u} (h : prefixBox l t x) : prefixBox l (t+1) x :=
    ⟨h.1,h.2.1.trans (Nat.le_succ _),h.2.2⟩
  rw [built_adj] at e ⊢
  rcases e with ⟨a,b,c,ix,iy⟩|⟨rfl,p,i,n⟩|⟨rfl,p,i,n⟩
  · exact .inl ⟨a,b,c,inc ix,inc iy⟩
  · exact .inr (.inl ⟨rfl,p,inc i,n⟩)
  · exact .inr (.inr ⟨rfl,p,inc i,n⟩)

private theorem row_eq {l t} (W : StepWindow u l t) {x : Board u} (ix : prefixBox l (t+1) x) :
    ∃ i : Fin 9, rowSite u l x.1.val i=x := by
  let i : Fin 9 := ⟨x.2.val-l,by unfold prefixBox at ix; omega⟩
  refine ⟨i,North.rc_inj ?_⟩
  rw [row_rc _ _ x.1.isLt (valid W).1]; apply Prod.ext <;> dsimp [North.rc,i] <;> unfold prefixBox at ix <;> omega

theorem insertion_complete {l t d} (F : Finset (Board u)) (W : StepWindow u l t)
    {x y} (h : (built F d l (t+1)).Adj x y) (new : ¬(built F d l t).Adj x y) :
    ∃ e∈insertions F d l t, (x=rowPort u l t e.1 ∧ y=rowPort u l t e.2) ∨
      (y=rowPort u l t e.1 ∧ x=rowPort u l t e.2) := by
  let p := rowPort u l t
  let hit (x y : Board u) := ∃ e∈insertions F d l t, x=p e.1 ∧ y=p e.2
  have pay {x y : Board u} (j : Fin 9) (k : Fin 3)
      (en : enabled (previous F l t) (wordRow F l (t+1)) (pinMask (u:=u) d l (t+1)) j k)
      (a : x=p (directed j k).1) (b : y=p (directed j k).2) : hit x y :=
    ⟨_,(row_mem ..).mpr ⟨j,k,en,rfl⟩,a,b⟩
  have pin {z : Board u} (iz : prefixBox l (t+1) z) (pz : z∈pinSet F d) (nn : z.1.val=t+1) :
      hit z (nw u) := by
    obtain ⟨j,eq⟩ := row_eq W iz; rw [nn] at eq
    obtain ⟨mz,_,_,s⟩ := mem_filter.mp pz
    have cc := (coords W (r:=t+1) le_rfl j).2; rw [eq] at cc
    exact pay j 2 ((enabled2 ..).mpr ⟨eq ▸ mz,by omega⟩) ((newPort ..).trans eq).symm rfl
  have ordinary {a b : Board u} (ia : prefixBox l (t+1) a) (ib : prefixBox l (t+1) b)
      (ab : (Bonds F).Adj a b) (ar : a.1.val≤b.1.val) (br : b.1.val=t+1)
      (lr : a.1.val=b.1.val → a.2.val<b.2.val) : hit a b := by
    obtain ⟨j,eq⟩ := row_eq W ib; rw [br] at eq
    have cc := (coords W (r:=t+1) le_rfl j).2; rw [eq] at cc
    have adj := grid_rc.mp ab.1
    simp only [North.edge,North.rc] at adj
    by_cases same : a.1.val=b.1.val
    · have pos : 0 < j.val := by specialize lr same; unfold prefixBox at ia; omega
      have ex := coords W (r:=t+1) le_rfl (prev j)
      have ea : rowSite u l (t+1) (prev j)=a := by
        apply Prod.ext <;> apply Fin.ext
        · exact ex.1.trans (same.trans br).symm
        · rw [ex.2]; change l+(j.val-1)=a.2.val; have := lr same; omega
      exact pay j 1 ((enabled1 ..).mpr ⟨pos,by rw [ea,eq]; exact ab.2⟩)
        ((posHoriz j pos).trans ea).symm ((newPort ..).trans eq).symm
    · have ex := coords W (r:=t) (by omega) j
      have ea : rowSite u l t j=a := by apply Prod.ext <;> apply Fin.ext <;> omega
      exact pay j 0 ((enabled0 ..).mpr ⟨by have := ia.1; omega,by rw [ea,eq]; exact ab.2⟩)
        ((oldPort ..).trans ea).symm ((newPort ..).trans eq).symm
  suffices yes : hit x y ∨ hit y x by
    rcases yes with ⟨e,m,h⟩|⟨e,m,h⟩
    · exact ⟨e,m,.inl h⟩
    · exact ⟨e,m,.inr h⟩
  have prevB {z : Board u} (iz : prefixBox l (t+1) z) (no : z.1.val≠t+1) : prefixBox l t z :=
    ⟨iz.1,by have := iz.2.1; omega,iz.2.2⟩
  rcases built_adj.mp h with ⟨ab,na,nb,ia,ib⟩|⟨rfl,pz,iz,ne⟩|⟨rfl,pz,iz,ne⟩
  · have top : x.1.val=t+1 ∨ y.1.val=t+1 := by
      by_contra! n
      exact new (built_adj.mpr (.inl ⟨ab,na,nb,prevB ia n.1,prevB ib n.2⟩))
    have near := grid_rc.mp ab.1
    simp only [North.edge,North.rc] at near
    have rx := ia.2.1; have ry := ib.2.1
    by_cases dir : x.1.val<y.1.val ∨ (x.1.val=y.1.val ∧ x.2.val<y.2.val)
    · exact .inl (ordinary ia ib ab (by omega) (by omega) (by omega))
    · exact .inr (ordinary ib ia ab.symm (by omega) (by omega) (by omega))
  · exact .inr (pin iz pz (by by_contra no; exact new (built_adj.mpr (.inr (.inl ⟨rfl,pz,prevB iz no,ne⟩)))))
  · exact .inl (pin iz pz (by by_contra no; exact new (built_adj.mpr (.inr (.inr ⟨rfl,pz,prevB iz no,ne⟩)))))

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
