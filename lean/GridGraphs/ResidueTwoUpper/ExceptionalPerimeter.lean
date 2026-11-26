import GridGraphs.ResidueTwoUpper.ExceptionalFrame
import GridGraphs.Accounting.BoundarySix.Connected.PerimeterLedger

/-! Physical exits count omitted perimeter edges. This ledger counts each
undirected forced perimeter edge exactly once, by its actual outgoing end. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.Frame
open ResidueZero Stencil Finset SimpleGraph BoundarySix.Connected
open scoped Sym2

theorem boundary_iff {n} (v : GridVertex n n) : IsGridBoundary v ↔ depthAt n (coord v)=0 := by
  have a := v.1.isLt; have b := v.2.isLt; unfold depthAt depth IsGridBoundary; dsimp [coord]; omega

theorem inward_iff_off {n} (hn : 35≤n) (v w : GridVertex n n) (adj : (gridGraph n n).Adj v w)
    (bd : IsGridBoundary v) : ¬IsGridBoundary w ↔ depthAt n (coord w)=1 := by
  have a := v.1.isLt; have b := v.2.isLt; have c := w.1.isLt; have f := w.2.isLt
  unfold IsGridBoundary at bd ⊢; change adjacent n n _ _ at adj
  simp only [adjacent,Fin.ext_iff] at adj
  unfold depthAt depth; dsimp [coord]; rcases adj with ⟨x,y|y⟩|⟨x,y|y⟩ <;> omega

noncomputable def exitSet {n} (P : GridVertex n n → GridVertex n n) : Finset (PerimeterVertex n) := by
  classical
  exact univ.filter fun v => ¬IsGridBoundary (P v.1)

theorem perimeter_ledger {n} (hn : 35≤n) (F : Finset (GridVertex n n))
    (P : GridVertex n n → GridVertex n n) (root : PerimeterVertex n)
    (sink : P root.1=root.1) (only : ∀ v : PerimeterVertex n, P v.1=v.1 → v=root)
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (arrows : ∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) :
    (perimeterHoles F).card=1+(exitSet P).card := by
  classical
  let G := perimeterGraph n
  let H := forcedEdgeGraph G (↑(perimeterSelected F) : Set _)
  let tang := univ.filter fun v : PerimeterVertex n => P v.1≠v.1 ∧ IsGridBoundary (P v.1)
  have edge_of {x y : PerimeterVertex n} : H.Adj x y ↔ (Bonds F).Adj x.1 y.1 := by
    change ((gridGraph n n).Adj x.1 y.1 ∧ (x∈perimeterSelected F ∨ y∈perimeterSelected F)) ↔ _
    simp only [mem_perimeterSelected]; rfl
  let target (v : PerimeterVertex n) (h : v∈tang) : PerimeterVertex n :=
    ⟨P v.1,(mem_filter.mp h).2.2⟩
  have count : tang.card=H.edgeFinset.card := by
    apply card_bij (fun v h => s(v,target v h))
    · intro v h; exact mem_edgeFinset.mpr (edge_of.mpr (step v.1 (mem_filter.mp h).2.1))
    · intro v hv w hw eq
      rcases Sym2.eq_iff.mp eq with eq|⟨a,b⟩
      · exact eq.1
      · have av : P w.1=v.1 := (congrArg Subtype.val a).symm
        have bv : P v.1=w.1 := congrArg Subtype.val b
        exact False.elim (((arrows _ _ (bv ▸ step v.1 (mem_filter.mp hv).2.1)).mp bv) av)
    · intro e he; induction e using Sym2.inductionOn with
      | _ v w =>
        have adj := edge_of.mp (mem_edgeFinset.mp he)
        by_cases vw : P v.1=w.1
        · have m : v∈tang := mem_filter.mpr ⟨mem_univ _,vw ▸ adj.ne.symm,vw ▸ w.2⟩
          exact ⟨v,m,congrArg (s(v,·)) (Subtype.ext vw)⟩
        · have wv : P w.1=v.1 := by by_contra no; exact vw ((arrows _ _ adj).mpr no)
          have m : w∈tang := mem_filter.mpr ⟨mem_univ _,wv ▸ adj.ne,wv ▸ v.2⟩
          exact ⟨w,m,(congrArg (s(w,·)) (Subtype.ext wv)).trans (Sym2.eq_swap ..)⟩
  have deg := G.sum_degrees_eq_twice_card_edges
  have eqDegree (v : PerimeterVertex n) : G.degree v=2 := perimeter_degree (by omega) _
  simp only [eqDegree,sum_const,card_univ,nsmul_eq_mul] at deg
  change Fintype.card (PerimeterVertex n)*2=2*G.edgeFinset.card at deg
  have holes := card_sdiff_add_card_eq_card (edgeFinset_mono (forcedEdgeGraph_le G (↑(perimeterSelected F) : Set _)))
  change (perimeterHoles F).card+H.edgeFinset.card=G.edgeFinset.card at holes
  let all := (univ : Finset (PerimeterVertex n))
  have partition := card_filter_add_card_filter_not (s:=all) (p:=fun v => IsGridBoundary (P v.1))
  have fixed := card_filter_add_card_filter_not (s:=all.filter fun v => IsGridBoundary (P v.1))
    (p:=fun v => P v.1=v.1)
  have one : ((all.filter fun v => IsGridBoundary (P v.1)).filter fun v => P v.1=v.1)={root} := by
    ext v; simp only [all,mem_filter,mem_univ,true_and,mem_singleton]
    constructor
    · intro h; exact only _ h.2
    · rintro rfl; exact ⟨by rw [sink]; exact v.2,sink⟩
  have kept : ((all.filter fun v => IsGridBoundary (P v.1)).filter fun v => ¬P v.1=v.1)=tang := by
    ext; simp [tang,all,and_comm]
  rw [one,kept,card_singleton] at fixed
  change _+(exitSet P).card=univ.card at partition
  rw [card_univ] at partition
  rw [←fixed,count] at partition
  rw [←holes] at deg
  omega

theorem isolated_fixed {V : Type*} {G : SimpleGraph V} (P : V → V)
    (arr : ∀ a b, G.Adj a b → (P a=b ↔ P b≠a)) {r x : V} (root : P r=r)
    (reach : G.Reachable r x) (fixed : P x=x) : r=x := by
  obtain ⟨p,hp⟩ := reach.exists_isPath
  have walk {a b : V} (q : G.Walk a b) :
      q.IsPath → (∀ c, G.Adj a c → c∈q.support → P a≠c) → P b=b → a=b := by
    induction q with
    | nil => simp
    | @cons a c b ac tail ih =>
      intro path start endFix
      have par : P c=a := by
        by_contra no
        exact start c ac (by simp [tail.start_mem_support]) ((arr _ _ ac).mpr no)
      have eq := ih path.of_cons (by
        intro z _ mem bad
        have za : z=a := bad.symm.trans par
        exact (Walk.cons_isPath_iff ac tail).mp path |>.2 (za ▸ mem)) endFix
      subst b
      exact False.elim (ac.ne (par.symm.trans endFix))
  exact walk p hp (fun _ e _ => by rw [root]; exact e.ne) fixed

/-- Any noncorner boundary point is marked or touches a marked boundary
point. This also excludes a second sink at a perimeter hole. -/
theorem perimeter_attached {n} (hn : 35≤n) (F : Finset (GridVertex n n))
    (corners : ∀ x, isCorner x → x∈F) (line : ∀ x, straight n (coord x) → x∈F)
    (v : PerimeterVertex n) : v.1∈F ∨ ∃ w∈F, (Bonds F).Adj v.1 w := by
  by_cases mem : v.1∈F
  · exact Or.inl mem
  right
  have side (i : Fin n) (place : Fin n → GridVertex n n) (vEq : v.1=place i)
      (beg : isCorner (place ⟨0,by omega⟩)) (end' : isCorner (place ⟨n-1,by omega⟩))
      (middle : ∀ j : Fin n, 3≤j.val → j.val+4≤n → straight n (coord (place j)))
      (edge : ∀ a b : Fin n, a.val+1=b.val ∨ b.val+1=a.val → (gridGraph n n).Adj (place a) (place b)) :
      ∃ w∈F, (Bonds F).Adj v.1 w := by
    have hi := i.isLt
    have get (j : Fin n) (jm : place j∈F) (adj : i.val+1=j.val ∨ j.val+1=i.val) :
        ∃ w∈F, (Bonds F).Adj v.1 w :=
      ⟨place j,jm,vEq ▸ ⟨edge i j adj,Or.inr jm⟩⟩
    have excl (j : Fin n) (jm : place j∈F) : i.val≠j.val := by
      intro eq; exact mem (vEq ▸ (Fin.ext eq ▸ jm))
    have lo := excl ⟨0,by omega⟩ (corners _ beg)
    have far := excl ⟨n-1,by omega⟩ (corners _ end')
    have mid : ¬(3 ≤ i.val ∧ i.val+4≤n) :=
      fun ⟨a,b⟩ => mem (vEq ▸ line _ (middle i a b))
    dsimp only at lo far
    rcases (show i.val=1 ∨ i.val=2 ∨ i.val+2=n ∨ i.val+3=n by omega) with a|a|a|a
    · exact get ⟨0,by omega⟩ (corners _ beg) (by simp; omega)
    · exact get ⟨3,by omega⟩ (line _ (middle _ (by rfl) (by dsimp; omega))) (by dsimp; omega)
    · exact get ⟨n-1,by omega⟩ (corners _ end') (by dsimp; omega)
    · exact get ⟨n-4,by omega⟩ (line _ (middle _ (by dsimp; omega) (by dsimp; omega))) (by dsimp; omega)
  have b := v.2
  obtain ⟨⟨r,c⟩,vb⟩ := v
  rcases b with br|br|bc|bc
  case' inl => apply side c (fun j => (r,j)) rfl
  case' inr.inl => apply side c (fun j => (r,j)) rfl
  case' inr.inr.inl => apply side r (fun j => (j,c)) rfl
  case' inr.inr.inr => apply side r (fun j => (j,c)) rfl
  all_goals dsimp only at *
  all_goals first
    | solve | simp [isCorner]; omega
    | solve | intro j lo hi; unfold straight depthAt depth; dsimp [coord]; omega
    | solve | intro a b h; change adjacent n n _ _; simp [adjacent,h]

/-- One missing perimeter edge if there is no exit; otherwise precisely two,
and the sole full occurrence is the star at the unique exit. -/
theorem gap_split {n} (hn : 35≤n) (F : Finset (GridVertex n n))
    (P : GridVertex n n → GridVertex n n) (root : PerimeterVertex n)
    (corners : ∀ x, isCorner x → x∈F)
    (reach : ∀ x y, (Bonds F).Adj x y → (Bonds F).Reachable root.1 x)
    (sink : P root.1=root.1) (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (arr : ∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x))
    (good : ∀ x, allGood F P x) (d : occurrence n) (zero : ∀ x, x≠d → weightAt F P x=0) :
    ((perimeterHoles F).card=1 ∧ exitSet P=∅) ∨
    ((perimeterHoles F).card=2 ∧ ∃ v : PerimeterVertex n, exitSet P={v} ∧ d=Sum.inl v.1) := by
  classical
  have geo (v : GridVertex n n) := star_geometry hn F P step v (good (.inl v))
  have only (v : PerimeterVertex n) (fix : P v.1=v.1) : v=root := by
    obtain mark|⟨w,_,adj⟩ := perimeter_attached hn F corners (fun x => (geo x).1) v
    · let r := v.1.1
      let s : Fin n := if r.val=0 then ⟨1,by omega⟩ else ⟨r.val-1,by have := r.isLt; omega⟩
      have e : (gridGraph n n).Adj v.1 (s,v.1.2) := by
        change adjacent _ _ _ _; simp [adjacent,s,r]; split_ifs <;> dsimp <;> omega
      exact Subtype.ext (isolated_fixed P arr sink (reach _ _ ⟨e,Or.inl mark⟩) fix).symm
    · exact Subtype.ext (isolated_fixed P arr sink (reach _ _ adj) fix).symm
  have ledger := perimeter_ledger hn F P root sink only step arr
  have charge (v : PerimeterVertex n) (h : v∈exitSet P) : Sum.inl v.1=d := by
    have off := (mem_filter.mp h).2
    have ne : P v.1≠v.1 := fun eq => off (by rw [eq]; exact v.2)
    have bd := (boundary_iff _).mp v.2
    have w := ((geo v.1).2.2.1 bd).mpr ⟨bd,(inward_iff_off hn _ _ (step _ ne).1 v.2).mp off⟩
    by_contra no
    have z := zero _ no; change starSlack F P v.1=0 at z; rw [z] at w; exact (by decide : (0:Int)≠full) w
  by_cases ex : (exitSet P).Nonempty
  · obtain ⟨v,h⟩ := ex
    have eq : exitSet P={v} := by
      ext x; rw [mem_singleton]; exact ⟨fun hx => Subtype.ext (Sum.inl.inj ((charge x hx).trans (charge v h).symm)), fun eq => eq ▸ h⟩
    exact Or.inr ⟨by simpa [eq] using ledger,v,eq,(charge v h).symm⟩
  · have eq := not_nonempty_iff_eq_empty.mp ex
    exact Or.inl ⟨by simpa [eq] using ledger,eq⟩

end GridGraphs.ResidueTwoUpper.Exceptional.Frame
