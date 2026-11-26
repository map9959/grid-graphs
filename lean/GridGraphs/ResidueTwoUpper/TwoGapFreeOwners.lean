import GridGraphs.ResidueTwoUpper.TwoGapFaceOwners

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
open SimpleGraph Finset ResidueZero

def isolated {n} (F : Finset (GridVertex n n)) (v : GridVertex n n) := ∀ w, ¬(Bonds F).Adj v w
def endsAt {n} (e : GridEdge n n) (v : GridVertex n n) :=
  e.primalEndpoints.1=v ∨ e.primalEndpoints.2=v

private theorem adjacent_head {V : Type*} {T : SimpleGraph V} (P : V → V)
    (arr : ∀ a b, T.Adj a b → (P a=b ↔ P b≠a)) {a b} (p : T.Walk a b) :
    p.IsPath → a≠b → P b=b → P a=p.snd := by
  induction p with
  | nil => simp
  | @cons a x b edge tail ih =>
    intro path _ fix
    rw [Walk.snd_cons]
    apply (arr _ _ edge).mpr
    by_cases end' : x=b
    · subst b; rw [fix]; exact edge.ne.symm
    · rw [ih path.of_cons end' fix]
      intro back; exact ((Walk.cons_isPath_iff edge tail).mp path).2 (back ▸ tail.getVert_mem_support 1)

/-- A forest with all active vertices in the root component admits a
perfect assignment of the unforced edges to its isolated vertices and
its bounded cells. No marked/score hypothesis enters the dual step. -/
theorem free_matching {n} (hn : 2≤n) (F : Finset (GridVertex n n))
    (acy : (Bonds F).IsAcyclic) (root : GridVertex n n) (activeRoot : ¬isolated F root)
    (reach : ∀ x y, (Bonds F).Adj x y → (Bonds F).Reachable root x) :
    ∃ own : ({v // isolated F v} ⊕ Cell n) → GridEdge n n,
      Function.Injective own ∧ (∀ v, endsAt (own (.inl v)) v.1) ∧
      (∀ f, incident (own (.inr f)) (face f)) ∧ ∀ e,
      (∃ x, own x=e) ↔ e.primalEndpoints.1∉F ∧ e.primalEndpoints.2∉F := by
  classical
  let G := Bonds F
  obtain ⟨T,sub,leGrid,tree⟩ := (gridGraph_connected (m:=n) (n:=n) (by omega) (by omega)).exists_isTree_le_of_le_of_isAcyclic
    (show G≤gridGraph n n from fun _ _ h => h.1) acy
  obtain ⟨pick,inj,incident',image⟩ := face_matching hn T leGrid tree
  let R (_ : T.ConnectedComponent) := root
  have sec (c : T.ConnectedComponent) : T.connectedComponentMk (R c)=c := by
    rw [←Quot.out_eq c]; exact ConnectedComponent.sound (tree.connected.preconnected _ _)
  let P := CapBill.parent R sec
  have fx (x) : P x=x ↔ x=root := CapBill.parent_fix R sec x
  have step {x} (ne : x≠root) : T.Adj x (P x) ∧ CapBill.depth R (P x)<CapBill.depth R x :=
    CapBill.parent_step R sec ne
  have arr (x y) (edge : T.Adj x y) : P x=y ↔ P y≠x := by
    constructor
    · intro a b
      have nx : x≠root := fun e => edge.ne (((fx x).mpr e).symm.trans a)
      have ny : y≠root := fun e => edge.ne.symm (((fx y).mpr e).symm.trans b)
      have sx := (step nx).2; have sy := (step ny).2; rw [a] at sx; rw [b] at sy; omega
    · exact fun no => (CapBill.parent_covers R sec tree.isAcyclic edge).resolve_right no
  have inherited {x} (ne : x≠root) (active : ¬isolated F x) : G.Adj x (P x) := by
    obtain ⟨y,h⟩ : ∃ y, G.Adj x y := by simpa [isolated,G] using active
    obtain ⟨p,hp⟩ := (reach x y h).symm.exists_isPath
    have first := adjacent_head P arr (p.mapLe sub) (hp.mapLe sub) ne ((fx root).mpr rfl)
    rw [first]
    have firstStep {a b} (w : G.Walk a b) (d : a≠b) : G.Adj a (w.mapLe sub).snd := by
      cases w with
      | nil => contradiction
      | cons e q => simpa [Walk.mapLe] using e
    exact firstStep p ne
  have isoNe (v : {x // isolated F x}) : v.1≠root := fun eq => activeRoot (eq ▸ v.2)
  let src (v : {x // isolated F x}) : (gridGraph n n).edgeSet :=
    ⟨s(v.1,P v.1),leGrid (step (isoNe v)).1⟩
  let ext (v : {x // isolated F x}) := (GridEdge.equivGridGraphEdgeSet n n).symm (src v)
  have literal (v) : (ext v).primalSym2=s(v.1,P v.1) :=
    congrArg Subtype.val ((GridEdge.equivGridGraphEdgeSet n n).apply_symm_apply (src v))
  have extTree (v) : T.Adj (ext v).primalEndpoints.1 (ext v).primalEndpoints.2 := by
    change (ext v).primalSym2 ∈ T.edgeSet
    rw [literal]; exact (step (isoNe v)).1
  have dis (v f) : ext v≠pick f := fun eq => ((image _).mp ⟨f,eq.symm⟩) (extTree v)
  let own := Sum.elim ext pick
  refine ⟨own,?_,?_,incident',?_⟩
  · rintro (a|a) (b|b) h
    · have eq := (literal a).symm.trans ((congrArg GridEdge.primalSym2 h).trans (literal b))
      rcases Sym2.eq_iff.mp eq with ⟨e,_⟩|⟨e,k⟩
      · exact congrArg Sum.inl (Subtype.ext e)
      · exact False.elim (((arr _ _ (k ▸ (step (isoNe a)).1)).mp k) e.symm)
    · exact False.elim (dis _ _ h)
    · exact False.elim (dis _ _ h.symm)
    · exact congrArg Sum.inr (inj h)
  · intro v; rcases Sym2.eq_iff.mp (literal v) with h|h
    · exact Or.inl h.1
    · exact Or.inr h.2
  · intro e; have gr : (gridGraph n n).Adj e.primalEndpoints.1 e.primalEndpoints.2 := e.primalSym2_mem_gridGraph_edgeSet
    have iff : ¬G.Adj e.primalEndpoints.1 e.primalEndpoints.2 ↔ e.primalEndpoints.1∉F ∧ e.primalEndpoints.2∉F := by
      change ¬(_ ∧ (_ ∨ _)) ↔ _; tauto
    rw [←iff]
    constructor
    · rintro ⟨v,rfl⟩; cases v with
      | inl v =>
        change ¬(ext v).primalSym2∈G.edgeSet; rw [literal]; exact v.2 _
      | inr f => exact fun h => ((image _).mp ⟨f,rfl⟩) (sub h)
    · intro no
      by_cases ht : T.Adj e.primalEndpoints.1 e.primalEndpoints.2
      · have claim {x y} (eq : e.primalSym2=s(x,y)) (p : P x=y) (ne : x≠y) : ∃ v, own v=e := by
          have nx : x≠root := fun z => ne (((fx x).mpr z).symm.trans p)
          have iso : isolated F x := by
            by_contra active; apply no; change e.primalSym2∈G.edgeSet; rw [eq,←p]; exact inherited nx active
          refine ⟨.inl ⟨x,iso⟩,GridEdge.primalSym2_injective ?_⟩
          change (ext ⟨x,iso⟩).primalSym2=_; rw [literal,eq,p]
        rcases CapBill.parent_covers R sec tree.isAcyclic ht with p|p
        · exact claim rfl p ht.ne
        · exact claim Sym2.eq_swap p ht.ne.symm
      · obtain ⟨f,h⟩ := (image _).mpr ht; exact ⟨.inr f,h⟩

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
