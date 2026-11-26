import GridGraphs.Results.ExactSquareFormula
import GridGraphs.Geometry.PhysicalFaceLine

/-! A local forest replacement may disconnect ports, but may not connect two
formerly disconnected ports. Under that hypothesis, *every* unchanged
exterior which worked for the old forest still works for the replacement. -/
namespace GridGraphs.NoPitch
open SimpleGraph Finset PitchCut

private theorem lift_walk {V : Type*} {A B : SimpleGraph V} (f : V → V)
    (h : ∀ ⦃x y⦄, A.Adj x y → B.Reachable (f x) (f y))
    {x y} (r : A.Reachable x y) : B.Reachable (f x) (f y) := by
  obtain ⟨w⟩ := r
  induction w with
  | nil => rfl
  | cons e _ ih => exact (h e).trans ih

/-- Pin every port; send the remaining vertices in each new component to
a representative port if there is one. Only reachability is transported. -/
private theorem port_map {V : Type*} (A B : SimpleGraph V) (P : Set V)
    (refines : ∀ x∈P, ∀ y∈P, A.Reachable x y → B.Reachable x y) :
    ∃ f : V → V, (∀ x∈P, f x=x) ∧ ∀ ⦃x y⦄, A.Adj x y → B.Reachable (f x) (f y) := by
  classical
  let rep (c : A.ConnectedComponent) :=
    if h : ∃ z∈P, A.connectedComponentMk z=c then h.choose else c.out
  let f (x : V) := if x∈P then x else rep (A.connectedComponentMk x)
  have same (x) : B.Reachable (f x) (rep (A.connectedComponentMk x)) := by
    by_cases hx : x∈P
    · let h : ∃ z∈P, A.connectedComponentMk z=A.connectedComponentMk x := ⟨x,hx,rfl⟩
      simp only [f,if_pos hx,rep,dif_pos h]
      exact refines _ hx _ h.choose_spec.1 (ConnectedComponent.exact h.choose_spec.2.symm)
    · simp [f,hx]
  refine ⟨f,fun x hx => by simp [f,hx],?_⟩
  intro x y edge
  have h := same x
  rw [ConnectedComponent.sound edge.reachable] at h
  exact h.trans (same y).symm

/-- Install a finite, ordered set of exterior edges. The strict order is
only for counting each undirected edge once. -/
def exterior {V : Type*} (s : Finset (V × V)) : SimpleGraph V :=
  ⨆ e ∈ s, SimpleGraph.edge e.1 e.2

theorem exterior_adj {V : Type*} (s : Finset (V × V)) (x y : V) :
    (exterior s).Adj x y ↔ x≠y ∧ ((x,y)∈s ∨ (y,x)∈s) := by
  simp only [exterior,iSup_adj,SimpleGraph.edge_adj]
  constructor
  · rintro ⟨⟨a,b⟩,h,⟨rfl,rfl⟩|⟨rfl,rfl⟩,ne⟩ <;> tauto
  · rintro ⟨ne,h|h⟩
    · exact ⟨(x,y),h,.inl ⟨rfl,rfl⟩,ne⟩
    · exact ⟨(y,x),h,.inr ⟨rfl,rfl⟩,ne⟩

theorem forest_glue {V : Type*} (A B : SimpleGraph V) (P : Set V)
    (refines : ∀ x∈P, ∀ y∈P, A.Reachable x y → B.Reachable x y)
    (forest : A.IsAcyclic) (s : Finset (V × V))
    (outside : ∀ e∈s, (e.2,e.1)∉s ∧ e.1∈P ∧ e.2∈P ∧ ¬B.Adj e.1 e.2)
    (old : (B ⊔ exterior s).IsAcyclic) : (A ⊔ exterior s).IsAcyclic := by
  classical
  obtain ⟨f,pin,lift⟩ := port_map A B P refines
  induction s using Finset.induction_on with
  | empty => simpa [exterior] using forest
  | @insert e s fresh ih =>
    obtain ⟨ord,p,q,missing⟩ := outside e (mem_insert_self ..)
    have rest := fun a (ha : a∈s) => outside a (mem_insert_of_mem ha)
    have step (H : SimpleGraph V) : H ⊔ exterior (insert e s) =
        (H ⊔ exterior s) ⊔ SimpleGraph.edge e.1 e.2 := by
      simp only [exterior,Finset.iSup_insert]; ac_rfl
    rw [step] at old ⊢
    have prev := ih (fun a ha => ⟨fun h => (rest a ha).1 (mem_insert_of_mem h),(rest a ha).2⟩)
      (old.anti le_sup_left)
    apply prev.sup_edge_of_not_reachable
    intro r
    have map {x y} (adj : (A ⊔ exterior s).Adj x y) :
        (B ⊔ exterior s).Reachable (f x) (f y) := by
      rcases adj with a|a
      · exact (lift a).mono le_sup_left
      · obtain ⟨_,h|h⟩ := (exterior_adj ..).mp a
        · rw [pin _ (rest _ h).2.1,pin _ (rest _ h).2.2.1]; exact a.reachable.mono le_sup_right
        · rw [pin _ (rest _ h).2.2.1,pin _ (rest _ h).2.1]; exact a.reachable.mono le_sup_right
    have conflict := lift_walk f (@map) r
    rw [pin _ p,pin _ q] at conflict
    rcases (isAcyclic_sup_fromEdgeSet_iff.mp old).2 conflict with eq|a|a
    · apply ord; apply mem_insert.mpr; left; exact Prod.ext eq.symm eq
    · exact missing a
    · obtain ⟨_,h|h⟩ := (exterior_adj ..).mp a
      · exact fresh h
      · exact ord (mem_insert_of_mem h)

end GridGraphs.NoPitch

namespace GridGraphs.NoPitch
open SimpleGraph Finset PitchCut
variable {k : Nat} (p : FacePos k)

def inBox (x : Site k) := 3*p.1.val≤x.1.val ∧ x.1.val≤3*p.1.val+3 ∧
  3*p.2.val≤x.2.val ∧ x.2.val≤3*p.2.val+3
def inCore (x : Site k) := 3*p.1.val<x.1.val ∧ x.1.val<3*p.1.val+3 ∧
  3*p.2.val<x.2.val ∧ x.2.val<3*p.2.val+3
instance (x : Site k) : Decidable (inCore p x) := by unfold inCore; infer_instance

abbrev fg (F : Finset (Site k)) := forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)
def faceGraph (F : Finset (Site k)) := confined (fg F) (inBox p)

private theorem inner_neighbor {x y : Site k} (hx : inCore p x)
    (adj : (gridGraph (N k) (N k)).Adj x y) : inBox p x ∧ inBox p y := by
  unfold inBox inCore at *
  rcases adj with ⟨e,h|h⟩|⟨e,h|h⟩ <;> have eq := congrArg Fin.val e <;> omega

/-- The changed four sites cannot affect a single exterior edge. The only
ports requiring a connectivity test are the twelve boundary vertices. -/
theorem refill_forest (F R : Finset (Site k)) (acy : (fg F).IsAcyclic)
    (same : ∀ x, ¬inCore p x → (x∈R ↔ x∈F))
    (localForest : (faceGraph p R).IsAcyclic)
    (ports : ∀ x, inBox p x → ¬inCore p x → ∀ y, inBox p y → ¬inCore p y →
      (faceGraph p R).Reachable x y → (faceGraph p F).Reachable x y) :
    (fg R).IsAcyclic := by
  classical
  let s := univ.filter (fun e : Site k × Site k =>
    toLex e.1<toLex e.2 ∧ (fg F).Adj e.1 e.2 ∧ ¬(inBox p e.1 ∧ inBox p e.2))
  have off {x y : Site k} (a : (gridGraph (N k) (N k)).Adj x y) (h : ¬(inBox p x ∧ inBox p y)) :
      ¬inCore p x ∧ ¬inCore p y :=
    ⟨fun hx => h (inner_neighbor p hx a),fun hy => h (inner_neighbor p hy a.symm).symm⟩
  have split (M : Finset (Site k)) (hm : ∀ x, ¬inCore p x → (x∈M ↔ x∈F)) :
      fg M = faceGraph p M ⊔ exterior s := by
    ext x y
    change (fg M).Adj x y ↔ ((fg M).Adj x y ∧ inBox p x ∧ inBox p y) ∨ _
    rw [exterior_adj]
    simp only [s,mem_filter,mem_univ,true_and]
    by_cases boxes : inBox p x ∧ inBox p y
    · tauto
    have flip : ¬(inBox p y ∧ inBox p x) := fun h => boxes h.symm
    have iff : (fg M).Adj x y ↔ (fg F).Adj x y := by
      change (_ ∧ (x∈M ∨ y∈M)) ↔ (_ ∧ (x∈F ∨ y∈F))
      constructor <;> rintro ⟨a,m⟩ <;> refine ⟨a,?_⟩ <;>
        simpa only [hm _ (off a boxes).1,hm _ (off a boxes).2] using m
    constructor
    · intro a
      have ne := a.ne
      rcases lt_or_gt_of_ne (show toLex x≠toLex y from ne) with h|h
      · exact Or.inr ⟨ne,Or.inl ⟨h,iff.mp a,boxes⟩⟩
      · exact Or.inr ⟨ne,Or.inr ⟨h,(iff.mp a).symm,flip⟩⟩
    · rintro (⟨a,_⟩|⟨_,⟨_,a,_⟩|⟨_,a,_⟩⟩)
      exacts [a,iff.mpr a,iff.mpr a.symm]
  rw [split R same]
  apply forest_glue (faceGraph p R) (faceGraph p F) {x | ¬inCore p x} _ localForest
  · intro e he
    obtain ⟨ord,a,h⟩ := (mem_filter.mp he).2
    exact ⟨fun m => ord.asymm (mem_filter.mp m).2.1,(off a.1 h).1,(off a.1 h).2,fun adj => h adj.2⟩
  · rwa [←split F (fun _ _ => Iff.rfl)]
  · intro x hx y hy r
    by_cases eq : x=y
    · rw [eq]
    obtain ⟨_,a⟩ := r.nonempty_neighborSet_left eq
    obtain ⟨_,b⟩ := r.symm.nonempty_neighborSet_left (Ne.symm eq)
    exact ports _ a.2.1 hx _ b.2.1 hy r

theorem maximizer_refill (F R : Finset (Site k)) (acy : (fg F).IsAcyclic)
    (optimal : F.card=maxPreserved (N k) (N k))
    (same : ∀ x, ¬inCore p x → (x∈R ↔ x∈F))
    (localForest : (faceGraph p R).IsAcyclic)
    (ports : ∀ x, inBox p x → ¬inCore p x → ∀ y, inBox p y → ¬inCore p y →
      (faceGraph p R).Reachable x y → (faceGraph p F).Reachable x y) :
    (R.filter (inCore p)).card ≤ (F.filter (inCore p)).card := by
  have bound := (squareMaskScore_iff_le (n:=N k) (s:=R.card) (by unfold N; omega)).mp
    ⟨R,mem_acyclicForcedSets.mpr (refill_forest p F R acy same localForest ports),rfl⟩
  have unchanged : R.filter (fun x => ¬inCore p x)=F.filter (fun x => ¬inCore p x) := by
    ext x; simp only [mem_filter]; by_cases hx : inCore p x <;> simp_all
  have h := card_filter_add_card_filter_not (s:=R) (p:=inCore p)
  have g := card_filter_add_card_filter_not (s:=F) (p:=inCore p)
  rw [unchanged] at h; omega

end GridGraphs.NoPitch
