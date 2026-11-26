import GridGraphs.Geometry.OccurrenceLabelledCotreeDualForest
import GridGraphs.ResidueTwoUpper.TwoGapNorthAligned

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
open SimpleGraph Finset

abbrev Cell (n : Nat) := Fin (n-1) × Fin (n-1)
def face {n} (v : Cell n) : GridFace n n := .cell v.1 v.2
def incident {n} (e : GridEdge n n) (f : GridFace n n) :=
  e.dualEndpoints.1=f ∨ e.dualEndpoints.2=f

/-- Each bounded face owns one omitted primal edge, incident to that
face; every omitted edge is owned exactly once. The edges here are
coordinate-labelled, even at corners where dual neighbors coincide. -/
theorem face_matching {n} (hn : 2≤n) (T : SimpleGraph (GridVertex n n))
    (sub : T≤gridGraph n n) (tree : T.IsTree) :
    ∃ pick : Cell n → GridEdge n n, Function.Injective pick ∧
      (∀ f, incident (pick f) (face f)) ∧ ∀ e,
      (∃ f, pick f=e) ↔ ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2 := by
  classical
  let free (e : GridEdge n n) := ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2
  let spans (e : GridEdge n n) (x y : GridFace n n) :=
    (e.dualEndpoints.1=x ∧ e.dualEndpoints.2=y) ∨ (e.dualEndpoints.1=y ∧ e.dualEndpoints.2=x)
  let D : SimpleGraph (GridFace n n) := {
    Adj x y := x≠y ∧ ∃ e, free e ∧ spans e x y
    symm := ⟨fun _ _ ⟨ne,e,h,k⟩ => ⟨ne.symm,e,h,k.symm⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  have reaches (x : GridFace n n) : D.Reachable x .out := by
    by_contra hx
    let S := {y | ¬D.Reachable y .out}
    obtain ⟨e,k,fr⟩ := SplitOccurrenceCotreeDualCore.exists_faceCut_crossing_not_adj_of_isAcyclic hn hn
      sub tree S ⟨x,hx⟩ (fun h => h .rfl)
    have cross {a b} (s : spans e a b) (ha : a∈S) (hb : b∉S) : False := by
      have adj : D.Adj a b := ⟨fun eq => hb (eq ▸ ha),e,fr,s⟩
      exact ha (adj.reachable.trans (not_not.mp hb))
    rcases k with k|k
    · exact cross (Or.inl ⟨rfl,rfl⟩) k.1 k.2
    · exact cross (Or.inr ⟨rfl,rfl⟩) k.1 k.2
  let depth (x : GridFace n n) := D.dist x .out
  have choose (f : Cell n) : ∃ e, free e ∧ ∃ y, spans e (face f) y ∧ depth y<depth (face f) := by
    obtain ⟨p,hp⟩ := (reaches (face f)).exists_walk_length_eq_dist
    have step {a b : GridFace n n} (q : D.Walk a b) (ne : a≠b) (len : q.length=D.dist a b) :
        ∃ y, D.Adj a y ∧ D.dist y b<D.dist a b := by
      cases q with
      | nil => contradiction
      | cons e rest =>
        exact ⟨_,e,by have := D.dist_le rest; simp only [Walk.length_cons] at len; omega⟩
    obtain ⟨y,⟨_,e,h,s⟩,lt⟩ := step p (by simp [face]) hp
    exact ⟨e,h,y,s,lt⟩
  let pick (f : Cell n) := (choose f).choose
  have fr (f) : free (pick f) := (choose f).choose_spec.1
  have desc (f) := (choose f).choose_spec.2
  have inj : Function.Injective pick := by
    intro f g eq
    obtain ⟨x,hx,lx⟩ := desc f; obtain ⟨y,hy,ly⟩ := desc g
    change spans (pick f) _ _ at hx; change spans (pick g) _ _ at hy
    rw [eq] at hx
    have same : face f=face g := by
      rcases hx with ⟨a,b⟩|⟨a,b⟩ <;> rcases hy with ⟨c,d⟩|⟨c,d⟩ <;>
        first | exact a.symm.trans c | exact b.symm.trans d
              | exfalso; exact (Nat.lt_asymm lx) (by simpa only [←a,←b,←c,←d] using ly)
    exact Prod.ext (GridFace.cell.inj same).1 (GridFace.cell.inj same).2
  let unused := (gridGraph n n).edgeFinset \ T.edgeFinset
  have counts := card_sdiff_add_card_eq_card (edgeFinset_mono sub)
  have size : unused.card=Fintype.card (Cell n) := by
    change unused.card+T.edgeFinset.card=_ at counts
    have t := tree.card_edgeFinset
    have g := gridGraph_card_edgeFinset n n
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    simp [Cell,GridVertex,numEdges,numHoriz,numVert] at t g ⊢
    nlinarith
  let im := univ.image (fun f : Cell n => (pick f).primalSym2)
  have all : im=unused := by
    apply eq_of_subset_of_card_le
    · intro e he; obtain ⟨f,_,rfl⟩ := mem_image.mp he
      exact mem_sdiff.mpr ⟨mem_edgeFinset.mpr ((pick f).primalSym2_mem_gridGraph_edgeSet),
        fun ht => fr f (mem_edgeFinset.mp ht)⟩
    · rw [size]; change _ ≤ (univ.image (GridEdge.primalSym2 ∘ pick)).card; rw [card_image_of_injective _ (GridEdge.primalSym2_injective.comp inj),card_univ]
  refine ⟨pick,inj,fun f => ?_,fun e => ⟨?_,?_⟩⟩
  · obtain ⟨_,h,_⟩ := desc f; exact h.elim (fun a => Or.inl a.1) (fun a => Or.inr a.2)
  · rintro ⟨f,rfl⟩; exact fr f
  · intro h
    have mem : e.primalSym2∈unused := mem_sdiff.mpr ⟨mem_edgeFinset.mpr e.primalSym2_mem_gridGraph_edgeSet,
      fun he => h (mem_edgeFinset.mp he)⟩
    rw [←all] at mem; obtain ⟨f,_,eq⟩ := mem_image.mp mem
    exact ⟨f,GridEdge.primalSym2_injective eq⟩

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
