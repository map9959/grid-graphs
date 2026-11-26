import GridGraphs.ResidueTwoUpper.PhysicalCounts

/-! The three overlap identities for actual occurrences, before taking
orbits. Keys and weights used for pooling may be arbitrary. -/
namespace GridGraphs.ResidueTwoUpper.Overlap
open Finset PhysicalCounts GridGraphs.ResidueTwoUpper.Star

private theorem step_inj {s} {x : Site s} {d e : Dir} {h k}
    (eq : step x d h=step x e k) : d=e := by
  have a := congrArg (fun p : Site s => p.1.val) eq
  have b := congrArg (fun p : Site s => p.2.val) eq
  dsimp only [step] at a b
  have hd := h.1.1; have he := k.1.1; have fd := h.2.1; have fe := k.2.1
  have r : dr d=dr e := by omega
  have c : dc d=dc e := by omega
  exact (show ∀ d e : Dir, dr d=dr e → dc d=dc e → d=e by decide) d e r c

theorem out_iff {s} {F : Finset (Site s)} {root : Site s}
    (A : RootArrows (forcedEdgeGraph (gridGraph s s) (↑F : Set _)) root)
    (x : Site s) (d : Dir) (ok : inside s x.1 x.2 d) :
    out A x=some d ↔ A.parent x=some (step x d ok) := by
  constructor
  · intro h; obtain ⟨_,e⟩ := out_spec A x d h; exact e
  · intro e
    cases eq : out A x with
    | none => have := (out_none A x).mp eq; simp_all
    | some j =>
      obtain ⟨h,p⟩ := out_spec A x j eq
      exact congrArg some (step_inj (Option.some.inj (p.symm.trans e)))

structure Bond (s : Nat) where
  x : Site s
  y : Site s
  d : Dir
  e : Dir
  hi : inside s x.1 x.2 d
  hj : inside s y.1 y.2 e
  forward : step x d hi=y
  backward : step y e hj=x

def forwardView {s} (F : Finset (Site s)) (o : Site s → Option Dir) (p : Bond s) :
    Bool × Bool × Bool :=
  (decide (p.x∈F),sample F p.x p.d,decide (o p.x=some p.d))
def backwardView {s} (F : Finset (Site s)) (o : Site s → Option Dir) (p : Bond s) :
    Bool × Bool × Bool :=
  (sample F p.y p.e,decide (p.y∈F),
   (sample F p.y p.e || decide (p.y∈F)) && decide (o p.y≠some p.e))

theorem step_adj {s} (x : Site s) (d : Dir) (h : inside s x.1 x.2 d) :
    (gridGraph s s).Adj x (step x d h) := by
  change adjacent s s _ _
  simp only [adjacent,Fin.ext_iff,step]
  have a := h.1.1; have b := h.2.1
  fin_cases d <;> norm_num [dr,dc] at * <;> omega

theorem edge_agrees {s} {F : Finset (Site s)} {root : Site s}
    (A : RootArrows (forcedEdgeGraph (gridGraph s s) (↑F : Set _)) root) (p : Bond s) :
    forwardView F (out A) p = backwardView F (out A) p := by
  have a := out_iff A p.x p.d p.hi
  have b := out_iff A p.y p.e p.hj
  rw [p.forward] at a; rw [p.backward] at b
  have grid := step_adj p.x p.d p.hi
  rw [p.forward] at grid
  simp only [forwardView,backwardView,sample,dif_pos p.hi,dif_pos p.hj,p.forward,p.backward]
  by_cases yes : p.x∈F ∨ p.y∈F
  · have edge := A.edge ⟨grid,yes⟩
    have ar : out A p.x=some p.d ↔ out A p.y≠some p.e := a.trans (edge.trans (not_congr b.symm))
    rcases yes with hx|hy <;> simp [*]
  · have no : out A p.x≠some p.d := fun e => yes (A.legal (a.mp e)).2
    simp only [not_or] at yes
    simp [yes.1,yes.2,no]

abbrev PatchPos (t : Nat) := Site (S t)
def embed {t} (p : PatchPos t) (q : Patch.Small) : Site (N t) :=
  Patch.place (a:=p.1.val) (b:=p.2.val) (by have := p.1.isLt; dsimp [N,S] at *; omega)
    (by have := p.2.isLt; dsimp [N,S] at *; omega) q
def mask {t} (F : Finset (Site (N t))) (p : PatchPos t) :=
  Patch.patchMask (a:=p.1.val) (b:=p.2.val) (by have := p.1.isLt; dsimp [N,S] at *; omega)
    (by have := p.2.isLt; dsimp [N,S] at *; omega) F

theorem projection_center {t} (F : Finset (Site (N t))) (p : PatchPos t) (q : Patch.Small) :
    Patch.bit (mask F p) q = decide (embed p q∈F) := Patch.patchMask_bit .. 

private theorem embed_step {t} (p : PatchPos t) (q : Patch.Small) (d : Dir)
    (h : inside 3 q.1 q.2 d) :
    ∃ ok : inside (N t) (embed p q).1 (embed p q).2 d,
      step (embed p q) d ok=embed p (step q d h) := by
  obtain ⟨⟨a,b⟩,⟨c,e⟩⟩ := h
  have pp := p.1.isLt; have pq := p.2.isLt
  dsimp [S] at pp pq
  refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,?_⟩
  all_goals simp only [embed,Patch.place,step,Prod.ext_iff,Fin.ext_iff,N]
  all_goals omega

theorem projection_neighbor {t} (F : Finset (Site (N t))) (p : PatchPos t) (q : Patch.Small)
    (d : Dir) (h : inside 3 q.1 q.2 d) :
    Patch.bit (mask F p) (step q d h)=sample F (embed p q) d := by
  obtain ⟨ok,eq⟩ := embed_step p q d h
  rw [projection_center]; simp [sample,ok,eq]

/-- The six overlap bits are read with a common physical coordinate in
both patches; the statement holds for any subword in any order. -/
theorem shared_word {t} (F : Finset (Site (N t))) (p p' : PatchPos t)
    {L : Type*} (q q' : L → Patch.Small) (same : ∀ l, embed p (q l)=embed p' (q' l)) :
    (fun l => Patch.bit (mask F p) (q l)) = fun l => Patch.bit (mask F p') (q' l) := by
  funext l; rw [projection_center,projection_center,same]

/-- Pool signed differences after identifying the two physical events.
This applies without symmetry or translation invariance of the input. -/
theorem cancel {I E : Type*} [Fintype I] (left right : I → E) (val : I → E → Int)
    (agree : ∀ i, left i=right i) : (∑ i, val i (left i))-(∑ i, val i (right i))=0 := by
  rw [funext agree,sub_self]

end GridGraphs.ResidueTwoUpper.Overlap
