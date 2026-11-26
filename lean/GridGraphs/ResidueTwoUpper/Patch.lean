import GridGraphs.Core.Forced

/-! Physical 3×3 patch support for the period-three relaxation. Inside
a 3×3 grid it suffices to exclude the nine rectangular perimeter cycles
to obtain exactly the 100 patch masks used by the dual. -/
namespace GridGraphs.ResidueTwoUpper.Patch
open SimpleGraph

abbrev Small := GridVertex 3 3
def bit (m : Fin 512) (p : Small) := m.val.testBit (3*p.1.val+p.2.val)

def perimeters : List (List Small) :=
  [[(0,0),(0,1),(1,1),(1,0)], [(0,1),(0,2),(1,2),(1,1)],
   [(1,0),(1,1),(2,1),(2,0)], [(1,1),(1,2),(2,2),(2,1)],
   [(0,0),(0,1),(0,2),(1,2),(1,1),(1,0)],
   [(1,0),(1,1),(1,2),(2,2),(2,1),(2,0)],
   [(0,0),(0,1),(1,1),(2,1),(2,0),(1,0)],
   [(0,1),(0,2),(1,2),(2,2),(2,1),(1,1)],
   [(0,0),(0,1),(0,2),(1,2),(2,2),(2,1),(2,0),(1,0)]]

def covered (m : Fin 512) (r : List Small) :=
  (r.zip (r.rotateLeft 1)).all fun (p,q) => bit m p || bit m q

def allowed (m : Fin 512) := !perimeters.any (covered m)

theorem count_allowed : (Finset.univ.filter fun m => allowed m).card = 100 := by
  decide +kernel

private theorem geometry : ∀ r ∈ perimeters, 2 < r.length ∧
    Function.Injective (fun i : Fin r.length => r[i]) ∧
    ∀ i j : Fin r.length, (cycleGraph r.length).Adj i j →
      (gridGraph 3 3).Adj r[i] r[j] ∧
        ((r[i],r[j]) ∈ r.zip (r.rotateLeft 1) ∨ (r[j],r[i]) ∈ r.zip (r.rotateLeft 1)) := by
  unfold Function.Injective
  decide +kernel

def place {n a b : Nat} (ha : a+2<n) (hb : b+2<n) (p : Small) : GridVertex n n :=
  (⟨a+p.1.val,by have := p.1.isLt; omega⟩,⟨b+p.2.val,by have := p.2.isLt; omega⟩)

private theorem place_inj {n a b} (ha : a+2<n) (hb : b+2<n) :
    Function.Injective (place ha hb) := by
  intro p q eq
  have e := congrArg (fun x : GridVertex n n => x.1.val) eq
  have f := congrArg (fun x : GridVertex n n => x.2.val) eq
  exact Prod.ext (Fin.ext (Nat.add_left_cancel e)) (Fin.ext (Nat.add_left_cancel f))

private theorem place_adj {n a b} (ha : a+2<n) (hb : b+2<n) {p q : Small}
    (e : (gridGraph 3 3).Adj p q) : (gridGraph n n).Adj (place ha hb p) (place ha hb q) := by
  change adjacent 3 3 p q at e
  change adjacent n n _ _
  simp only [adjacent,Fin.ext_iff,place] at e ⊢
  omega

def patchMask {n a b} (ha : a+2<n) (hb : b+2<n) (F : Finset (GridVertex n n)) : Fin 512 :=
  ((BitVec.ofBoolListLE ((List.finRange 9).map fun i =>
    decide (place ha hb (Fin.ofNat 3 (i.val/3),Fin.ofNat 3 i.val) ∈ F))).cast
    (by simp) : BitVec 9).toFin

theorem patchMask_bit {n a b} (ha : a+2<n) (hb : b+2<n) (F : Finset (GridVertex n n))
    (p : Small) : bit (patchMask ha hb F) p = decide (place ha hb p ∈ F) := by
  change (BitVec.getLsbD _ _) = _
  simp only [BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> rfl

theorem physical_allowed {n a b} (ha : a+2<n) (hb : b+2<n)
    (F : Finset (GridVertex n n))
    (h : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    allowed (patchMask ha hb F) := by
  by_contra bad
  simp only [allowed,Bool.not_eq_true',Bool.not_eq_false,List.any_eq_true] at bad
  obtain ⟨r,hr,cover⟩ := bad
  obtain ⟨len,inj,adj⟩ := geometry r hr
  have forced {p q} (e : (p,q) ∈ r.zip (r.rotateLeft 1)) :
      place ha hb p ∈ F ∨ place ha hb q ∈ F := by
    have marks := List.all_eq_true.mp cover _ e
    simpa only [patchMask_bit,Bool.or_eq_true,decide_eq_true_eq] using marks
  have contains : cycleGraph r.length ⊑ forcedEdgeGraph (gridGraph n n) (↑F : Set _) := by
    refine ⟨⟨⟨fun i => place ha hb r[i],?_⟩,(place_inj ha hb).comp inj⟩⟩
    intro i j hij
    obtain ⟨grid,edge⟩ := adj i j hij
    exact ⟨place_adj ha hb grid,edge.elim forced (fun rev => (forced rev).symm)⟩
  obtain ⟨_,p,cyc,_⟩ := (cycleGraph_isContained_iff len).mp contains
  exact h p cyc

end GridGraphs.ResidueTwoUpper.Patch
