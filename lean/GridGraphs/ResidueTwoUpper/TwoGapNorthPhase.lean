import GridGraphs.ResidueTwoUpper.TwoGapNorthInputs

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North
open SimpleGraph ResidueZero Stencil Words BoundarySix.Connected

abbrev Rect := GridVertex 5 4
def belt : Fin 14 → Rect := ![(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),
  (4,3),(4,2),(4,1),(4,0),(3,0),(2,0),(1,0)]
def place {n j : Nat} (hn : 5≤n) (hj : j+4≤n) (s : Rect) : GridVertex n n :=
  (⟨s.1.val,by have := s.1.isLt; omega⟩,⟨j+s.2.val,by have := s.2.isLt; omega⟩)

/-- The single type of cycle rejected by the width-six phase scan.
A complete 5-by-4 belt has fourteen edges; it is enough for one
endpoint of each edge to be marked, not necessarily the whole belt. -/
theorem rectangle_missing {n j} (hn : 5≤n) (hj : j+4≤n) (F : Finset (GridVertex n n))
    (acy : (Bonds F).IsAcyclic) :
    ∃ i : Fin 14, place hn hj (belt i)∉F ∧ place hn hj (belt (i+1))∉F := by
  classical
  by_contra! all
  have adj : ∀ i : Fin 14, (gridGraph 5 4).Adj (belt i) (belt (i+1)) := by native_decide
  have edge (i : Fin 14) : (Bonds F).Adj (place hn hj (belt i)) (place hn hj (belt (i+1))) := by
    constructor
    · have h := adj i; change adjacent _ _ _ _ at h ⊢
      simp only [adjacent,Fin.ext_iff,place] at h ⊢; omega
    · exact or_iff_not_imp_left.mpr (all i)
  let f : cycleGraph 14 →g Bonds F := ⟨fun i => place hn hj (belt i),fun {i k} h => by
    rcases (by native_decide : ∀ a b : Fin 14, (cycleGraph 14).Adj a b → a+1=b ∨ b+1=a) i k h with e|e
    · exact e ▸ edge i
    · exact e ▸ (edge k).symm⟩
  have inj : Function.Injective f := by
    intro i k e
    apply (by native_decide : Function.Injective belt)
    have x := congrArg (fun v : GridVertex n n => v.1.val) e
    have y := congrArg (fun v : GridVertex n n => v.2.val) e
    exact Prod.ext (Fin.ext x) (Fin.ext (Nat.add_left_cancel (show j+(belt i).2.val=j+(belt k).2.val from y)))
  have tree : (cycleGraph 14).IsTree := ⟨cycleGraph_connected,acy.comap f inj⟩
  have count := tree.card_edgeFinset
  have num : (cycleGraph 14).edgeFinset.card=14 := by native_decide
  simp [num] at count

/-- The exact missing input to the adjacent-frame checker. Alignment alone
puts the exit in the admissible index range even on side 35. -/
theorem short_inputs {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (canon : packed (signature (by omega) F)=code4 0 0 1 1)
    (phase : ∀ P d, Chart F P d → d%3=2) :
    ∃ P q, 1≤q ∧ q+2≤11+14*u ∧ Chart F P (2+3*q) ∧
      (∀ v, IsGridBoundary v → outDir v (P v)=(rimDatum (11+14*(u:Int)) q v.2.val v.1.val).2.1) ∧
      ∀ c : Fin (35+42*u), 3≤c.val ∧ c.val+3≤34+42*u → c.val≠2+3*q →
        ((⟨2,by omega⟩,c) : GridVertex (35+42*u) (35+42*u))∈F → P (⟨2,by omega⟩,c)=(⟨1,by omega⟩,c) := by
  obtain ⟨P,d,C⟩ := chart_of_0011 F acy score two canon
  have := phase P d C
  obtain ⟨lo,hi,exc⟩ := C.ordinary
  have eq : d=2+3*(d/3) := by omega
  refine ⟨P,d/3,by omega,by omega,eq ▸ C,fun v bd => parent_field C eq v bd,?_⟩
  intro c bounds ne mark
  exact tooth_arrow C acy score canon c bounds (by rwa [eq]) mark

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North
