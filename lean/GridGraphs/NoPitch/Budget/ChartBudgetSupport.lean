import GridGraphs.NoPitch.Budget.LineAmounts
import GridGraphs.NoPitch.TailStarCoverage

namespace GridGraphs.NoPitch.Budget
open PitchCut Finset Keys GridGraphs.NoPitch.Dual TailCoverage
attribute [local irreducible] chart19 chart58 chart61

/-- Check the retained matrix itself. The unsigned debit, independent
join upper bound and off-skeleton cap all have sense 1. None is retained
on these three supports; the corner lower bound is their only inequality. -/
def shape (D : Chart) := D.rows.all fun r =>
  if r.source=1 then r.sense==2 && r.rhs==⟨2,0,0⟩ else r.sense==0
private theorem shape19 : shape chart19 := by native_decide
private theorem shape58 : shape chart58 := by native_decide
private theorem shape61 : shape chart61 := by native_decide

private theorem sense {D : Chart} (ok : shape D) (i : Fin D.rows.size) :
    (D.rows[i].source=1 ∧ D.rows[i].sense=2 ∧ D.rows[i].rhs=⟨2,0,0⟩) ∨ D.rows[i].sense=0 := by
  have h := Array.all_eq_true_iff_forall_mem.mp ok _ (Array.getElem_mem i.isLt)
  by_cases src : D.rows[i].source=1 <;> simp_all

theorem sense19 (i : Fin chart19.rows.size) :
    (chart19.rows[i].source=1 ∧ chart19.rows[i].sense=2 ∧ chart19.rows[i].rhs=⟨2,0,0⟩) ∨
      chart19.rows[i].sense=0 := sense shape19 i

theorem sense_tail {k : Nat} (i : Fin (tailChart k).rows.size) :
    ((tailChart k).rows[i].source=1 ∧ (tailChart k).rows[i].sense=2 ∧
      (tailChart k).rows[i].rhs=⟨2,0,0⟩) ∨ (tailChart k).rows[i].sense=0 := by
  apply sense; unfold tailChart; split <;> first | exact shape58 | exact shape61

/-- A packed line debit is not charged to any retained `≤` row. -/
theorem no_upper_tail {k : Nat} (i : Fin (tailChart k).rows.size) : (tailChart k).rows[i].sense≠1 := by
  rcases sense_tail i with h|h <;> omega

end GridGraphs.NoPitch.Budget
