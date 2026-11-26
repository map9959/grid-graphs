import GridGraphs.NoPitch.Budget.ForbiddenStars
import GridGraphs.NoPitch.Budget.ChartBudgetSupport
import GridGraphs.NoPitch.Budget.LineSymmetries
import GridGraphs.Results.PhysicalTailUpper

namespace GridGraphs.NoPitch.Budget
open PitchCut Finset GridGraphs.NoPitch.Dual TailCoverage
attribute [local irreducible] chart19 chart58 chart61
variable {k : Nat}

private def positional (D : Chart) := decide (∀ i : Fin D.rows.size, D.rows[i].source=1 → i.val=0)
private theorem pos19 : positional chart19 := by native_decide
private theorem pos58 : positional chart58 := by native_decide
private theorem pos61 : positional chart61 := by native_decide
private theorem tailZero {D : Chart} {b : Int} (ok : tailCheck D b) (i : Fin D.cols.size) :
    ¬0<price D i := by
  have non (j : Fin D.cols.size) : 0≤price D j := by unfold price; split <;> first | rfl | exact le_max_left ..
  have h := single_le_sum (s:=univ) (f:=price D) (fun j _ => non j) (mem_univ i)
  change _≤repair D at h
  simp only [tailCheck,Bool.and_eq_true,beq_iff_eq] at ok
  have z := ok.1.1.1.2
  omega

/-- The tail dual needs only its remaining equality rows on this one
physical vector. There is no nonnegativity, fixed-column, residual cap
or corner-root obligation left for the caller. -/
theorem tail_upper_of_equalities (hk : 19≤k) (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (equalities : ∀ i : Fin (tailChart k).rows.size, (tailChart k).rows[i].sense=0 →
      2*lhs (tailChart k) (physicalVector (tailChart k) F (out F)) i =
        8*(tailChart k).rows[i].rhs.atStep ((k-19)/2 : Nat)) : F.card ≤ squareScore (N k) := by
  apply physical_tail_upper hk F acy (out F) (out_inside F) (cap:=0)
  refine ⟨physical_nonneg _ _ _,forbidden_tail F hk,?_,?_⟩
  · intro i pos
    have z (D : Chart) (b : Int) (ok : tailCheck D b) : ∀ j : Fin D.cols.size, ¬0<price D j := tailZero ok
    have all : ∀ j : Fin (tailChart k).cols.size, ¬0<price (tailChart k) j := by
      apply z (tailChart k) (if k%2=1 then 19 else 20)
      by_cases h : k%2=1 <;> simp [tailChart,h,verified58,verified61]
    exact False.elim (all i pos)
  · intro i
    rcases sense_tail i with ⟨src,_,_⟩|e
    · have p : positional (tailChart k) := by unfold tailChart; split <;> first | exact pos58 | exact pos61
      have idx := of_decide_eq_true p i src
      have r : cornerRow (tailChart k) F ((k-19)/2 : Nat) := by
        unfold tailChart; split <;> first | exact corner58 F hk acy _ | exact corner61 F hk acy _
      obtain ⟨j,hj,h⟩ := r
      exact (Fin.ext (hj.trans idx.symm) : j=i) ▸ h
    · rw [e]; exact equalities i e

private theorem zero19 : repair chart19=0 := by native_decide

theorem feasible19_of_remaining (F : Finset (Site 6)) (acy : (G F).IsAcyclic)
    (eqs : ∀ i : Fin chart19.rows.size, chart19.rows[i].sense=0 → i.val≠1928 →
      2*lhs chart19 (physicalVector chart19 F (out F)) i=8*chart19.rows[i].rhs.atStep 0) :
    Feasible chart19 (physicalVector chart19 F (out F)) 8 0 (8*19^2) := by
  refine ⟨physical_nonneg _ _ _,forbidden19 F,?_,?_⟩
  · intro j p
    have n (i : Fin chart19.cols.size) : 0≤price chart19 i := by unfold price; split <;> first | rfl | exact le_max_left ..
    have h := single_le_sum (s:=univ) (f:=price chart19) (fun i _ => n i) (mem_univ j)
    change _≤repair chart19 at h; rw [zero19] at h; omega
  · intro i
    rcases sense19 i with ⟨src,_,_⟩|e
    · obtain ⟨j,hj,h⟩ := corner19 F acy
      exact (Fin.ext (hj.trans (of_decide_eq_true pos19 i src).symm) : j=i) ▸ h
    · by_cases pos : i.val=1928
      · obtain ⟨j,hj,_,h⟩ := realizedRow19 F acy
        exact (Fin.ext (hj.trans pos.symm) : j=i) ▸ h
      · rw [e]; exact eqs i e pos

end GridGraphs.NoPitch.Budget
