import GridGraphs.Results.SquareFormulaFanResidual

namespace GridGraphs

/-- The seed and the physical halo are supplied by the same putative
exceptional forest. The last north-strip cut excludes that forest. -/
theorem exactSquareFormula : ExactSquareFormula := by
  apply exactSquareFormula_of_pending_fans
  intro u q mem
  rw [ResidueTwoUpper.Exceptional.OneGap.pendingFanIndices_empty] at mem
  exact (List.not_mem_nil mem).elim

theorem maxPreserved_square_exact {n : Nat} (hn : 0<n) :
    maxPreserved n n=squareScore n := exactSquareFormula n hn

theorem maxPreserved_161_exact : maxPreserved 161 161=squareScore 161 :=
  maxPreserved_square_exact (by decide)

end GridGraphs
