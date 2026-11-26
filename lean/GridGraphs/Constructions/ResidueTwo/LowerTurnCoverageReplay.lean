import GridGraphs.Constructions.ResidueTwo.LowerTurnTable

namespace GridGraphs.ResidueTwoLower.Poly

/-- Closed checks that every actual forced physical edge lies in its
chart's input layer, simultaneously for the entire width progression. -/
theorem table_input_coverage : ∀ b∈baseList,
    coverOK (charts b) (widthExpr b) (physRegion b)=true := by
  have closed : baseList.all (fun b => coverOK (charts b) (widthExpr b) (physRegion b))=true := by
    native_decide
  simpa using closed

theorem lower_of_turn_closure (closed : ∀ b∈baseList, chartOK (charts b)=true)
    (k : Nat) : squareScore (3*k+2) ≤ maxPreserved (3*k+2) (3*k+2) := by
  apply lower_of_chart_table charts _ k
  intro b hb
  exact ⟨charts_nonempty b hb,closed b hb,table_input_coverage b hb⟩

end GridGraphs.ResidueTwoLower.Poly
