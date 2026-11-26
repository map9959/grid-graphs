import GridGraphs.Constructions.ResidueTwo.LowerTurnCoverageReplay

namespace GridGraphs.ResidueTwoLower.Poly

set_option maxHeartbeats 0 in
/-- All turn implications on the fourteen semi-infinite charts. For a fast
replay load the Lean-generated `LowerTurnKernel:dynlib`; the kernel module
imports only `Init`. -/
theorem charts_closed : ∀ b∈baseList, chartOK (charts b)=true := by
  have all : baseList.all (fun b => chartOK (charts b))=true := by native_decide
  simpa using all

theorem zipper_routes (k : Nat) (hk : 39≤k) :
    let n := 3*k+2
    ∀ r c : Fin (n-1), (holeDual n (marks n)).Reachable (.cell r c) .out := by
  apply zipper_routes_of_chart_table charts _ k hk
  intro b hb
  exact ⟨charts_nonempty _ hb,charts_closed _ hb,table_input_coverage _ hb⟩

theorem squareScore_lower_residue_two (k : Nat) :
    squareScore (3*k+2) ≤ maxPreserved (3*k+2) (3*k+2) :=
  lower_of_turn_closure charts_closed k

end GridGraphs.ResidueTwoLower.Poly
