import GridGraphs.Constructions.ResidueTwo.LowerTurn23High

namespace GridGraphs.ResidueTwoLower.Poly

abbrev chart23 := input23

theorem chart23_size : chart23.size=11 := by native_decide

-- A single closed replay checks Presburger regions, not finite-width boards.
set_option maxHeartbeats 0 in
theorem chart23_closed : chartOK chart23=true := by
  apply (chartOK_iff _).mpr
  intro s hs
  rw [chart23_size] at hs
  interval_cases s
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · exact layer23_eight
  · exact layer23_nine
  · exact terminal23

theorem routes23 (t : Nat) (r c : Fin ((23+42*t)-1)) :
    (holeDual (23+42*t) (marks (23+42*t))).Reachable (.cell r c) .out :=
  routes_of_chart _ (by rw [show chart23.size=11 from chart23_size]; decide)
    chart23_closed (forced23 t) r c

end GridGraphs.ResidueTwoLower.Poly
