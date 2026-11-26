import GridGraphs.Constructions.ResidueTwo.LowerTurnFamilies
import GridGraphs.Constructions.ResidueTwo.LowerTurnBase23Cover

namespace GridGraphs.ResidueTwoLower.Poly

/-- Coordinates are never stored. Each line encodes the region of source
sites for one layer and direction, with the width parameter left free. -/
def charts : Nat → Chart
  | 23 => input23
  | 35 => (decode (include_str "LowerTurnData/base35.turns")).getD #[]
  | 38 => (decode (include_str "LowerTurnData/base38.turns")).getD #[]
  | 41 => (decode (include_str "LowerTurnData/base41.turns")).getD #[]
  | 44 => (decode (include_str "LowerTurnData/base44.turns")).getD #[]
  | 47 => (decode (include_str "LowerTurnData/base47.turns")).getD #[]
  | 50 => (decode (include_str "LowerTurnData/base50.turns")).getD #[]
  | 53 => (decode (include_str "LowerTurnData/base53.turns")).getD #[]
  | 56 => (decode (include_str "LowerTurnData/base56.turns")).getD #[]
  | 59 => (decode (include_str "LowerTurnData/base59.turns")).getD #[]
  | 62 => (decode (include_str "LowerTurnData/base62.turns")).getD #[]
  | 68 => (decode (include_str "LowerTurnData/base68.turns")).getD #[]
  | 71 => (decode (include_str "LowerTurnData/base71.turns")).getD #[]
  | 74 => (decode (include_str "LowerTurnData/base74.turns")).getD #[]
  | _ => #[]

theorem charts_nonempty : ∀ b ∈ baseList, 0<(charts b).size := by
  have h : baseList.all (fun b => 0<(charts b).size) = true := by native_decide
  simpa using h

/-- This is a *finite* replay obligation. It implies routes at arbitrarily
large widths by specialization of the parametric regions, not interpolation. -/
def allChecks := baseList.all (fun b => chartOK (charts b) &&
  coverOK (charts b) (widthExpr b) (physRegion b))

theorem zipper_routes_of_allChecks (ok : allChecks=true) (k : Nat) (hk : 39≤k) :
    let n := 3*k+2
    ∀ r c : Fin (n-1), (holeDual n (marks n)).Reachable (.cell r c) .out := by
  apply zipper_routes_of_chart_table charts _ k hk
  intro b hb
  refine ⟨charts_nonempty b hb,?_⟩
  simpa only [Bool.and_eq_true] using ((List.all_eq_true.mp ok) b hb)

theorem residue_two_lower_of_allChecks (ok : allChecks=true) (k : Nat) :
    squareScore (3*k+2) ≤ maxPreserved (3*k+2) (3*k+2) :=
  squareScore_lower_of_zipper_routes (zipper_routes_of_allChecks ok) k

end GridGraphs.ResidueTwoLower.Poly
