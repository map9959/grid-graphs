import GridGraphs.Constructions.ResidueTwo.LowerTurnAll

namespace GridGraphs

theorem squareScore_lower_residue_two (k : Nat) :
    squareScore (3*k+2) ≤ maxPreserved (3*k+2) (3*k+2) :=
  ResidueTwoLower.Poly.squareScore_lower_residue_two k

namespace ResidueTwoLower

/-- Exact type of the `zipperRoutes` premise in `SquareFormulaAssembly`. -/
theorem blocked_zipper_routes (k : Nat) (hk : 39≤k) :
    let n := 3*k+2
    ∀ r c : Fin (n-1), r.val=0 ∨ ¬climbs n (marks n) r c →
      (holeDual n (marks n)).Reachable (.cell r c) .out :=
  fun r c _ => Poly.zipper_routes k hk r c

end ResidueTwoLower
end GridGraphs
