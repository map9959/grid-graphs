import GridGraphs.Constructions.ResidueTwo.LowerZipper
import GridGraphs.Constructions.ResidueTwo.ResidueTwoLowerScores
import GridGraphs.Constructions.ResidueTwo.ResidueTwoAffineMax
import GridGraphs.Constructions.ResidueTwo.LowerZipperPhysicalCount
import GridGraphs.Constructions.ResidueTwo.LowerZipperRoutes
import GridGraphs.Constructions.ResidueTwo.LowerTurnBoundary

namespace GridGraphs.ResidueTwoLower

/-- The first two complete periods of the fourteen residue-two tails,
including the isolated base masks preceding their starting sides. -/
private theorem replay_two_periods :
    ∀ i : Fin 32, let n := 23+3*i.val
      replay n (squareScore n) (marks n) = true := by native_decide

/-- An unconditional lower bound in the actual square graph, through side 116. -/
theorem squareScore_lower_through_116 (k : Nat) (hk : k ≤ 38) :
    squareScore (3*k+2) ≤ maxPreserved (3*k+2) (3*k+2) := by
  by_cases hs : k ≤ 6
  · interval_cases k
    · exact (exactSquareFormula_through_five (n := 2) (by decide) (by decide)).ge
    · exact (exactSquareFormula_through_five (n := 5) (by decide) (by decide)).ge
    · exact twentySeven_le_maxPreserved_eight_eight
    · exact fortyNine_le_maxPreserved_eleven_eleven
    · exact seventySeven_le_maxPreserved_fourteen_fourteen
    · exact oneHundredTen_le_maxPreserved_seventeen_seventeen
    · exact oneHundredFifty_le_maxPreserved_twenty_twenty
  · let i : Fin 32 := ⟨k-7,by omega⟩
    have h := replay_two_periods i
    dsimp only at h
    rw [show 23+3*i.val=3*k+2 by dsimp [i]; omega] at h
    exact replay_sound (by omega) h

/-- The older all-width affine trees give this explicit bound on any remaining
deficit, even without the sharp zipper transport theorem. -/
theorem squareScore_sub_affine_gap_lower (k : Nat) (hk : 6 ≤ k) :
    squareScore (3*k+2) - ((k-5) - (k-5)/7 - (if k%14=11 then 1 else 0))
      ≤ maxPreserved (3*k+2) (3*k+2) := by
  apply Nat.le_trans _ (residueTwoAffine_uniform_le_maxPreserved k (by omega))
  rw [squareScore_three_mul_add_two k hk]
  split <;> omega

/-- Uniform integration point: exact cardinality of the specified zipper
marks and a route from every bounded face to the exterior across unmarked
edges suffice. No computation of BFS distances is needed in a symbolic
proof of these two tail obligations. -/
theorem squareScore_lower_of_zipper_tail
    (count : ∀ k : Nat, 39 ≤ k → let n := 3*k+2
      (Finset.univ.filter (fun v : GridVertex n n => marks n v.1 v.2)).card = squareScore n)
    (route : ∀ k : Nat, 39 ≤ k → let n := 3*k+2
      ∀ r c, (uuDualGraph (Finset.univ.filter
        (fun v : GridVertex n n => marks n v.1 v.2 = false))).Reachable (.cell r c) .out)
    (k : Nat) : squareScore (3*k+2) ≤ maxPreserved (3*k+2) (3*k+2) := by
  by_cases h : k ≤ 38
  · exact squareScore_lower_through_116 k h
  let n := 3*k+2
  let U := Finset.univ.filter (fun v : GridVertex n n => marks n v.1 v.2 = false)
  have path (x : GridFace n n) : (uuDualGraph U).Reachable x .out := by
    cases x with
    | out => exact .refl _
    | cell r c => exact route k (by omega) r c
  let : Nonempty (GridFace n n) := ⟨.out⟩
  have conn : (uuDualGraph U).Connected := ⟨fun a b => (path a).trans (path b).symm⟩
  have e : Finset.univ \ U = Finset.univ.filter
      (fun v : GridVertex n n => marks n v.1 v.2) := by ext; simp [U]
  rw [← count k (by omega), ← e]
  exact compl_card_le_maxPreserved_of_uuDual_connected
    (m := n) (n := n) (by dsimp [n]; omega) (by dsimp [n]; omega) U conn

/-- With all-width counting discharged, only physical dual reachability
remains in the tail for the sharp residue-two lower bound. -/
theorem squareScore_lower_of_zipper_routes
    (route : ∀ k : Nat, 39 ≤ k → let n := 3*k+2
      ∀ r c, (uuDualGraph (Finset.univ.filter
        (fun v : GridVertex n n => marks n v.1 v.2 = false))).Reachable (.cell r c) .out)
    (k : Nat) : squareScore (3*k+2) ≤ maxPreserved (3*k+2) (3*k+2) :=
  squareScore_lower_of_zipper_tail marks_card_eq_squareScore route k

/-- Faces with a verified local climb can be omitted from the remaining
route obligations. -/
theorem squareScore_lower_of_blocked_routes
    (blocked : ∀ k : Nat, 39 ≤ k → let n := 3*k+2
      ∀ r c : Fin (n-1), r.val=0 ∨ ¬ climbs n (marks n) r c →
        (holeDual n (marks n)).Reachable (.cell r c) .out)
    (k : Nat) : squareScore (3*k+2) ≤ maxPreserved (3*k+2) (3*k+2) :=
  squareScore_lower_of_zipper_routes (fun k hk => routes_of_blocked (blocked k hk)) k

/-- Integration of directed primal turn certificates. Produces the physical
dual routes, including those on the top row and at the blocked tips. -/
theorem zipper_routes_of_turn_bounds (k : Nat) (rank : Turn.Pt → Turn.Dir → Nat)
    (straight : ∀ v d, Turn.forced (3*k+2) (marks (3*k+2)) v d →
      Turn.forced (3*k+2) (marks (3*k+2)) (Turn.advance v d) d →
      rank (Turn.advance v d) d ≤ rank v d)
    (bend : ∀ v d e, e=Turn.turnL d ∨ e=Turn.turnR d →
      Turn.forced (3*k+2) (marks (3*k+2)) v d →
      Turn.forced (3*k+2) (marks (3*k+2)) (Turn.advance v d) e →
      rank (Turn.advance v d) e < rank v d) (r c : Fin (3*k+2-1)) :
    (holeDual (3*k+2) (marks (3*k+2))).Reachable (.cell r c) .out :=
  Turn.routes_of_turn_rank _ rank straight bend r c

end GridGraphs.ResidueTwoLower
