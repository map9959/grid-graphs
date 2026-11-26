import GridGraphs.ResidueTwoUpper.StencilBoundary

/-! Upper-side integration with the corrected square score. After the
period-three stencil only side eleven and `35+42u` require exclusions. -/
namespace GridGraphs.ResidueTwoUpper.Stencil

theorem upper_of_remaining_at
    (eleven : maxPreserved 11 11 ≤ 49)
    (k : Nat) (hk : 3≤k)
    (exceptional : ∀ u : Nat, 3*k+2=35+42*u → ¬SquareMaskScore (35+42*u) (440+1020*u+588*u^2)) :
    maxPreserved (3*k+2) (3*k+2) ≤ squareScore (3*k+2) := by
  by_cases tail : 6≤k
  · by_cases bad : k%14=11
    · let u := k/14
      have ku : k=11+14*u := by dsimp [u]; omega
      have side : 3*k+2=35+42*u := by omega
      have pred : squareScore (3*k+2)+1=440+1020*u+588*u^2 := by
        rw [squareScore_three_mul_add_two k tail,if_pos bad]
        have div : (k-5)/7=2*u := by omega
        rw [div,ku]; ring_nf; omega
      have no := exceptional u side
      rw [squareMaskScore_iff_le (by omega)] at no
      rw [←side,←pred] at no
      omega
    · exact maxPreserved_le_squareScore tail bad
  · interval_cases k
    · exact eleven
    · exact fourteen_exact.le
    · exact seventeen_exact.le

theorem upper_of_remaining
    (eleven : maxPreserved 11 11 ≤ 49)
    (exceptional : ∀ u : Nat, ¬SquareMaskScore (35+42*u) (440+1020*u+588*u^2))
    (k : Nat) (hk : 3≤k) :
    maxPreserved (3*k+2) (3*k+2) ≤ squareScore (3*k+2) :=
  upper_of_remaining_at eleven k hk (fun u _ => exceptional u)

end GridGraphs.ResidueTwoUpper.Stencil
