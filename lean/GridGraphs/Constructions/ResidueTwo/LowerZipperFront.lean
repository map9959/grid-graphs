import GridGraphs.Constructions.ResidueTwo.LowerZipperPieces

namespace GridGraphs.ResidueTwoLower

/-- Physical column predicates in an advancing row, before the optional
one-site wire repair. -/
def advance (k a j : Nat) := leftRail (3*a) j ||
  rightRail (3*k+1-3*a) j ||
  (j%3 == 2 && 3*a+5 ≤ j && j < 3*k+1-3*a-4)

theorem advance_count {a k : Nat} (h : 2*a+2 ≤ k) :
    rowCount (advance k a) (3*k+2) = k := by
  let n := 3*k+2
  let r := 3*k+1-3*a
  let pitch (lo hi d j : Nat) := decide (lo ≤ j) && decide (j<hi) && j%3 == d
  have e : rowCount (advance k a) n =
      rowCount (fun j => (pitch 0 (3*a+1) 0 j || pitch r n 1 j) ||
        pitch (3*a+5) (r-4) 2 j) n := by
    apply rowCount_congr
    intro j hj
    apply Bool.eq_iff_iff.mpr
    simp [advance,leftRail,rightRail,pitch,n,r] at *
    omega
  rw [e,rowCount_or,rowCount_or]
  · have L := rowCount_pitch 0 (3*a+1) 0 n (by omega) (by omega)
    have R := rowCount_pitch r n 1 n (by dsimp [r,n]; omega) (by omega)
    by_cases sep : 3*a+5 ≤ r-4
    · have M := rowCount_pitch (3*a+5) (r-4) 2 n sep (by omega)
      change rowCount (fun j => _) n + _ + _ = _
      dsimp [pitch] at *
      rw [L,R,M]
      dsimp [r,n]; omega
    · have M : rowCount (pitch (3*a+5) (r-4) 2) n = 0 := by
        unfold rowCount
        simp [Finset.filter_eq_empty_iff,pitch]
        omega
      rw [M]; dsimp [pitch]; rw [L,R]; dsimp [r,n] at *; omega
  · intro j hj
    simp [pitch]; omega
  · intro j hj
    simp [pitch]; omega

end GridGraphs.ResidueTwoLower
