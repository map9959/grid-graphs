import Mathlib

namespace GridGraphs.DenseCollarPrice

def C (k : ℤ) := 3*k^2 + 5*k + (3*k-13)/10

/-- After the eight cuts are contracted there are only 24 port vertices. -/
theorem capNine (n corner sides rc rs : ℤ) (hc : 3*corner ≤ 432+2*rc)
    (hs : 3*sides ≤ 36*(n-20)-24+2*rs) (forest : rc+rs ≤ 23) :
    sides+corner ≤ 12*n-89 := by omega

theorem capFourApart (n corner sides bad rc rs : ℤ) (hc : 9*corner ≤ 1296+6*rc)
    (hs : 9*sides+bad ≤ 108*(n-20)-60+6*rs) (forest : rc+rs ≤ 23) :
    9*(sides+corner)+bad ≤ 9*(12*n-89)+15 := by omega

theorem stepBudget (k : ℤ) : 12*(3*k+1)-89 ≤ C k-C (k-6) := by
  have h : C k-C (k-6) = 12*(3*k+1)-90+((3*k-13)/10-(3*k-31)/10) := by
    unfold C
    rw [show 3*(k-6)-13 = 3*k-31 by ring]
    ring
  omega

/-- Opening one pitch slice duplicates three terminal groups, permitting
at most two independent identifications in the opened forest. -/
theorem oneCut (m T r : ℤ) (rank : r ≤ 2)
    (sweep : 3*(T-3)-9*(4*m-1)-2*r ≤ 451) : T ≤ 12*m+151 := by omega

/-- The inside and outside refills keep different unchanged forests. -/
theorem twoRefills (original outer inner rim eo ei upperA upperS : ℤ)
    (count : original=outer+rim+inner)
    (ext : outer+eo≤upperA) (inside : inner+ei≤upperS) :
    original ≤ upperA+upperS-(eo+ei-rim) := by omega

theorem rankPrice (M R band I c m D a h : ℤ)
    (partition : M=R+band+I) (transfer : 3*band ≤ a+h+c-1)
    (ledger : 3*I+c ≤ m*m+D) : 3*M ≤ 3*R+a+h-1+m*m+D := by omega

def offBar (k : ℤ) := 3*k^2+6*k+1-(31*(k+1)+69)/70-(3*(k+1)+9)/10

theorem offPhaseBar (k : ℤ) (hk : 34 ≤ k) : offBar k ≤ C k := by
  unfold C offBar
  by_cases large : 70 ≤ k
  · omega
  · have stop : k ≤ 69 := by omega
    interval_cases k <;> norm_num

theorem offPhaseHoles (k h breaks M : ℤ) (target : C k < M)
    (repair : M ≤ offBar k + h + breaks) (gaps : 2*breaks ≤ h) :
    k-34 ≤ 35*h := by
  unfold C at target
  unfold offBar at repair
  omega

end GridGraphs.DenseCollarPrice
