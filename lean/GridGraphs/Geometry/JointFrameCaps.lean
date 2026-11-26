import Mathlib

namespace GridGraphs.JointFrameCaps

/-- q=p+u terminal labels per end, with u additional cut spokes
paired directly. Core classes C are counted on the physical end teeth. -/
theorem rankPrice (p u q C a b excess : ℤ)
    (hq : q = p+u)
    (rank : 2*q+1 ≤ a+b+C+u)
    (plain : excess ≤ 0) (priced : excess+C ≤ p) :
    10*excess ≤ 7*(a+b-q-1) := by omega

theorem connectedEnd (q classes marks weighted excess : ℤ)
    (limited : classes ≤ q) (cost : 10*marks+7*classes ≤ weighted)
    (rank : excess ≤ classes-q) :
    marks+excess ≤ (weighted-7*q)/10 := by omega

/-- Increasing side by 30 adds ten terminal columns and thirty core
rows. At end depths nine the cap remainder increases by at most 253 marks. -/
theorem widthPump (k : ℤ) :
    (3*(k+10)^2+5*(k+10)+(3*(k+10)-13)/10) -
        (3*k^2+5*k+(3*k-13)/10) =
    ((3*k+1-18+30)*(k-1+10) - (3*k+1-18)*(k-1)) + 253 := by
  have h : (3*(k+10)-13)/10 = (3*k-13)/10+3 := by omega
  rw [h]; ring

end GridGraphs.JointFrameCaps
