import Mathlib

namespace GridGraphs.CoreBoundaryEnvelope

/-- The marked-run/forced-component ledger with visible boundary classes. -/
theorem portLedger (I r c m D classes runs : ℤ)
    (identity : 3*I+r+c=m*m+D) (hc : classes ≤ c) (hr : runs ≤ r) :
    3*I ≤ m*m+D-classes-runs := by omega

theorem splitWitnesses (b extraRuns extraComps : ℤ)
    (hi : 0 ≤ extraComps) (cover : 2*b ≤ 3*extraRuns+extraComps) :
    (2*b+2)/3 ≤ extraRuns+extraComps := by omega

/-- Straight 10-layer strip: exterior rank pays for the backing bits. -/
theorem highPiece (T L D A O r c touch ends outer : ℤ)
    (ledger : 3*T = 10*L + A + outer + ends - r - c)
    (distinct : O ≤ r) (used : touch ≤ c) (h : outer ≤ L) :
    3*T+D-(A+D-O-touch) ≤ 11*L+ends := by omega

/-- For the 2n/3 split, S=(7n-124)/3, qL=qH=3; retain the
actual capacity correction r >= (M-T)/(n-20). -/
theorem mixedEnvelope (M n : ℤ) (hn : 181 ≤ n)
    (env : (63*(n-20)+21)*M ≤
      (21*n^2+56*n+3157)*(n-20)+21*(16*n-170)) :
    90*M ≤ 30*n^2+70*n+4860 := by
  by_contra! h
  have hp : 0 < 63*(n-20)+21 := by omega
  have H := mul_lt_mul_of_pos_left h hp
  nlinarith

theorem belowComb (M k : ℤ) (hk : 60 ≤ k)
    (bound : 90*M ≤ 30*(3*k+1)^2+70*(3*k+1)+4860) :
    M ≤ 3*k^2+5*k+(3*k-13)/10 := by
  have h : 3*k-22 ≤ 10*((3*k-13)/10) := by omega
  nlinarith

end GridGraphs.CoreBoundaryEnvelope
