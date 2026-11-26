import Mathlib

namespace GridGraphs.EndBandRank

/-- The side surgery returns actual marks before the end exchange.
Compulsory spokes may require paid exterior deletions. -/
theorem combined (original aligned comb S old teeth free joins cuts : ℤ)
    (gain : original + S - old + teeth + free + joins - cuts ≤ aligned)
    (frame : aligned ≤ comb) :
    original ≤ comb + old + cuts - teeth - free - joins - S := by omega

theorem emptyBacking (original comb S old teeth pairRank : ℤ)
    (exchange : original ≤ comb + old - 2*teeth - pairRank - S)
    (enough : old ≤ 2*teeth + pairRank + S) : original ≤ comb := by omega

/-- Repeating five side paths at spacings of three subtracts only a
constant from the comb, even though the three-row alignment cost can
grow linearly. -/
theorem fiveRims (k : ℤ) :
    3*(k-10)^2 + 5*(k-10) + (3*(k-10)-13)/10
      + 20*(3*k+1)-285 = 3*k^2+5*k+(3*k-13)/10-18 := by
  have h : (3*(k-10)-13)/10 = (3*k-13)/10-3 := by omega
  rw [h]; ring

end GridGraphs.EndBandRank
