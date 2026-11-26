import Mathlib

namespace GridGraphs.VerticalCapTariff

/-- Per triple, each empty row cancels a double or pays for the
one-row allowance. The forest of double-row joins has at most `extra` edges. -/
theorem doubleRows (r gain doubles zeros extra : ℤ)
    (balance : gain = doubles - zeros + r)
    (empty : r ≤ zeros) (joins : doubles ≤ extra) : gain ≤ extra := by omega

/-- Bottom holes not covered from the side: at most one per missing
bottom tooth can be covered by a top column, and one per extra rod. -/
theorem uncovered (r teeth extra other : ℤ)
    (isolates : 3*(r-teeth) ≤ (r-teeth)+extra+other) :
    2*(r-teeth) ≤ extra+other := by omega

theorem tariff (r gain teeth extra other : ℤ)
    (ledger : 3*gain = 2*r-teeth-extra-other)
    (doubles : gain ≤ extra) (otherNonnegative : 0 ≤ other)
    (holes : 2*(r-teeth) ≤ extra+other) : 7*gain ≤ 2*r := by omega

theorem deletionCost (r gain deletions : ℤ) (thinned : 7*(gain-deletions) ≤ 2*r)
    (comb : 3*r ≤ 10*gain) : r ≤ 70*deletions := by omega

/-- Projection of the endpoint bill; j counts waived terminal sinks. -/
theorem endpointPrice (r gain bill j : ℤ)
    (ledger : 4*gain = 2*r+2*j-bill) (windows : 4*r ≤ 5*(bill+j)) :
    20*gain ≤ 6*r+15*j := by omega

theorem wiredEndpointPrice (r gain bill : ℤ)
    (ledger : 4*gain = 2*r-bill) (windows : 4*r ≤ 5*bill) :
    10*gain ≤ 3*r := by omega

end GridGraphs.VerticalCapTariff
