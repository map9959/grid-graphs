import Mathlib

namespace GridGraphs.SparseSpokeExchange

/-- `rank` counts independent component joins, not the number of
nonempty projected tooth positions. -/
theorem repairedGain (before after holes rank wing clip deleted : ℤ)
    (replay : after = before+holes+wing-clip-deleted)
    (cycles : deleted ≤ holes-rank) :
    before+rank+wing-clip ≤ after := by omega

theorem maxSparse (rank wing u₁ u₂ : ℤ)
    (maximal : rank+wing ≤ 0) (hr : 0 ≤ rank) (hw : 0 ≤ wing)
    (h₁ : u₁-2 ≤ wing) (h₂ : u₂-2 ≤ wing) :
    rank=0 ∧ u₁≤2 ∧ u₂≤2 := by omega

/-- Even when holes are two apart, each clipped inward mark gives
two isolated contact sites. At most two marks per wing are lost. -/
theorem nonadjacent (before after rank wing clip : ℤ)
    (gain : before+rank+wing-clip ≤ after)
    (isolated : 2*clip ≤ rank) (hc : 0≤clip) (hw : -4 ≤ wing) :
    before ≤ after+4 := by omega

theorem gapTest (k r original repaired gain : ℤ)
    (change : original+gain ≤ repaired)
    (sector : 30*(repaired-1) ≤ k-26+3*r)
    (enough : k-26+3*r < 30*gain) : original ≤ 0 := by omega

theorem clusters (M normalized comb added deleted g : ℤ)
    (chosen : added ≤ g+4) (cycleRepairs : deleted ≤ 6*added)
    (gain : M+added-deleted ≤ normalized)
    (upper : normalized ≤ comb+4) : M ≤ comb+5*g+24 := by omega

end GridGraphs.SparseSpokeExchange
