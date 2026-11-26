import Mathlib

namespace GridGraphs.CropEndCoupling

/-- Exterior donor edges form a forest before the optional end ports.
Rank of their union can be computed in either order. -/
theorem portGain (edges rankAfterPorts oldPorts allPorts kept rankKeptAfterPorts
    newPorts : ℤ)
    (old : edges + oldPorts = allPorts + rankAfterPorts)
    (change : kept + newPorts = allPorts + rankKeptAfterPorts) :
    newPorts-oldPorts = (edges-rankAfterPorts)-(kept-rankKeptAfterPorts) := by omega

/-- Pay once per lost foot and once per break between surviving doubles. -/
theorem railInterval (doubles normal teeth lostFeet otherCuts gain : ℤ)
    (slots : normal ≤ teeth + doubles)
    (disjointCuts : doubles - lostFeet ≤ 1 + otherCuts)
    (net : gain ≤ normal - lostFeet - otherCuts) : gain ≤ teeth+1 := by omega

end GridGraphs.CropEndCoupling
