import GridGraphs.Accounting.BoundaryStratifiedCarrierBound
import GridGraphs.Constructions.ResidueOne.ResidueOneMax

/-! # The exact ten-by-ten optimum -/

namespace GridGraphs

/-- Boundary stratification closes the residue-one upper bound at side ten. -/
theorem maxPreserved_ten_ten : maxPreserved 10 10 = 42 := by
  apply Nat.le_antisymm
  · simpa using maxPreserved_le_boundary_stratified_carrier_bound (n := 10) (by omega)
  · simpa using residueOne_le_maxPreserved 3 (by omega)

end GridGraphs
