import GridGraphs.Accounting.CarrierLengthBound
import GridGraphs.Constructions.ResidueOne.ResidueOneMax

/-! # The exact seven-by-seven optimum -/

namespace GridGraphs

/-- The carrier-length upper bound meets the residue-one construction at side seven. -/
theorem maxPreserved_seven_seven : maxPreserved 7 7 = 22 := by
  apply Nat.le_antisymm
  · simpa using maxPreserved_le_carrier_length_bound (n := 7) (by omega)
  · simpa using residueOne_le_maxPreserved 2 (by omega)

end GridGraphs
