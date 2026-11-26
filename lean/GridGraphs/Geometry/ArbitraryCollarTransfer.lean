import Mathlib

namespace GridGraphs.ArbitraryCollarTransfer

/-- Pump both sides to residue two with `q=12 (mod 14)`.
Neither solved residue-two endpoint has an exceptional correction. -/
theorem pumpPrice (q : ℤ) (hq : q % 14 = 12) :
    (3*q^2+7*q-(q-5)/7) -
    (3*(q-8)^2+7*(q-8)-(q-13)/7) = 16*(3*q+2)-170 := by
  have h : (q-5)/7 = (q-13)/7 + 2 := by omega
  rw [h]; ring

theorem capOfPump (n s a : ℤ) (h : a+16*(s-n) ≤ 16*s-170) :
    a ≤ 16*n-170 := by omega

/-- `lost` counts withheld owners of redundant template edges. -/
theorem netCrop (n old repaired ten core deficit lost : ℤ)
    (count : old = core + ten)
    (shell : ten ≤ 16*n-170-deficit)
    (refill : repaired ≥ core + 8*(n-12)-40-lost) :
    old-repaired ≤ 8*n-34-deficit+lost := by omega

end GridGraphs.ArbitraryCollarTransfer
