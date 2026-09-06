import GridGraphs.Constructions.ResidueZero.ResidueZeroPersistent
import GridGraphs.Constructions.ResidueZero.ResidueZeroWord
import GridGraphs.Constructions.ResidueZero.ResidueZeroFrontier
import GridGraphs.Constructions.ResidueZero.ResidueZeroCaps

/-!
# Endpoint rows for persistent residue-zero geometry

The top two face rows and the face row below the appended `R_k` are strict
interior rows.  Consequently a persistent certificate at the successor width
supplies exactly the `topRows` and `appendedRow` fields of
`PersistentResidueZeroStepGeometry`.
-/

namespace GridGraphs

open SimpleGraph

/-- The top two endpoint rows of a successor certificate give the `topRows`
field of the persistent step geometry. -/
theorem persistentResidueZeroStepGeometry_topRows
    (k : Nat) (hk : 7 ≤ k)
    (h : PersistentResidueZeroCertificate (k + 1) (by omega)) :
    ∀ (r c : Fin (3 * (k + 1) - 1)),
      (r.val = 1 ∨ r.val = 2) →
      (persistentResidueZeroGraph (k + 1) (by omega)).Reachable (r, c)
        (residueZeroAnchorCoord (k + 1) (by omega)) := by
  intro r c hr
  exact h r (by omega) (by omega) c

/-- The face row below the appended `R_k` is strict interior, so a successor
certificate gives the `appendedRow` field of the persistent step geometry. -/
theorem persistentResidueZeroStepGeometry_appendedRow
    (k : Nat) (hk : 7 ≤ k)
    (h : PersistentResidueZeroCertificate (k + 1) (by omega)) :
    ∀ c : Fin (3 * (k + 1) - 1),
      (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
        (⟨3 * k, by omega⟩, c)
        (residueZeroAnchorCoord (k + 1) (by omega)) := by
  intro c
  apply h ⟨3 * k, by omega⟩
  · simp
    omega
  · simp
    omega

end GridGraphs
