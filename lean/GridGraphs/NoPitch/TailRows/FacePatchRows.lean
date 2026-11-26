import GridGraphs.NoPitch.TailRows.FacePatchMetadata
import GridGraphs.NoPitch.TailRows.FacePatchLift
import GridGraphs.NoPitch.TailRows.FacePatchReplay

/-! The face key sees nine ordered pairs of boundary bands. A patch key
also sees fine diagonal labels, so one cannot simply replace its position
by the face representative. At each parity base the decoded scan checks
that the selected, units-weighted patch charge agrees with that of the
representative child, or vanishes on a seam. `patch_rep` transports the
full patch key and `patch_class` transports its child class. The sums in
`lifted` are over the original forest, never over base-board frequencies. -/

namespace GridGraphs.NoPitch.TailRows.FacePatch
open PitchCut Budget Keys TailCoverage GridGraphs.NoPitch.Dual
attribute [local irreducible] chart58 chart61

private theorem replay (k : Nat) : cert (tailChart k) (if k%2=1 then 19 else 20) := by
  by_cases odd : k%2=1 <;> simp [tailChart,odd,base58,base61]

/-- The global skeleton face atom and every physical patch have an actual
column in the parity chart (not just a default-zero projected charge). -/
theorem physical_catalogue {k} (hk : 19≤k) (F : Finset (Site k)) (acy : (G F).IsAcyclic) :
    (∀ p, (locate (tailChart k) (index (tailChart k)) (face F p)).isSome) ∧
    (∀ p, (locate (tailChart k) (index (tailChart k)) (patch F p)).isSome) :=
  catalogue_of_cert hk _ (replay k) F acy

/-- The entire tag-6 block on the physical vector, at every tail width. -/
theorem face_patch_tail {k} (hk : 19≤k) (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (o : Site k → Option (Fin 4)) (i : Fin (tailChart k).rows.size)
    (sel : (supportMasks (tailChart k))[i.val]! = 6) : lhs (tailChart k) (physicalVector (tailChart k) F o) i=0 :=
  lifted hk _ (replay k) F acy o i (beq_iff_eq.mpr sel)

theorem physical_patch_rows {k} (hk : 19≤k) (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (o : Site k → Option (Fin 4)) (i : Fin (tailChart k).rows.size)
    (sel : (supportMasks (tailChart k))[i.val]! = 6) (t : Int) :
    rowHolds (tailChart k).rows[i].sense (2*lhs (tailChart k) (physicalVector (tailChart k) F o) i)
      (8*(tailChart k).rows[i].rhs.atStep t) := by
  obtain ⟨sense,rhs⟩ := row_shape i sel
  rw [face_patch_tail hk F acy o i sel,sense,rhs]; simp [rowHolds,Poly.atStep]

end GridGraphs.NoPitch.TailRows.FacePatch
