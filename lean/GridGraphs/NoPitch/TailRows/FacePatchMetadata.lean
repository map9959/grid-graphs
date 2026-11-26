import GridGraphs.NoPitch.TailRows.FacePatchChecks

namespace GridGraphs.NoPitch.TailRows.FacePatch
open GridGraphs.NoPitch.Dual
attribute [local irreducible] chart58 chart61

@[noinline] def scanInfo (D : Chart) (tags : Array Nat) :=
  let s := tagged tags
  (List.range D.rows.size).filter s |>.length |> fun n =>
  (n,decide (∀ i : Fin D.rows.size, s i → D.rows[i].sense=0 ∧ D.rows[i].rhs=⟨0,0,0⟩))
def rowInfo (D : Chart) := scanInfo D (supportMasks D)
theorem metadata : rowInfo chart58=(369,true) ∧ rowInfo chart61=(363,true) := by native_decide

theorem row_shape {k : Nat} (i : Fin (TailCoverage.tailChart k).rows.size)
    (sel : (supportMasks (TailCoverage.tailChart k))[i.val]! = 6) :
    (TailCoverage.tailChart k).rows[i].sense=0 ∧ (TailCoverage.tailChart k).rows[i].rhs=⟨0,0,0⟩ := by
  have h : (rowInfo (TailCoverage.tailChart k)).2=true := by
    by_cases odd : k%2=1 <;> simp [TailCoverage.tailChart,odd,metadata.1,metadata.2]
  exact of_decide_eq_true h i (beq_iff_eq.mpr sel)

end GridGraphs.NoPitch.TailRows.FacePatch
