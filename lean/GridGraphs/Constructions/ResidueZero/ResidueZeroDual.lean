import GridGraphs.Constructions.ResidueZero.ResidueZero
import GridGraphs.Geometry.GridDual

/-!
# Dual structure of the residue-zero construction

This file exposes the row and cap membership facts needed by a frontier proof
of dual connectivity.  In particular, it avoids unfolding the dependent image
defining `uResidueZero` at every dual edge.
-/

namespace GridGraphs

open SimpleGraph

/-- A slot in a phase row gives the corresponding vertex of `uResidueZero`. -/
theorem phase_vertex_mem_uResidueZero (k : Nat) (hk : 7 ≤ k)
    (i : Fin (phaseRows k).length)
    (j : PhaseSlot k ((phaseRows k).get i)) :
    ((⟨i.val + 2, by
        have hi := i.isLt
        have hl := phaseRows_length k hk
        omega⟩,
      ⟨phaseColumn k ((phaseRows k).get i) j,
        phaseColumn_lt
          (phaseRows_parameter_lt k hk _ (List.get_mem (phaseRows k) i)) j⟩) :
      GridVertex (3 * k) (3 * k)) ∈ uResidueZero k hk := by
  rw [uResidueZero, Finset.mem_image]
  refine ⟨Sum.inr (Sum.inr (Sum.inr ⟨i, j⟩)), Finset.mem_univ _, ?_⟩
  rfl

/-- Every vertex in the all-U cap row belongs to the construction. -/
theorem all_cap_mem_uResidueZero (k : Nat) (hk : 7 ≤ k) (c : Nat)
    (hc : c < 3 * k) :
    ((⟨1, by omega⟩, ⟨c, hc⟩) : GridVertex (3 * k) (3 * k)) ∈
      uResidueZero k hk := by
  rw [uResidueZero, Finset.mem_image]
  refine ⟨Sum.inl ⟨c, hc⟩, Finset.mem_univ _, rfl⟩

/-- Every non-leftmost vertex in the penultimate cap row belongs to U. -/
theorem penultimate_cap_mem_uResidueZero (k : Nat) (hk : 7 ≤ k) (c : Nat)
    (hc0 : 0 < c) (hc : c < 3 * k) :
    ((⟨3 * k - 2, by omega⟩, ⟨c, hc⟩) : GridVertex (3 * k) (3 * k)) ∈
      uResidueZero k hk := by
  rw [uResidueZero, Finset.mem_image]
  let j : Fin (3 * k - 1) := ⟨c - 1, by omega⟩
  refine ⟨Sum.inr (Sum.inl j), Finset.mem_univ _, ?_⟩
  apply Prod.ext
  · apply Fin.ext
    simp [residueZeroVertex]
  · apply Fin.ext
    simp [residueZeroVertex, j]
    omega

/-- The unique vertex in the bottom cap row belongs to U. -/
theorem bottom_cap_mem_uResidueZero (k : Nat) (hk : 7 ≤ k) :
    ((⟨3 * k - 1, by omega⟩, ⟨1, by omega⟩) :
      GridVertex (3 * k) (3 * k)) ∈ uResidueZero k hk := by
  rw [uResidueZero, Finset.mem_image]
  refine ⟨Sum.inr (Sum.inr (Sum.inl ⟨0, by omega⟩)), Finset.mem_univ _, rfl⟩

/-- Two U vertices next to each other in a primal row join the faces above and
below that edge. -/
theorem horizontal_uu_dual_cells_adj {N : Nat}
    (U : Finset (GridVertex N N)) (r c : Nat)
    (hr0 : 0 < r) (hr : r < N - 1) (hc : c < N - 1)
    (hl : ((⟨r, by omega⟩, ⟨c, by omega⟩) : GridVertex N N) ∈ U)
    (hright : ((⟨r, by omega⟩, ⟨c + 1, by omega⟩) : GridVertex N N) ∈ U) :
    (uuDualGraph U).Adj (.cell ⟨r - 1, by omega⟩ ⟨c, hc⟩)
      (.cell ⟨r, hr⟩ ⟨c, hc⟩) := by
  let e : HorizontalGridEdge N N := ⟨⟨r, by omega⟩, ⟨c, hc⟩⟩
  refine ⟨?_, Or.inl ⟨e, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩⟩
  · intro h
    injection h with hrow
    have := congrArg Fin.val hrow
    simp at this
    omega
  · simpa [e, horizontalPrimalEndpoints] using hl
  · simpa [e, horizontalPrimalEndpoints] using hright
  · simp [e, horizontalDualEndpoints, hr0.ne']
  · simp [e, horizontalDualEndpoints, show r + 1 ≠ N by omega]

/-- Two vertically adjacent U vertices join the faces on the two sides. -/
theorem vertical_uu_dual_cells_adj {N : Nat}
    (U : Finset (GridVertex N N)) (r c : Nat)
    (hr : r < N - 1) (hc0 : 0 < c) (hc : c < N - 1)
    (ht : ((⟨r, by omega⟩, ⟨c, by omega⟩) : GridVertex N N) ∈ U)
    (hb : ((⟨r + 1, by omega⟩, ⟨c, by omega⟩) : GridVertex N N) ∈ U) :
    (uuDualGraph U).Adj (.cell ⟨r, hr⟩ ⟨c - 1, by omega⟩)
      (.cell ⟨r, hr⟩ ⟨c, hc⟩) := by
  let e : VerticalGridEdge N N := ⟨⟨r, hr⟩, ⟨c, by omega⟩⟩
  refine ⟨?_, Or.inr ⟨e, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩⟩
  · intro h
    injection h with _ hcol
    have := congrArg Fin.val hcol
    simp at this
    omega
  · simpa [e, verticalPrimalEndpoints] using ht
  · simpa [e, verticalPrimalEndpoints] using hb
  · simp [e, verticalDualEndpoints, hc0.ne']
  · simp [e, verticalDualEndpoints, show c + 1 ≠ N by omega]

end GridGraphs
