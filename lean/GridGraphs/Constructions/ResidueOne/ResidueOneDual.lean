import GridGraphs.Constructions.ResidueOne.ResidueOne
import GridGraphs.Geometry.GridDual

/-!
# Dual connectivity of the residue-one construction

The parent of a bounded face is chosen as follows.  Faces in rows congruent to
one move right, faces in rows congruent to zero move down (after moving column
zero to column one), and faces in rows congruent to two move up (with the
analogous column-zero exception).  The right edge of every residue-one row is
joined to the unbounded face.
-/

namespace GridGraphs

open SimpleGraph

@[simp] lemma mem_uResidueOne_iff {k : Nat}
    {v : GridVertex (3 * k + 1) (3 * k + 1)} :
    v ∈ uResidueOne k ↔ isInUResidueOne k v.1 v.2 := by
  simp [uResidueOne]

private lemma horizontal_dual_cells_adj {N : Nat}
    (U : Finset (GridVertex N N)) (R C : Nat)
    (hR0 : 0 < R) (hR : R < N - 1) (hC : C < N - 1)
    (hleft : ((⟨R, by omega⟩, ⟨C, by omega⟩) : GridVertex N N) ∈ U)
    (hright : ((⟨R, by omega⟩, ⟨C + 1, by omega⟩) : GridVertex N N) ∈ U) :
    (uuDualGraph U).Adj
      (.cell ⟨R - 1, by omega⟩ ⟨C, hC⟩)
      (.cell ⟨R, hR⟩ ⟨C, hC⟩) := by
  let e : HorizontalGridEdge N N := ⟨⟨R, by omega⟩, ⟨C, hC⟩⟩
  refine ⟨?_, Or.inl ⟨e, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩⟩
  · intro h
    injection h with hr
    have := congrArg Fin.val hr
    simp at this
    omega
  · simpa [e, horizontalPrimalEndpoints] using hleft
  · simpa [e, horizontalPrimalEndpoints] using hright
  · simp [e, horizontalDualEndpoints, hR0.ne']
  · simp [e, horizontalDualEndpoints, show R + 1 ≠ N by omega]

private lemma vertical_dual_cells_adj {N : Nat}
    (U : Finset (GridVertex N N)) (R C : Nat)
    (hR : R < N - 1) (hC0 : 0 < C) (hC : C < N - 1)
    (htop : ((⟨R, by omega⟩, ⟨C, by omega⟩) : GridVertex N N) ∈ U)
    (hbottom : ((⟨R + 1, by omega⟩, ⟨C, by omega⟩) : GridVertex N N) ∈ U) :
    (uuDualGraph U).Adj
      (.cell ⟨R, hR⟩ ⟨C - 1, by omega⟩)
      (.cell ⟨R, hR⟩ ⟨C, hC⟩) := by
  let e : VerticalGridEdge N N := ⟨⟨R, hR⟩, ⟨C, by omega⟩⟩
  refine ⟨?_, Or.inr ⟨e, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩⟩
  · intro h
    injection h with _ hc
    have := congrArg Fin.val hc
    simp at this
    omega
  · simpa [e, verticalPrimalEndpoints] using htop
  · simpa [e, verticalPrimalEndpoints] using hbottom
  · simp [e, verticalDualEndpoints, hC0.ne']
  · simp [e, verticalDualEndpoints, show C + 1 ≠ N by omega]

private lemma vertical_dual_right_out_adj {N : Nat}
    (U : Finset (GridVertex N N)) (R : Nat)
    (hN : 2 ≤ N) (hR : R < N - 1)
    (htop : ((⟨R, by omega⟩, ⟨N - 1, by omega⟩) : GridVertex N N) ∈ U)
    (hbottom : ((⟨R + 1, by omega⟩, ⟨N - 1, by omega⟩) : GridVertex N N) ∈ U) :
    (uuDualGraph U).Adj
      (.cell ⟨R, hR⟩ ⟨N - 2, by omega⟩) .out := by
  let e : VerticalGridEdge N N := ⟨⟨R, hR⟩, ⟨N - 1, by omega⟩⟩
  refine ⟨by simp, Or.inr ⟨e, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩⟩
  · simpa [e, verticalPrimalEndpoints] using htop
  · simpa [e, verticalPrimalEndpoints] using hbottom
  · simp [e, verticalDualEndpoints, show N - 1 ≠ 0 by omega]
    omega
  · simp [e, verticalDualEndpoints]
    omega

private lemma residue_one_dense_second {k r c : Nat} (_hk : 1 ≤ k)
    (hr : r < 3 * k) (hc : c < 3 * k + 1)
    (hmod : r % 3 = 1) (hc1 : 1 ≤ c) :
    ((⟨r, by omega⟩, ⟨c, hc⟩) : GridVertex (3 * k + 1) (3 * k + 1)) ∈
      uResidueOne k := by
  rw [mem_uResidueOne_iff]
  change isInUResidueOne k ⟨r, by omega⟩ ⟨c, hc⟩
  unfold isInUResidueOne
  exact Or.inr (Or.inl ⟨hmod, hr, hc1⟩)

private lemma residue_one_dense_third {k r c : Nat} (_hk : 1 ≤ k)
    (hr : r < 3 * k) (hc : c < 3 * k + 1)
    (hmod : r % 3 = 2) (hc1 : 1 ≤ c) :
    ((⟨r, by omega⟩, ⟨c, hc⟩) : GridVertex (3 * k + 1) (3 * k + 1)) ∈
      uResidueOne k := by
  rw [mem_uResidueOne_iff]
  change isInUResidueOne k ⟨r, by omega⟩ ⟨c, hc⟩
  unfold isInUResidueOne
  by_cases hfinal : r + 1 = 3 * k
  · exact Or.inr (Or.inr (Or.inr (by simpa using hfinal)))
  · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
    · simpa using hmod
    · have : r + 1 < 3 * k := by omega
      simpa using this
    · simpa using hc1

private lemma residue_one_sparse_anchor {k r : Nat} (hk : 1 ≤ k)
    (hr : r < 3 * k) (hmod : r % 3 = 0) :
    ((⟨r, by omega⟩, ⟨1, by omega⟩) : GridVertex (3 * k + 1) (3 * k + 1)) ∈
      uResidueOne k := by
  rw [mem_uResidueOne_iff]
  change isInUResidueOne k ⟨r, by omega⟩ ⟨1, by omega⟩
  unfold isInUResidueOne
  exact Or.inl ⟨hmod, hr, rfl⟩

private lemma residue_one_row_reachable_out (k r c : Nat) (hk : 1 ≤ k)
    (hr : r < 3 * k) (hc : c < 3 * k) (hmod : r % 3 = 1) :
    (uuDualGraph (uResidueOne k)).Reachable
      (.cell ⟨r, hr⟩ ⟨c, hc⟩) .out := by
  induction hdist : 3 * k - c using Nat.strong_induction_on generalizing c with
  | h d ih =>
      by_cases hlast : c + 1 = 3 * k
      · have ht := residue_one_dense_second hk hr (by omega : 3 * k < 3 * k + 1)
          hmod (by omega : 1 ≤ 3 * k)
        have hb := residue_one_dense_third hk (by omega : r + 1 < 3 * k)
          (by omega : 3 * k < 3 * k + 1) (by omega : (r + 1) % 3 = 2)
          (by omega : 1 ≤ 3 * k)
        have ht' :
            ((⟨r, by omega⟩, ⟨(3 * k + 1) - 1, by omega⟩) :
              GridVertex (3 * k + 1) (3 * k + 1)) ∈ uResidueOne k := by
          simpa only [Nat.add_sub_cancel] using ht
        have hb' :
            ((⟨r + 1, by omega⟩, ⟨(3 * k + 1) - 1, by omega⟩) :
              GridVertex (3 * k + 1) (3 * k + 1)) ∈ uResidueOne k := by
          simpa only [Nat.add_sub_cancel] using hb
        have hadj := vertical_dual_right_out_adj (uResidueOne k) r
          (by omega : 2 ≤ 3 * k + 1) hr ht' hb'
        simpa [show c = 3 * k - 1 by omega] using hadj.reachable
      · have hcnext : c + 1 < 3 * k := by omega
        have ht := residue_one_dense_second hk hr (by omega : c + 1 < 3 * k + 1)
          hmod (by omega : 1 ≤ c + 1)
        have hb := residue_one_dense_third hk (by omega : r + 1 < 3 * k)
          (by omega : c + 1 < 3 * k + 1) (by omega : (r + 1) % 3 = 2)
          (by omega : 1 ≤ c + 1)
        have hadj := vertical_dual_cells_adj (uResidueOne k) r (c + 1) hr
          (by omega) hcnext ht hb
        have hlt : 3 * k - (c + 1) < d := by omega
        exact hadj.reachable.trans (ih _ hlt (c + 1) hcnext rfl)

private theorem uResidueOne_dual_reachable_out (k : Nat) (hk : 1 ≤ k)
    (f : GridFace (3 * k + 1) (3 * k + 1)) :
    (uuDualGraph (uResidueOne k)).Reachable f .out := by
  cases f with
  | out => exact Reachable.refl _
  | cell r c =>
      have hrmod : r.val % 3 < 3 := Nat.mod_lt _ (by omega)
      rcases (by omega : r.val % 3 = 0 ∨ r.val % 3 = 1 ∨ r.val % 3 = 2) with
        hmod | hmod | hmod
      · by_cases hc0 : c.val = 0
        · have hcEq : c = ⟨0, by omega⟩ := Fin.ext hc0
          rw [hcEq]
          have hs := residue_one_sparse_anchor hk r.isLt hmod
          have hd := residue_one_dense_second hk (by omega : r.val + 1 < 3 * k)
            (by omega : 1 < 3 * k + 1) (by omega : (r.val + 1) % 3 = 1) (by omega)
          have hadj := vertical_dual_cells_adj (uResidueOne k) r.val 1 r.isLt
            (by omega) (by omega) hs hd
          have hleft := residue_one_dense_second hk (by omega : r.val + 1 < 3 * k)
            (by omega : 1 < 3 * k + 1) (by omega : (r.val + 1) % 3 = 1) (by omega)
          have hright := residue_one_dense_second hk (by omega : r.val + 1 < 3 * k)
            (by omega : 2 < 3 * k + 1) (by omega : (r.val + 1) % 3 = 1) (by omega)
          have hdown := horizontal_dual_cells_adj (uResidueOne k) (r.val + 1) 1
            (by omega) (by omega) (by omega) hleft hright
          have hcore := residue_one_row_reachable_out k (r.val + 1) 1 hk
            (by omega) (by omega) (by omega)
          exact hadj.reachable.trans (hdown.reachable.trans hcore)
        · have hleft := residue_one_dense_second hk (by omega : r.val + 1 < 3 * k)
            (by omega : c.val < 3 * k + 1) (by omega : (r.val + 1) % 3 = 1)
            (by omega : 1 ≤ c.val)
          have hright := residue_one_dense_second hk (by omega : r.val + 1 < 3 * k)
            (by omega : c.val + 1 < 3 * k + 1) (by omega : (r.val + 1) % 3 = 1)
            (by omega : 1 ≤ c.val + 1)
          have hadj := horizontal_dual_cells_adj (uResidueOne k) (r.val + 1) c.val
            (by omega) (by omega) c.isLt hleft hright
          exact hadj.reachable.trans
            (residue_one_row_reachable_out k (r.val + 1) c.val hk (by omega) c.isLt (by omega))
      · exact residue_one_row_reachable_out k r.val c.val hk r.isLt c.isLt hmod
      · by_cases hfinal : r.val + 1 = 3 * k
        · have hleft' :
              ((⟨r.val, by omega⟩, ⟨c.val, by omega⟩) :
                GridVertex (3 * k + 1) (3 * k + 1)) ∈ uResidueOne k := by
            rw [mem_uResidueOne_iff]
            exact Or.inr (Or.inr (Or.inr hfinal))
          have hright' :
              ((⟨r.val, by omega⟩, ⟨c.val + 1, by omega⟩) :
                GridVertex (3 * k + 1) (3 * k + 1)) ∈ uResidueOne k := by
            rw [mem_uResidueOne_iff]
            exact Or.inr (Or.inr (Or.inr hfinal))
          have hadj := horizontal_dual_cells_adj (uResidueOne k) r.val c.val
            (by omega) r.isLt c.isLt hleft' hright'
          exact hadj.symm.reachable.trans
            (residue_one_row_reachable_out k (r.val - 1) c.val hk (by omega) c.isLt (by omega))
        · by_cases hc0 : c.val = 0
          · have hcEq : c = ⟨0, by omega⟩ := Fin.ext hc0
            rw [hcEq]
            have ht := residue_one_dense_third hk r.isLt (by omega : 1 < 3 * k + 1)
              hmod (by omega)
            have hb := residue_one_sparse_anchor hk (by omega : r.val + 1 < 3 * k)
              (by omega : (r.val + 1) % 3 = 0)
            have hadj := vertical_dual_cells_adj (uResidueOne k) r.val 1 r.isLt
              (by omega) (by omega) ht hb
            have hleft := residue_one_dense_third hk r.isLt
              (by omega : 1 < 3 * k + 1) hmod (by omega)
            have hright := residue_one_dense_third hk r.isLt
              (by omega : 2 < 3 * k + 1) hmod (by omega)
            have hup := horizontal_dual_cells_adj (uResidueOne k) r.val 1
              (by omega) r.isLt (by omega) hleft hright
            have hcore := residue_one_row_reachable_out k (r.val - 1) 1 hk
              (by omega) (by omega) (by omega)
            exact hadj.reachable.trans (hup.symm.reachable.trans hcore)
          · have hleft := residue_one_dense_third hk r.isLt
              (by omega : c.val < 3 * k + 1) hmod (by omega : 1 ≤ c.val)
            have hright := residue_one_dense_third hk r.isLt
              (by omega : c.val + 1 < 3 * k + 1) hmod (by omega)
            have hadj := horizontal_dual_cells_adj (uResidueOne k) r.val c.val
              (by omega) r.isLt c.isLt hleft hright
            exact hadj.symm.reachable.trans
              (residue_one_row_reachable_out k (r.val - 1) c.val hk (by omega) c.isLt (by omega))

/-- The U-U dual of the residue-one construction is connected. -/
theorem uuDualGraph_uResidueOne_connected (k : Nat) (hk : 1 ≤ k) :
    (uuDualGraph (uResidueOne k)).Connected := by
  have : Nonempty (GridFace (3 * k + 1) (3 * k + 1)) := ⟨.out⟩
  constructor
  intro f g
  exact (uResidueOne_dual_reachable_out k hk f).trans
    (uResidueOne_dual_reachable_out k hk g).symm

/-- The forced graph on the complement of the residue-one set is acyclic. -/
theorem forced_compl_uResidueOne_isAcyclic (k : Nat) (hk : 1 ≤ k) :
    (forcedEdgeGraph (gridGraph (3 * k + 1) (3 * k + 1))
      (↑(uResidueOne k) : Set (GridVertex (3 * k + 1) (3 * k + 1)))ᶜ).IsAcyclic := by
  exact gridDualCycleSeparation (uResidueOne k)
    (uuDualGraph_uResidueOne_connected k hk)

/-- A spanning tree preserving every vertex outside the residue-one set. -/
theorem exists_isTree_preserving_compl_uResidueOne (k : Nat) (hk : 1 ≤ k) :
    ∃ T : SimpleGraph (GridVertex (3 * k + 1) (3 * k + 1)),
      T ≤ gridGraph (3 * k + 1) (3 * k + 1) ∧ T.IsTree ∧
      ∀ ⦃v : GridVertex (3 * k + 1) (3 * k + 1)⦄,
        v ∈ (↑(uResidueOne k) : Set (GridVertex (3 * k + 1) (3 * k + 1)))ᶜ →
          preservesIncidentEdges (gridGraph (3 * k + 1) (3 * k + 1)) T v := by
  exact exists_isTree_preserving_compl_of_uuDual_connected_grid
    (uResidueOne k) (uuDualGraph_uResidueOne_connected k hk)
    (gridGraph_connected (by omega) (by omega))

end GridGraphs
