import GridGraphs.Constructions.ResidueZero.ResidueZeroConnected

/-!
# Widening the residue-zero construction

The recurrence `B_(k+1) = R_(k-2) S_(k-2) B_k R_k` shifts the old phase
block down by two rows and adds three columns on the right.  This file records
the coordinate embedding and the part of dual-edge preservation which is
independent of boundary attachments.
-/

namespace GridGraphs

open SimpleGraph

/-- The recursive decomposition of the phase word at the next width. -/
theorem phaseRows_succ (k : Nat) (hk : 7 ≤ k) :
    phaseRows (k + 1) =
      [.ordinary (k - 2), .seam (k - 2)] ++ phaseRows k ++ [.ordinary k] := by
  rw [phaseRows, if_pos (by omega : 7 ≤ k + 1), phaseRows, if_pos hk]
  have h₁ : k + 1 - 7 = (k - 7) + 1 := by omega
  rw [h₁, phaseRowsFrom]
  have h₂ : k - 7 + 5 = k - 2 := by omega
  have h₃ : k - 7 + 7 = k := by omega
  rw [h₂, h₃]

/-- Occupation of an old coordinate is preserved when a phase row is
reinterpreted at the next width. -/
theorem PhaseOccupied.widen {k c : Nat} {row : PhaseRow} (_hk : 7 ≤ k)
    (hrow : row.parameter < k) (h : PhaseOccupied k row c) :
    PhaseOccupied (k + 1) row c := by
  cases row with
  | ordinary a =>
      simp only [PhaseRow.parameter] at hrow
      rw [phaseOccupied_ordinary_iff hrow] at h
      rw [phaseOccupied_ordinary_iff (by omega : a < k + 1)]
      rcases h with h | h | h
      · exact Or.inl ⟨h.choose, by omega, h.choose_spec.2⟩
      · exact Or.inr (Or.inl
          ⟨h.choose, by omega, h.choose_spec.2.1, h.choose_spec.2.2⟩)
      · exact Or.inr (Or.inr
          ⟨h.choose, by omega, h.choose_spec.2.1, h.choose_spec.2.2⟩)
  | seam a =>
      simp only [PhaseRow.parameter] at hrow
      rw [phaseOccupied_seam_iff hrow] at h
      rw [phaseOccupied_seam_iff (by omega : a < k + 1)]
      rcases h with h | h | h
      · exact Or.inl ⟨h.choose, by omega, h.choose_spec.2⟩
      · exact Or.inr (Or.inl
          ⟨h.choose, by omega, h.choose_spec.2.1, h.choose_spec.2.2⟩)
      · exact Or.inr (Or.inr
          ⟨h.choose, by omega, h.choose_spec.2.1, h.choose_spec.2.2⟩)

/-- Embed an old bounded face after the two newly prepended phase rows.  The
three new columns lie to the right, so columns are unchanged. -/
def widenBoundedFace (k : Nat) :
    Fin (3 * k - 1) × Fin (3 * k - 1) →
      Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1) :=
  fun rc =>
    (⟨rc.1.val + 2, by have := rc.1.isLt; omega⟩,
      ⟨rc.2.val, by have := rc.2.isLt; omega⟩)

/-- The corresponding embedding into bounded dual faces. -/
def widenCell (k : Nat) (r c : Fin (3 * k - 1)) :
    GridFace (3 * (k + 1)) (3 * (k + 1)) :=
  .cell (widenBoundedFace k (r, c)).1 (widenBoundedFace k (r, c)).2

@[simp] theorem widenCell_eq (k : Nat) (r c : Fin (3 * k - 1)) :
    widenCell k r c = .cell ⟨r.val + 2, by have := r.isLt; omega⟩
      ⟨c.val, by have := c.isLt; omega⟩ := rfl

theorem widenBoundedFace_injective (k : Nat) :
    Function.Injective (widenBoundedFace k) := by
  rintro ⟨r, c⟩ ⟨r', c'⟩ h
  apply Prod.ext
  · apply Fin.ext
    have := congrArg (fun p => p.1.val) h
    simp [widenBoundedFace] at this
    omega
  · apply Fin.ext
    exact congrArg (fun p => p.2.val) h

/-- The old bounded dual graph restricted to edges which survive widening.
Keeping the old-edge conjunct makes this a genuine subgraph of the old U-U
dual graph rather than a graph pulled back only from the new grid. -/
def widenableOldDualGraph (k : Nat) (hk : 7 ≤ k) :
    SimpleGraph (Fin (3 * k - 1) × Fin (3 * k - 1)) where
  Adj x y :=
    (uuDualGraph (uResidueZero k hk)).Adj (.cell x.1 x.2) (.cell y.1 y.2) ∧
      (uuDualGraph (uResidueZero (k + 1) (by omega))).Adj
        (widenCell k x.1 x.2) (widenCell k y.1 y.2)
  symm := by
    constructor
    rintro x y ⟨hold, hnew⟩
    exact ⟨hold.symm, hnew.symm⟩
  loopless := by
    constructor
    rintro x ⟨hold, -⟩
    exact (uuDualGraph (uResidueZero k hk)).loopless.irrefl (.cell x.1 x.2) hold

/-- Every edge of the restricted old graph is an old U-U dual edge. -/
def widenableOldDualToOld (k : Nat) (hk : 7 ≤ k) :
    widenableOldDualGraph k hk →g uuDualGraph (uResidueZero k hk) where
  toFun x := .cell x.1 x.2
  map_rel' h := h.1

/-- Coordinate widening is a graph homomorphism on all surviving old edges. -/
def widenableOldDualToWidened (k : Nat) (hk : 7 ≤ k) :
    widenableOldDualGraph k hk →g
      uuDualGraph (uResidueZero (k + 1) (by omega)) where
  toFun x := widenCell k x.1 x.2
  map_rel' h := h.2

/-- Consequently every old bounded U-U path whose edges survive widening maps
to reachability in the widened dual graph. -/
theorem widenable_old_dual_reachable (k : Nat) (hk : 7 ≤ k)
    {x y : Fin (3 * k - 1) × Fin (3 * k - 1)}
    (h : (widenableOldDualGraph k hk).Reachable x y) :
    (uuDualGraph (uResidueZero (k + 1) (by omega))).Reachable
      (widenCell k x.1 x.2) (widenCell k y.1 y.2) :=
  h.map (widenableOldDualToWidened k hk)

/-- A phase coordinate can be inserted into `uResidueZero` from an occupied
column witness, without exposing the dependent image representation. -/
theorem phase_occupied_mem_uResidueZero (k : Nat) (hk : 7 ≤ k)
    (i : Fin (phaseRows k).length) (c : Nat)
    (hc : PhaseOccupied k ((phaseRows k).get i) c) :
    ((⟨i.val + 2, by
        have hi := i.isLt
        have hlen := phaseRows_length k hk
        omega⟩,
      ⟨c, by
        rcases hc with ⟨j, rfl⟩
        exact phaseColumn_lt
          (phaseRows_parameter_lt k hk _ (List.get_mem (phaseRows k) i)) j⟩) :
      GridVertex (3 * k) (3 * k)) ∈ uResidueZero k hk := by
  rcases hc with ⟨j, rfl⟩
  exact phase_vertex_mem_uResidueZero k hk i j

/-- An occupied coordinate of an old row, interpreted at the new width, occurs
two phase rows lower in the widened construction. -/
theorem old_phase_occupied_mem_widened (k : Nat) (hk : 7 ≤ k)
    (i : Fin (phaseRows k).length) (c : Nat)
    (hc : PhaseOccupied (k + 1) ((phaseRows k).get i) c) :
    ((⟨i.val + 4, by
        have hi := i.isLt
        have hlen := phaseRows_length k hk
        omega⟩,
      ⟨c, by
        rcases hc with ⟨j, rfl⟩
        have hp := phaseRows_parameter_lt k hk _ (List.get_mem (phaseRows k) i)
        have := phaseColumn_lt (show ((phaseRows k).get i).parameter < k + 1 by
          omega) j
        omega⟩) : GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
      uResidueZero (k + 1) (by omega) := by
  have hword := phaseRows_succ k hk
  have hi : i.val + 2 < (phaseRows (k + 1)).length := by
    have hlenNew := phaseRows_length (k + 1) (by omega)
    have hlenOld := phaseRows_length k hk
    have := i.isLt
    omega
  let i' : Fin (phaseRows (k + 1)).length := ⟨i.val + 2, hi⟩
  have hrow : (phaseRows (k + 1)).get i' = (phaseRows k).get i := by
    simp [i', hword]
  have hc' : PhaseOccupied (k + 1) ((phaseRows (k + 1)).get i') c := by
    rw [hrow]
    exact hc
  simpa [i'] using phase_occupied_mem_uResidueZero (k + 1) (by omega) i' c hc'

/-- Every old phase vertex occurs two rows lower in the widened construction. -/
theorem old_phase_vertex_mem_widened (k : Nat) (hk : 7 ≤ k)
    (i : Fin (phaseRows k).length) (c : Nat)
    (hc : PhaseOccupied k ((phaseRows k).get i) c) :
    ((⟨i.val + 4, by
        have hi := i.isLt
        have hlen := phaseRows_length k hk
        omega⟩,
      ⟨c, by
        rcases hc with ⟨j, rfl⟩
        have hp := phaseRows_parameter_lt k hk _ (List.get_mem (phaseRows k) i)
        have := phaseColumn_lt hp j
        omega⟩) : GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
      uResidueZero (k + 1) (by omega) := by
  apply old_phase_occupied_mem_widened k hk i c
  exact hc.widen hk
    (phaseRows_parameter_lt k hk _ (List.get_mem (phaseRows k) i))

/-- Horizontal U-U dual edges in an old phase row survive under the face
embedding. -/
theorem old_phase_horizontal_dual_adj_widened (k : Nat) (hk : 7 ≤ k)
    (i : Fin (phaseRows k).length) (c : Nat) (hc : c < 3 * k - 1)
    (hleft : PhaseOccupied k ((phaseRows k).get i) c)
    (hright : PhaseOccupied k ((phaseRows k).get i) (c + 1)) :
    (uuDualGraph (uResidueZero (k + 1) (by omega))).Adj
      (widenCell k ⟨i.val + 1, by
        have hi := i.isLt
        have hlen := phaseRows_length k hk
        omega⟩ ⟨c, hc⟩)
      (widenCell k ⟨i.val + 2, by
        have hi := i.isLt
        have hlen := phaseRows_length k hk
        omega⟩ ⟨c, hc⟩) := by
  have hi' : i.val < 3 * k - 4 := by
    simpa [phaseRows_length k hk] using i.isLt
  have hadj := horizontal_uu_dual_cells_adj
    (uResidueZero (k + 1) (by omega)) (i.val + 4) c
    (by omega) (by omega) (by omega)
    (old_phase_vertex_mem_widened k hk i c hleft)
    (old_phase_vertex_mem_widened k hk i (c + 1) hright)
  simpa [widenCell, widenBoundedFace] using hadj

/-- Vertical U-U dual edges between consecutive old phase rows survive under
the face embedding. -/
theorem old_phase_vertical_dual_adj_widened (k : Nat) (hk : 7 ≤ k)
    (i : Nat) (hi : i + 1 < (phaseRows k).length) (c : Nat)
    (hc0 : 0 < c) (hc : c < 3 * k - 1)
    (htop : PhaseOccupied k ((phaseRows k)[i]'(by omega)) c)
    (hbottom : PhaseOccupied k ((phaseRows k)[i + 1]'hi) c) :
    (uuDualGraph (uResidueZero (k + 1) (by omega))).Adj
      (widenCell k ⟨i + 2, by
        have hlen := phaseRows_length k hk
        omega⟩ ⟨c - 1, by omega⟩)
      (widenCell k ⟨i + 2, by
        have hlen := phaseRows_length k hk
        omega⟩ ⟨c, hc⟩) := by
  have hi' : i + 1 < 3 * k - 4 := by
    simpa [phaseRows_length k hk] using hi
  have hadj := vertical_uu_dual_cells_adj
    (uResidueZero (k + 1) (by omega)) (i + 4) c
    (by omega) (by omega) (by omega)
    (old_phase_vertex_mem_widened k hk ⟨i, by omega⟩ c htop)
    (old_phase_vertex_mem_widened k hk ⟨i + 1, hi⟩ c hbottom)
  simpa [widenCell, widenBoundedFace] using hadj

/-- At the widened width, every old phase row has the two new right-slab
vertices in columns `3k` and `3k+1`. -/
theorem old_phase_right_slab_run (k : Nat) (hk : 7 ≤ k)
    (i : Fin (phaseRows k).length) :
    ((⟨i.val + 4, by
        have hi := i.isLt
        have hlen := phaseRows_length k hk
        omega⟩, ⟨3 * k, by omega⟩) :
        GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
          uResidueZero (k + 1) (by omega) ∧
      ((⟨i.val + 4, by
          have hi := i.isLt
          have hlen := phaseRows_length k hk
          omega⟩, ⟨3 * k + 1, by omega⟩) :
        GridVertex (3 * (k + 1)) (3 * (k + 1))) ∈
          uResidueZero (k + 1) (by omega) := by
  have hp := phaseRows_parameter_lt k hk _ (List.get_mem (phaseRows k) i)
  constructor
  · apply old_phase_occupied_mem_widened k hk i
    cases hrow : (phaseRows k).get i with
    | ordinary a =>
        simp only [hrow, PhaseRow.parameter] at hp ⊢
        exact (phaseOccupied_ordinary_iff (by omega : a < k + 1)).2
          (Or.inr (Or.inr ⟨k, by omega, by omega, rfl⟩))
    | seam a =>
        simp only [hrow, PhaseRow.parameter] at hp ⊢
        exact (phaseOccupied_seam_iff (by omega : a < k + 1)).2
          (Or.inr (Or.inr ⟨k, by omega, by omega, rfl⟩))
  · apply old_phase_occupied_mem_widened k hk i
    exact phaseOccupied_backbone (by omega : k < k + 1)

/-- Each old phase row supplies a vertical dual edge in the new slab. -/
theorem old_phase_right_slab_vertical_step (k : Nat) (hk : 7 ≤ k)
    (i : Fin (phaseRows k).length) :
    (uuDualGraph (uResidueZero (k + 1) (by omega))).Adj
      (.cell ⟨i.val + 3, by
        have hi := i.isLt
        have hlen := phaseRows_length k hk
        omega⟩ ⟨3 * k, by omega⟩)
      (.cell ⟨i.val + 4, by
        have hi := i.isLt
        have hlen := phaseRows_length k hk
        omega⟩ ⟨3 * k, by omega⟩) := by
  rcases old_phase_right_slab_run k hk i with ⟨hl, hr⟩
  exact horizontal_uu_dual_cells_adj _ (i.val + 4) (3 * k)
    (by omega) (by
      have hi := i.isLt
      have hlen := phaseRows_length k hk
      omega) (by omega) hl hr

/-- Consecutive old phase rows attach the first two new slab columns. -/
theorem old_phase_right_slab_horizontal_step (k : Nat) (hk : 7 ≤ k)
    (i : Nat) (hi : i + 1 < (phaseRows k).length) :
    (uuDualGraph (uResidueZero (k + 1) (by omega))).Adj
      (.cell ⟨i + 4, by
        have hlen := phaseRows_length k hk
        omega⟩ ⟨3 * k - 1, by omega⟩)
      (.cell ⟨i + 4, by
        have hlen := phaseRows_length k hk
        omega⟩ ⟨3 * k, by omega⟩) := by
  have ht := (old_phase_right_slab_run k hk ⟨i, by omega⟩).1
  have hb := (old_phase_right_slab_run k hk ⟨i + 1, hi⟩).1
  exact vertical_uu_dual_cells_adj _ (i + 4) (3 * k)
    (by
      have hlen := phaseRows_length k hk
      omega) (by omega) (by omega) ht hb

/-!
## Remaining induction obstruction

`ResidueZeroInteriorReachability k hk` ends every old path at `GridFace.out`.
The bounded-face embedding above cannot map that endpoint functorially.  In
particular, `final_interior_frontier_adj_out k hk` uses the old right boundary
at column `3*k-1`; after widening this boundary is three columns inside the new
grid.  Thus its image is not the OUT edge used by
`final_interior_frontier_adj_out (k+1) _`.

The local lemmas above embed the old phase-block edges and attach its first two
new slab columns.  To close the induction one still needs a symbolic path from
the image of the old final-frontier anchor through the appended `R_k`, the
rightmost slab face, and the shifted bottom cap to the new OUT edge.  The same
strengthened, bounded-anchor certificate must be established for `B_7` by
explicit local paths.  The existing induction hypothesis, which remembers only
reachability to OUT, does not retain such a path endpoint, so it is not strong
enough on its own.
-/

end GridGraphs
