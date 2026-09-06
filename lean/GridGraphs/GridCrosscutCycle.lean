import GridGraphs.GridBoundaryCycle
import GridGraphs.GridCropComponents
import GridGraphs.GridDual

/-!
# Closing a grid crosscut in a one-cell collar

This file contains only combinatorial graph theory.  A path in an `m x n` grid
is translated into the central rectangle of the `(m + 2) x (n + 2)` grid.  A
chosen simple arc of the outer boundary, together with its two radial edges,
closes the translated path to a cycle.  No Jordan or crossing theorem is used.
-/

namespace GridGraphs

open SimpleGraph

/-! ## Finite clockwise arcs in the boundary numbering -/

private theorem cyclicOffset_succ {k : Nat} (hk : 0 < k) (i : Fin k) (d : Nat) :
    cyclicOffset hk (cyclicOffset hk i 1) d = cyclicOffset hk i (d + 1) := by
  apply Fin.ext
  simp only [cyclicOffset]
  rw [Nat.add_mod]
  rw [Nat.mod_mod, ← Nat.add_mod]
  congr 1
  omega

private theorem gridBoundarySucc_eq_cyclicOffset {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    gridBoundarySucc hm hn i =
      cyclicOffset (gridBoundaryLength_pos hm hn) i 1 := by
  rfl

/-- Walk clockwise for exactly `d` boundary edges. -/
def gridBoundaryForwardWalk {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : (d : Nat) →
    (gridGraph m n).Walk (gridBoundaryVertex hm hn i)
      (gridBoundaryVertex hm hn
        (cyclicOffset (gridBoundaryLength_pos hm hn) i d))
  | 0 => Walk.nil.copy rfl (congrArg (gridBoundaryVertex hm hn) (by
      apply Fin.ext
      simp [cyclicOffset, Nat.mod_eq_of_lt i.isLt]))
  | d + 1 =>
      (Walk.cons (gridBoundaryVertex_succ_adj hm hn i)
        (gridBoundaryForwardWalk hm hn (gridBoundarySucc hm hn i) d)).copy rfl
          (congrArg (gridBoundaryVertex hm hn)
            (cyclicOffset_succ (gridBoundaryLength_pos hm hn) i d))

@[simp] theorem length_gridBoundaryForwardWalk {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) (d : Nat) :
    (gridBoundaryForwardWalk hm hn i d).length = d := by
  induction d generalizing i with
  | zero => simp [gridBoundaryForwardWalk]
  | succ d ih => simp [gridBoundaryForwardWalk, ih]

@[simp] theorem support_gridBoundaryForwardWalk {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) (d : Nat) :
    (gridBoundaryForwardWalk hm hn i d).support =
      (List.range (d + 1)).map fun t =>
        gridBoundaryVertex hm hn
          (cyclicOffset (gridBoundaryLength_pos hm hn) i t) := by
  induction d generalizing i with
  | zero =>
      rw [gridBoundaryForwardWalk, Walk.support_copy]
      simp [cyclicOffset, Nat.mod_eq_of_lt i.isLt]
  | succ d ih =>
      simp only [gridBoundaryForwardWalk, Walk.support_copy, Walk.support_cons, ih]
      conv_rhs =>
        rw [show d + 1 + 1 = (d + 1) + 1 by omega, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      congr 1
      · congr 1
        apply Fin.ext
        simp [cyclicOffset, Nat.mod_eq_of_lt i.isLt]
      · apply List.map_congr_left
        intro t ht
        rw [List.mem_range] at ht
        congr 1
        rw [gridBoundarySucc_eq_cyclicOffset, cyclicOffset_succ]

/-- The boundary edge reached after `t` clockwise steps from `i`. -/
def gridBoundaryOffsetEdge {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) (t : Nat) : Sym2 (GridVertex m n) :=
  s(gridBoundaryVertex hm hn
      (cyclicOffset (gridBoundaryLength_pos hm hn) i t),
    gridBoundaryVertex hm hn
      (cyclicOffset (gridBoundaryLength_pos hm hn) i (t + 1)))

/-- Coordinate label of the clockwise edge leaving a boundary position. -/
noncomputable def gridBoundaryCoordinateEdge {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) : GridEdge m n :=
  (GridEdge.equivGridGraphEdgeSet m n).symm
    ⟨gridBoundaryOffsetEdge hm hn i 0, by
      unfold gridBoundaryOffsetEdge
      rw [SimpleGraph.mem_edgeSet]
      have hzero : cyclicOffset (gridBoundaryLength_pos hm hn) i 0 = i := by
        apply Fin.ext
        simp [cyclicOffset, Nat.mod_eq_of_lt i.isLt]
      simpa only [hzero, Nat.zero_add, cyclicOffset_one_eq_gridBoundarySucc hm hn] using
        gridBoundaryVertex_succ_adj hm hn i⟩

theorem gridBoundaryCoordinateEdge_primalSym2_eq_gridBoundaryOffsetEdge_zero
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) :
    (gridBoundaryCoordinateEdge hm hn i).primalSym2 =
      gridBoundaryOffsetEdge hm hn i 0 := by
  exact congrArg Subtype.val
    ((GridEdge.equivGridGraphEdgeSet m n).apply_symm_apply _)

/-- The bounded face incident to the clockwise edge leaving a boundary
position. -/
def gridBoundaryEdgeInnerFace {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (p : GridBoundaryPosition m n) : GridFace m n :=
  if htop : p.val < n - 1 then
    .cell ⟨0, by omega⟩ ⟨p.val, by omega⟩
  else if hright : p.val < n + m - 2 then
    .cell ⟨p.val + 1 - n, by omega⟩ ⟨n - 2, by omega⟩
  else if hbottom : p.val < m + 2 * n - 3 then
    .cell ⟨m - 2, by omega⟩ ⟨m + 2 * n - 4 - p.val, by omega⟩
  else
    .cell ⟨gridBoundaryLength m n - p.val - 1, by
      unfold gridBoundaryLength at *
      omega⟩ ⟨0, by omega⟩

private theorem gridBoundaryCoordinateEdge_eq_top {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (p : GridBoundaryPosition m n)
    (htop : p.val < n - 1) :
    gridBoundaryCoordinateEdge hm hn p =
      .horizontal ⟨⟨0, by omega⟩, ⟨p.val, by omega⟩⟩ := by
  apply GridEdge.primalSym2_injective
  rw [gridBoundaryCoordinateEdge_primalSym2_eq_gridBoundaryOffsetEdge_zero]
  simp only [GridEdge.primalSym2_horizontal, horizontalPrimalEndpoints]
  change gridBoundaryOffsetEdge hm hn p 0 =
    s((⟨0, by omega⟩, ⟨p.val, by omega⟩),
      (⟨0, by omega⟩, ⟨p.val + 1, by omega⟩))
  unfold gridBoundaryOffsetEdge
  have hpnext : p.val + 1 < gridBoundaryLength m n := by
    unfold gridBoundaryLength
    omega
  have hnextval : (⟨p.val + 1, hpnext⟩ : GridBoundaryPosition m n).val =
      p.val + 1 := rfl
  simp only [cyclicOffset, Nat.add_zero, Nat.mod_eq_of_lt p.isLt,
    Nat.mod_eq_of_lt hpnext]
  change s(gridBoundaryVertex hm hn p,
    gridBoundaryVertex hm hn ⟨p.val + 1, hpnext⟩) = _
  rw [gridBoundaryVertex_top hm hn p (by omega),
    gridBoundaryVertex_top hm hn ⟨p.val + 1, hpnext⟩ (by omega)]

private theorem gridBoundaryCoordinateEdge_eq_right {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (p : GridBoundaryPosition m n)
    (htop : ¬p.val < n - 1) (hright : p.val < n + m - 2) :
    gridBoundaryCoordinateEdge hm hn p =
      .vertical ⟨⟨p.val + 1 - n, by omega⟩, ⟨n - 1, by omega⟩⟩ := by
  apply GridEdge.primalSym2_injective
  rw [gridBoundaryCoordinateEdge_primalSym2_eq_gridBoundaryOffsetEdge_zero]
  simp only [GridEdge.primalSym2_vertical, verticalPrimalEndpoints]
  change gridBoundaryOffsetEdge hm hn p 0 =
    s((⟨p.val + 1 - n, by omega⟩, ⟨n - 1, by omega⟩),
      (⟨p.val + 1 - n + 1, by omega⟩, ⟨n - 1, by omega⟩))
  unfold gridBoundaryOffsetEdge
  have hpnext : p.val + 1 < gridBoundaryLength m n := by
    unfold gridBoundaryLength
    omega
  have hnextval : (⟨p.val + 1, hpnext⟩ : GridBoundaryPosition m n).val =
      p.val + 1 := rfl
  simp only [cyclicOffset, Nat.add_zero, Nat.mod_eq_of_lt p.isLt,
    Nat.mod_eq_of_lt hpnext]
  change s(gridBoundaryVertex hm hn p,
    gridBoundaryVertex hm hn ⟨p.val + 1, hpnext⟩) = _
  by_cases hcorner : p.val < n
  · rw [gridBoundaryVertex_top hm hn p hcorner,
      gridBoundaryVertex_right hm hn ⟨p.val + 1, hpnext⟩ (by omega) (by omega)]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Prod.ext <;> apply Fin.ext <;> simp only
    all_goals omega
  · rw [gridBoundaryVertex_right hm hn p hcorner (by omega),
      gridBoundaryVertex_right hm hn ⟨p.val + 1, hpnext⟩ (by omega) (by omega)]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Prod.ext <;> apply Fin.ext <;> simp only
    all_goals omega

private theorem gridBoundaryCoordinateEdge_eq_bottom {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (p : GridBoundaryPosition m n)
    (hright : ¬p.val < n + m - 2)
    (hbottom : p.val < m + 2 * n - 3) :
    gridBoundaryCoordinateEdge hm hn p =
      .horizontal ⟨⟨m - 1, by omega⟩,
        ⟨m + 2 * n - 4 - p.val, by omega⟩⟩ := by
  apply GridEdge.primalSym2_injective
  rw [gridBoundaryCoordinateEdge_primalSym2_eq_gridBoundaryOffsetEdge_zero]
  simp only [GridEdge.primalSym2_horizontal, horizontalPrimalEndpoints]
  change gridBoundaryOffsetEdge hm hn p 0 =
    s((⟨m - 1, by omega⟩, ⟨m + 2 * n - 4 - p.val, by omega⟩),
      (⟨m - 1, by omega⟩, ⟨m + 2 * n - 4 - p.val + 1, by omega⟩))
  unfold gridBoundaryOffsetEdge
  have hpnext : p.val + 1 < gridBoundaryLength m n := by
    unfold gridBoundaryLength
    omega
  have hnextval : (⟨p.val + 1, hpnext⟩ : GridBoundaryPosition m n).val =
      p.val + 1 := rfl
  simp only [cyclicOffset, Nat.add_zero, Nat.mod_eq_of_lt p.isLt,
    Nat.mod_eq_of_lt hpnext]
  change s(gridBoundaryVertex hm hn p,
    gridBoundaryVertex hm hn ⟨p.val + 1, hpnext⟩) = _
  by_cases hcorner : p.val < n + m - 1
  · rw [gridBoundaryVertex_right hm hn p (by omega) hcorner,
      gridBoundaryVertex_bottom hm hn ⟨p.val + 1, hpnext⟩ (by omega) (by omega)]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Prod.ext <;> apply Fin.ext <;> simp only
    all_goals omega
  · rw [gridBoundaryVertex_bottom hm hn p hcorner (by omega),
      gridBoundaryVertex_bottom hm hn ⟨p.val + 1, hpnext⟩ (by omega) (by omega)]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Prod.ext <;> apply Fin.ext <;> simp only
    all_goals omega

private theorem gridBoundaryCoordinateEdge_eq_left {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (p : GridBoundaryPosition m n)
    (hbottom : ¬p.val < m + 2 * n - 3) :
    gridBoundaryCoordinateEdge hm hn p =
      .vertical ⟨⟨gridBoundaryLength m n - p.val - 1, by
        unfold gridBoundaryLength at *
        omega⟩, ⟨0, by omega⟩⟩ := by
  apply GridEdge.primalSym2_injective
  rw [gridBoundaryCoordinateEdge_primalSym2_eq_gridBoundaryOffsetEdge_zero]
  simp only [GridEdge.primalSym2_vertical, verticalPrimalEndpoints]
  change gridBoundaryOffsetEdge hm hn p 0 =
    s((⟨gridBoundaryLength m n - p.val - 1, by
          unfold gridBoundaryLength at *
          omega⟩, ⟨0, by omega⟩),
      (⟨gridBoundaryLength m n - p.val - 1 + 1, by
          unfold gridBoundaryLength at *
          omega⟩, ⟨0, by omega⟩))
  unfold gridBoundaryOffsetEdge
  have hpnext : p.val + 1 ≤ gridBoundaryLength m n := by omega
  by_cases hlast : p.val + 1 < gridBoundaryLength m n
  · simp only [cyclicOffset, Nat.add_zero, Nat.mod_eq_of_lt p.isLt,
      Nat.mod_eq_of_lt hlast]
    have hnextval : (⟨p.val + 1, hlast⟩ : GridBoundaryPosition m n).val =
        p.val + 1 := rfl
    change s(gridBoundaryVertex hm hn p,
      gridBoundaryVertex hm hn ⟨p.val + 1, hlast⟩) = _
    by_cases hcorner : p.val < m + 2 * n - 2
    · rw [gridBoundaryVertex_bottom hm hn p (by omega) hcorner,
        gridBoundaryVertex_left hm hn ⟨p.val + 1, hlast⟩ (by omega)]
      rw [Sym2.eq_iff]
      right
      constructor <;> apply Prod.ext <;> apply Fin.ext <;>
        simp only
      all_goals unfold gridBoundaryLength at *; omega
    · rw [gridBoundaryVertex_left hm hn p hcorner,
        gridBoundaryVertex_left hm hn ⟨p.val + 1, hlast⟩ (by omega)]
      rw [Sym2.eq_iff]
      right
      constructor <;> apply Prod.ext <;> apply Fin.ext <;> simp only
      all_goals omega
  · have hlast' : p.val + 1 = gridBoundaryLength m n := by omega
    have hshape : gridBoundaryLength m n =
        (m + 2 * n - 2) + (m - 2) := by
      unfold gridBoundaryLength
      omega
    simp only [cyclicOffset, Nat.add_zero, Nat.mod_eq_of_lt p.isLt,
      hlast', Nat.mod_self]
    change s(gridBoundaryVertex hm hn p,
      gridBoundaryVertex hm hn ⟨0, gridBoundaryLength_pos hm hn⟩) = _
    by_cases hcorner : p.val < m + 2 * n - 2
    · rw [gridBoundaryVertex_bottom hm hn p (by omega) hcorner,
        gridBoundaryVertex_top hm hn ⟨0, gridBoundaryLength_pos hm hn⟩ (by
          change 0 < n
          omega)]
      rw [Sym2.eq_iff]
      right
      constructor <;> apply Prod.ext <;> apply Fin.ext <;>
        simp only
      all_goals unfold gridBoundaryLength at *; omega
    · rw [gridBoundaryVertex_left hm hn p hcorner,
        gridBoundaryVertex_top hm hn ⟨0, gridBoundaryLength_pos hm hn⟩ (by
          change 0 < n
          omega)]
      rw [Sym2.eq_iff]
      right
      constructor <;> apply Prod.ext <;> apply Fin.ext <;>
        simp only
      all_goals unfold gridBoundaryLength at *; omega

/-- Every clockwise coordinate boundary edge is incident to `out` and its
named bounded face. -/
theorem gridBoundaryCoordinateEdge_hasDualEndpoints_out_innerFace {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (p : GridBoundaryPosition m n) :
    HasDualEndpoints (gridBoundaryCoordinateEdge hm hn p).dualEndpoints
      GridFace.out (gridBoundaryEdgeInnerFace hm hn p) := by
  by_cases htop : p.val < n - 1
  · rw [gridBoundaryCoordinateEdge_eq_top hm hn p htop]
    simp [gridBoundaryEdgeInnerFace, htop, GridEdge.dualEndpoints,
      horizontalDualEndpoints, HasDualEndpoints]
    omega
  by_cases hright : p.val < n + m - 2
  · rw [gridBoundaryCoordinateEdge_eq_right hm hn p htop hright]
    have hnshape : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    change HasDualEndpoints (verticalDualEndpoints _)
      GridFace.out (gridBoundaryEdgeInnerFace hm hn p)
    right
    constructor
    · exact (verticalDualEndpoints_snd_of_right _ hnshape).symm
    · have hp_lt : p.val < gridBoundaryLength m n := p.isLt
      have hnsub : n - 1 ≠ 0 := by omega
      unfold gridBoundaryLength at hp_lt
      simp [verticalDualEndpoints, gridBoundaryEdgeInnerFace, htop, hright,
        hnshape, hnsub, Nat.sub_sub]
  by_cases hbottom : p.val < m + 2 * n - 3
  · rw [gridBoundaryCoordinateEdge_eq_bottom hm hn p hright hbottom]
    have hmshape : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
    change HasDualEndpoints (horizontalDualEndpoints _)
      GridFace.out (gridBoundaryEdgeInnerFace hm hn p)
    right
    constructor
    · exact (horizontalDualEndpoints_snd_of_bottom _ hmshape).symm
    · have hp_lt : p.val < gridBoundaryLength m n := p.isLt
      have hmsub : m - 1 ≠ 0 := by omega
      unfold gridBoundaryLength at hp_lt
      simp [horizontalDualEndpoints, gridBoundaryEdgeInnerFace, htop, hright,
        hbottom, hmshape, hmsub, Nat.sub_sub]
  · rw [gridBoundaryCoordinateEdge_eq_left hm hn p hbottom]
    have hn_ne : 1 ≠ n := by omega
    change HasDualEndpoints (verticalDualEndpoints _)
      GridFace.out (gridBoundaryEdgeInnerFace hm hn p)
    left
    constructor
    · exact (verticalDualEndpoints_fst_of_left _ rfl).symm
    · simp [verticalDualEndpoints, gridBoundaryEdgeInnerFace, htop, hright,
        hbottom, hn_ne]

/-- Exact unordered edge list of a finite clockwise boundary walk. -/
@[simp] theorem edges_gridBoundaryForwardWalk {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) (d : Nat) :
    (gridBoundaryForwardWalk hm hn i d).edges =
      (List.range d).map (gridBoundaryOffsetEdge hm hn i) := by
  induction d generalizing i with
  | zero => simp [gridBoundaryForwardWalk]
  | succ d ih =>
      simp only [gridBoundaryForwardWalk, Walk.edges_copy, Walk.edges_cons, ih]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      congr 1
      · simp [gridBoundaryOffsetEdge, gridBoundarySucc_eq_cyclicOffset,
          cyclicOffset, Nat.mod_eq_of_lt i.isLt]
      · apply List.map_congr_left
        intro t ht
        simp only [Function.comp_apply, gridBoundaryOffsetEdge]
        rw [Sym2.eq_iff]
        left
        constructor
        · congr 1
          rw [gridBoundarySucc_eq_cyclicOffset, cyclicOffset_succ]
        · congr 1
          rw [gridBoundarySucc_eq_cyclicOffset, cyclicOffset_succ]

private theorem cyclicOffset_injective_below {k : Nat} (hk : 0 < k) (i : Fin k)
    {s t : Nat} (hs : s < k) (ht : t < k)
    (h : cyclicOffset hk i s = cyclicOffset hk i t) : s = t := by
  have hs' : cyclicOffset hk i s = i + ⟨s, hs⟩ := by
    apply Fin.ext
    simp [cyclicOffset, Fin.add_def]
  have ht' : cyclicOffset hk i t = i + ⟨t, ht⟩ := by
    apply Fin.ext
    simp [cyclicOffset, Fin.add_def]
  rw [hs', ht'] at h
  have hfin : (⟨s, hs⟩ : Fin k) = ⟨t, ht⟩ := add_left_cancel h
  exact congrArg Fin.val hfin

/-- A clockwise boundary segment shorter than the perimeter is simple. -/
theorem gridBoundaryForwardWalk_isPath {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) {d : Nat}
    (hd : d < gridBoundaryLength m n) :
    (gridBoundaryForwardWalk hm hn i d).IsPath := by
  rw [Walk.isPath_def, support_gridBoundaryForwardWalk]
  apply List.Nodup.map_on
  intro s hs t ht hst
  apply cyclicOffset_injective_below (gridBoundaryLength_pos hm hn) i
  · rw [List.mem_range] at hs
    omega
  · rw [List.mem_range] at ht
    omega
  · exact gridBoundaryVertex_injective hm hn hst
  · exact List.nodup_range

/-- Membership in a finite clockwise arc is membership in its cyclic interval. -/
theorem mem_support_gridBoundaryForwardWalk_iff {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) (d : Nat)
    (x : GridVertex m n) :
    x ∈ (gridBoundaryForwardWalk hm hn i d).support ↔
      ∃ t ≤ d, x = gridBoundaryVertex hm hn
        (cyclicOffset (gridBoundaryLength_pos hm hn) i t) := by
  rw [support_gridBoundaryForwardWalk, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [List.mem_range] at ht
    exact ⟨t, by omega, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ?_, rfl⟩
    rw [List.mem_range]
    omega

/-- Translation of a grid into the central rectangle of its one-cell collar. -/
def gridCollarEmbedding (m n : Nat) : GridVertex m n ↪ GridVertex (m + 2) (n + 2) :=
  gridOffsetEmbedding 1 1 (by omega) (by omega)

/-- The collar translation as an induced graph embedding. -/
def gridCollarGraphEmbedding (m n : Nat) :
    gridGraph m n ↪g gridGraph (m + 2) (n + 2) :=
  gridOffsetGraphEmbedding 1 1 (by omega) (by omega)

@[simp] theorem gridCollarEmbedding_fst_val {m n : Nat} (v : GridVertex m n) :
    (gridCollarEmbedding m n v).1.val = v.1.val + 1 := by
  simp [gridCollarEmbedding, Nat.add_comm]

@[simp] theorem gridCollarEmbedding_snd_val {m n : Nat} (v : GridVertex m n) :
    (gridCollarEmbedding m n v).2.val = v.2.val + 1 := by
  simp [gridCollarEmbedding, Nat.add_comm]

/-- Translated vertices never lie on the outer frame. -/
theorem gridCollarEmbedding_not_boundary {m n : Nat} (v : GridVertex m n) :
    ¬IsGridBoundary (gridCollarEmbedding m n v) := by
  simp only [IsGridBoundary, gridCollarEmbedding_fst_val,
    gridCollarEmbedding_snd_val]
  omega

/-- The central rectangle and the outer frame are disjoint. -/
theorem gridCollarEmbedding_ne_of_boundary {m n : Nat} (v : GridVertex m n)
    {x : GridVertex (m + 2) (n + 2)} (hx : IsGridBoundary x) :
    gridCollarEmbedding m n v ≠ x := by
  rintro rfl
  exact gridCollarEmbedding_not_boundary v hx

/-! ## Canonical collar ports -/

/-- Outer-frame port on the side followed by the clockwise boundary edge out
of `i`.  At a corner this selects the outgoing side. -/
def clockwiseOutPort {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : GridVertex (m + 2) (n + 2) :=
  if htop : i.val < n - 1 then
    (⟨0, by omega⟩, ⟨i.val + 1, by omega⟩)
  else if hright : i.val < n + m - 2 then
    (⟨i.val + 1 - n + 1, by omega⟩, ⟨n + 1, by omega⟩)
  else if hbottom : i.val < m + 2 * n - 3 then
    (⟨m + 1, by omega⟩, ⟨m + 2 * n - 2 - i.val, by omega⟩)
  else
    (⟨gridBoundaryLength m n - i.val + 1, by
      unfold gridBoundaryLength at *
      omega⟩, ⟨0, by omega⟩)

/-- Outer-frame port on the side preceding `i` in clockwise order.  At a
corner this selects the incoming side. -/
def clockwiseInPort {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : GridVertex (m + 2) (n + 2) :=
  if hzero : i.val = 0 then
    (⟨1, by omega⟩, ⟨0, by omega⟩)
  else if htop : i.val < n then
    (⟨0, by omega⟩, ⟨i.val + 1, by omega⟩)
  else if hright : i.val < n + m - 1 then
    (⟨i.val - n + 2, by omega⟩, ⟨n + 1, by omega⟩)
  else if hbottom : i.val < m + 2 * n - 2 then
    (⟨m + 1, by omega⟩, ⟨m + 2 * n - 2 - i.val, by omega⟩)
  else
    (⟨gridBoundaryLength m n - i.val + 1, by
      unfold gridBoundaryLength at *
      omega⟩, ⟨0, by omega⟩)

theorem clockwiseOutPort_boundary {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : IsGridBoundary (clockwiseOutPort hm hn i) := by
  unfold clockwiseOutPort IsGridBoundary
  split_ifs <;> simp_all

theorem clockwiseInPort_boundary {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : IsGridBoundary (clockwiseInPort hm hn i) := by
  unfold clockwiseInPort IsGridBoundary
  split_ifs <;> simp_all

theorem clockwiseOutPort_spoke {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) :
    (gridGraph (m + 2) (n + 2)).Adj
      (gridCollarEmbedding m n (gridBoundaryVertex hm hn i))
      (clockwiseOutPort hm hn i) := by
  simp only [gridGraph, adjacent, Fin.ext_iff, gridCollarEmbedding_fst_val,
    gridCollarEmbedding_snd_val]
  unfold clockwiseOutPort gridBoundaryVertex
  split_ifs <;> simp <;> unfold gridBoundaryLength at * <;> omega

theorem clockwiseInPort_spoke {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) :
    (gridGraph (m + 2) (n + 2)).Adj
      (gridCollarEmbedding m n (gridBoundaryVertex hm hn i))
      (clockwiseInPort hm hn i) := by
  simp only [gridGraph, adjacent, Fin.ext_iff, gridCollarEmbedding_fst_val,
    gridCollarEmbedding_snd_val]
  unfold clockwiseInPort gridBoundaryVertex
  split_ifs <;> simp <;> unfold gridBoundaryLength at * <;> omega

/-- Canonical boundary position of a known outer-frame vertex. -/
noncomputable def collarBoundaryPosition {m n : Nat}
    (x : GridVertex (m + 2) (n + 2)) (hx : IsGridBoundary x) :
    GridBoundaryPosition (m + 2) (n + 2) :=
  (gridBoundaryEquiv (by omega) (by omega)).symm ⟨x, hx⟩

@[simp] theorem gridBoundaryVertex_collarBoundaryPosition {m n : Nat}
    (x : GridVertex (m + 2) (n + 2)) (hx : IsGridBoundary x) :
    gridBoundaryVertex (by omega) (by omega) (collarBoundaryPosition x hx) = x := by
  exact congrArg Subtype.val
    ((gridBoundaryEquiv (by omega) (by omega)).apply_symm_apply ⟨x, hx⟩)

@[simp] theorem collarBoundaryPosition_val {m n : Nat}
    (x : GridVertex (m + 2) (n + 2)) (hx : IsGridBoundary x) :
    (collarBoundaryPosition x hx).val = gridBoundaryIndex x := by
  rw [← gridBoundaryIndex_vertex (show 2 ≤ m + 2 by omega)
      (show 2 ≤ n + 2 by omega) (collarBoundaryPosition x hx),
    gridBoundaryVertex_collarBoundaryPosition]

/-- Clockwise distance in a nonempty finite cyclic numbering. -/
def cyclicForwardDistance {k : Nat} (_hk : 0 < k) (i j : Fin k) : Nat :=
  if i.val ≤ j.val then j.val - i.val else j.val + k - i.val

/-- The open clockwise sector from `c` to `d`. -/
def OpenCyclicSector {k : Nat} (hk : 0 < k) (c d x : Fin k) : Prop :=
  0 < cyclicForwardDistance hk c x ∧
    cyclicForwardDistance hk c x < cyclicForwardDistance hk c d

theorem cyclicForwardDistance_lt {k : Nat} (hk : 0 < k) (i j : Fin k) :
    cyclicForwardDistance hk i j < k := by
  unfold cyclicForwardDistance
  split_ifs <;> omega

theorem cyclicForwardDistance_pos_of_ne {k : Nat} (hk : 0 < k)
    {i j : Fin k} (hij : i ≠ j) : 0 < cyclicForwardDistance hk i j := by
  have hijv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  unfold cyclicForwardDistance
  split_ifs <;> omega

theorem cyclicOffset_forwardDistance {k : Nat} (hk : 0 < k) (i j : Fin k) :
    cyclicOffset hk i (cyclicForwardDistance hk i j) = j := by
  apply Fin.ext
  change (i.val + cyclicForwardDistance hk i j) % k = j.val
  unfold cyclicForwardDistance
  split_ifs with h
  · rw [Nat.add_sub_of_le h, Nat.mod_eq_of_lt j.isLt]
  · have hij : i.val ≤ j.val + k := by omega
    rw [Nat.add_sub_of_le hij]
    simp [Nat.mod_eq_of_lt j.isLt]

private theorem cyclicForwardDistance_offset_of_lt {k : Nat} (hk : 0 < k)
    (a : Fin k) {t : Nat} (ht : t < k) :
    cyclicForwardDistance hk a (cyclicOffset hk a t) = t := by
  have hoff := cyclicOffset_forwardDistance hk a (cyclicOffset hk a t)
  have hdlt := cyclicForwardDistance_lt hk a (cyclicOffset hk a t)
  exact cyclicOffset_injective_below hk a hdlt ht hoff

/-- Before one complete revolution, boundary offset edges are injectively
numbered by their offsets. -/
theorem gridBoundaryOffsetEdge_injective_below {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n)
    {s t : Nat} (hs : s < gridBoundaryLength m n)
    (ht : t < gridBoundaryLength m n)
    (h : gridBoundaryOffsetEdge hm hn i s =
      gridBoundaryOffsetEdge hm hn i t) : s = t := by
  rw [gridBoundaryOffsetEdge, gridBoundaryOffsetEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · exact cyclicOffset_injective_below (gridBoundaryLength_pos hm hn) i hs ht
      (gridBoundaryVertex_injective hm hn h.1)
  · let k := gridBoundaryLength m n
    have hk : 4 ≤ k := by
      dsimp [k]
      unfold gridBoundaryLength
      omega
    have hs₁ : s = (t + 1) % k := by
      have he := gridBoundaryVertex_injective hm hn h.1
      have hd := congrArg
        (cyclicForwardDistance (gridBoundaryLength_pos hm hn) i) he
      rw [cyclicForwardDistance_offset_of_lt _ _ hs] at hd
      have heq : cyclicOffset (gridBoundaryLength_pos hm hn) i (t + 1) =
          cyclicOffset (gridBoundaryLength_pos hm hn) i ((t + 1) % k) := by
        apply Fin.ext
        simp [cyclicOffset, k]
      rw [heq, cyclicForwardDistance_offset_of_lt _ _
        (Nat.mod_lt _ (gridBoundaryLength_pos hm hn))] at hd
      exact hd
    have ht₁ : t = (s + 1) % k := by
      have he := gridBoundaryVertex_injective hm hn h.2
      have hd := congrArg
        (cyclicForwardDistance (gridBoundaryLength_pos hm hn) i) he
      have heq : cyclicOffset (gridBoundaryLength_pos hm hn) i (s + 1) =
          cyclicOffset (gridBoundaryLength_pos hm hn) i ((s + 1) % k) := by
        apply Fin.ext
        simp [cyclicOffset, k]
      rw [heq, cyclicForwardDistance_offset_of_lt _ _
          (Nat.mod_lt _ (gridBoundaryLength_pos hm hn)),
        cyclicForwardDistance_offset_of_lt _ _ ht] at hd
      exact hd.symm
    by_cases htlast : t + 1 < k
    · rw [Nat.mod_eq_of_lt htlast] at hs₁
      by_cases hslast : s + 1 < k
      · rw [Nat.mod_eq_of_lt hslast] at ht₁
        omega
      · have : s + 1 = k := by omega
        rw [this, Nat.mod_self] at ht₁
        omega
    · have htK : t + 1 = k := by omega
      rw [htK, Nat.mod_self] at hs₁
      subst s
      rw [Nat.mod_eq_of_lt (by omega)] at ht₁
      omega

/-- A named boundary edge occurs in a sub-revolution forward walk exactly
when its offset is smaller than the walk length. -/
theorem mem_edges_gridBoundaryForwardWalk_iff {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n)
    {d t : Nat} (hd : d ≤ gridBoundaryLength m n)
    (ht : t < gridBoundaryLength m n) :
    gridBoundaryOffsetEdge hm hn i t ∈
        (gridBoundaryForwardWalk hm hn i d).edges ↔ t < d := by
  rw [edges_gridBoundaryForwardWalk, List.mem_map]
  constructor
  · rintro ⟨s, hs, hst⟩
    rw [List.mem_range] at hs
    have hsK : s < gridBoundaryLength m n := by omega
    exact (gridBoundaryOffsetEdge_injective_below hm hn i hsK ht hst).symm ▸ hs
  · intro htd
    exact ⟨t, by simp [htd], rfl⟩

noncomputable def clockwiseOutPortPosition {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : GridBoundaryPosition (m + 2) (n + 2) :=
  collarBoundaryPosition (clockwiseOutPort hm hn i) (clockwiseOutPort_boundary hm hn i)

noncomputable def clockwiseInPortPosition {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : GridBoundaryPosition (m + 2) (n + 2) :=
  collarBoundaryPosition (clockwiseInPort hm hn i) (clockwiseInPort_boundary hm hn i)

/-- Numerical collar index of the outgoing port.  Passing each original corner
adds the two extra outer-frame vertices belonging to that corner. -/
def clockwiseOutPortIndex {m n : Nat} (i : GridBoundaryPosition m n) : Nat :=
  if i.val < n - 1 then i.val + 1
  else if i.val < n + m - 2 then i.val + 3
  else if i.val < m + 2 * n - 3 then i.val + 5
  else i.val + 7

/-- Numerical collar index of the incoming port. -/
def clockwiseInPortIndex {m n : Nat} (i : GridBoundaryPosition m n) : Nat :=
  if i.val = 0 then gridBoundaryLength m n + 7
  else if i.val < n then i.val + 1
  else if i.val < n + m - 1 then i.val + 3
  else if i.val < m + 2 * n - 2 then i.val + 5
  else i.val + 7

/-- The coordinate outer-frame edge immediately clockwise of the outward spoke
at an original boundary position. -/
noncomputable def outerEdgeAtPosition {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : GridEdge (m + 2) (n + 2) :=
  (GridEdge.equivGridGraphEdgeSet (m + 2) (n + 2)).symm
    ⟨gridBoundaryOffsetEdge (by omega) (by omega)
      (clockwiseOutPortPosition hm hn i) 0, by
        unfold gridBoundaryOffsetEdge
        rw [SimpleGraph.mem_edgeSet]
        have hadj := (gridBoundaryForwardWalk (by omega) (by omega)
          (clockwiseOutPortPosition hm hn i) 1).adj_of_mem_edges
            ((mem_edges_gridBoundaryForwardWalk_iff (by omega) (by omega)
              (clockwiseOutPortPosition hm hn i) (d := 1) (t := 0)
              (by unfold gridBoundaryLength; omega)
              (by have := gridBoundaryLength_pos (show 2 ≤ m + 2 by omega)
                    (show 2 ≤ n + 2 by omega); omega)).2 (by omega))
        simpa [gridBoundaryOffsetEdge] using hadj⟩

@[simp] theorem boundaryVertex_clockwiseOutPortPosition {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    gridBoundaryVertex (by omega) (by omega) (clockwiseOutPortPosition hm hn i) =
      clockwiseOutPort hm hn i := by
  apply gridBoundaryVertex_collarBoundaryPosition

@[simp] theorem boundaryVertex_clockwiseInPortPosition {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    gridBoundaryVertex (by omega) (by omega) (clockwiseInPortPosition hm hn i) =
      clockwiseInPort hm hn i := by
  apply gridBoundaryVertex_collarBoundaryPosition

@[simp] theorem clockwiseOutPortPosition_val {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    (clockwiseOutPortPosition hm hn i).val = clockwiseOutPortIndex i := by
  have hi := i.isLt
  unfold gridBoundaryLength at hi
  unfold clockwiseOutPortPosition
  rw [collarBoundaryPosition_val]
  by_cases htop : i.val < n - 1
  · simp [clockwiseOutPort, clockwiseOutPortIndex, gridBoundaryIndex, htop]
  by_cases hright : i.val < n + m - 2
  · simp [clockwiseOutPort, clockwiseOutPortIndex, gridBoundaryIndex, htop, hright]
    omega
  by_cases hbottom : i.val < m + 2 * n - 3
  · simp [clockwiseOutPort, clockwiseOutPortIndex, gridBoundaryIndex, htop, hright,
      hbottom]
    split_ifs <;> omega
  · simp [clockwiseOutPort, clockwiseOutPortIndex, gridBoundaryIndex, htop, hright,
      hbottom, gridBoundaryLength]
    split_ifs <;> omega

@[simp] theorem clockwiseInPortPosition_val {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    (clockwiseInPortPosition hm hn i).val = clockwiseInPortIndex i := by
  have hi := i.isLt
  unfold gridBoundaryLength at hi
  unfold clockwiseInPortPosition
  rw [collarBoundaryPosition_val]
  by_cases hzero : i.val = 0
  · simp [clockwiseInPort, clockwiseInPortIndex, gridBoundaryIndex, hzero,
      gridBoundaryLength]
    split_ifs <;> omega
  by_cases htop : i.val < n
  · simp [clockwiseInPort, clockwiseInPortIndex, gridBoundaryIndex, hzero, htop]
  by_cases hright : i.val < n + m - 1
  · simp [clockwiseInPort, clockwiseInPortIndex, gridBoundaryIndex, hzero, htop,
      hright]
    omega
  by_cases hbottom : i.val < m + 2 * n - 2
  · simp [clockwiseInPort, clockwiseInPortIndex, gridBoundaryIndex, hzero, htop,
      hright, hbottom]
    split_ifs <;> omega
  · simp [clockwiseInPort, clockwiseInPortIndex, gridBoundaryIndex, hzero, htop,
      hright, hbottom, gridBoundaryLength]
    split_ifs <;> omega

set_option maxHeartbeats 1000000 in
/-- Outgoing collar indices preserve the linear order of original boundary
positions. -/
theorem clockwiseOutPortIndex_lt_iff {m n : Nat} (_hm : 2 ≤ m) (_hn : 2 ≤ n)
    (a b : GridBoundaryPosition m n) :
    clockwiseOutPortIndex a < clockwiseOutPortIndex b ↔ a.val < b.val := by
  have ha := a.isLt
  have hb := b.isLt
  unfold gridBoundaryLength at ha hb
  unfold clockwiseOutPortIndex
  split_ifs <;> omega

set_option maxHeartbeats 1000000 in
/-- Away from equality, an outgoing port precedes an incoming port exactly
when its original position precedes the incoming position. -/
theorem clockwiseOutPortIndex_lt_inPortIndex_iff {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (a b : GridBoundaryPosition m n)
    (hb0 : b.val ≠ 0) (hab : a ≠ b) :
    clockwiseOutPortIndex a < clockwiseInPortIndex b ↔ a.val < b.val := by
  have ha := a.isLt
  have hb := b.isLt
  have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  unfold gridBoundaryLength at ha hb
  unfold clockwiseOutPortIndex clockwiseInPortIndex gridBoundaryLength
  split_ifs <;> omega

set_option maxHeartbeats 1000000 in
/-- Reverse cross-order counterpart of
`clockwiseOutPortIndex_lt_inPortIndex_iff`. -/
theorem clockwiseInPortIndex_lt_outPortIndex_iff {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (a b : GridBoundaryPosition m n)
    (ha0 : a.val ≠ 0) (hab : a ≠ b) :
    clockwiseInPortIndex a < clockwiseOutPortIndex b ↔ a.val < b.val := by
  have ha := a.isLt
  have hb := b.isLt
  have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  unfold gridBoundaryLength at ha hb
  unfold clockwiseInPortIndex clockwiseOutPortIndex gridBoundaryLength
  split_ifs <;> omega

theorem clockwiseOutPortPosition_lt_iff {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (a b : GridBoundaryPosition m n) :
    (clockwiseOutPortPosition hm hn a).val <
        (clockwiseOutPortPosition hm hn b).val ↔ a.val < b.val := by
  simp only [clockwiseOutPortPosition_val]
  exact clockwiseOutPortIndex_lt_iff hm hn a b

theorem clockwiseOutPortPosition_lt_inPortPosition_iff {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (a b : GridBoundaryPosition m n)
    (hb0 : b.val ≠ 0) (hab : a ≠ b) :
    (clockwiseOutPortPosition hm hn a).val <
        (clockwiseInPortPosition hm hn b).val ↔ a.val < b.val := by
  simp only [clockwiseOutPortPosition_val, clockwiseInPortPosition_val]
  exact clockwiseOutPortIndex_lt_inPortIndex_iff hm hn a b hb0 hab

theorem clockwiseInPortPosition_lt_outPortPosition_iff {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (a b : GridBoundaryPosition m n)
    (ha0 : a.val ≠ 0) (hab : a ≠ b) :
    (clockwiseInPortPosition hm hn a).val <
        (clockwiseOutPortPosition hm hn b).val ↔ a.val < b.val := by
  simp only [clockwiseOutPortPosition_val, clockwiseInPortPosition_val]
  exact clockwiseInPortIndex_lt_outPortIndex_iff hm hn a b ha0 hab

theorem clockwiseOutPortPosition_injective {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Function.Injective (clockwiseOutPortPosition hm hn) := by
  intro a b hab
  apply Fin.ext
  by_contra hval
  rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
  · have := (clockwiseOutPortPosition_lt_iff hm hn a b).2 hlt
    rw [hab] at this
    exact (Nat.lt_irrefl _ this).elim
  · have := (clockwiseOutPortPosition_lt_iff hm hn b a).2 hgt
    rw [hab] at this
    exact (Nat.lt_irrefl _ this).elim

set_option maxHeartbeats 1000000 in
theorem clockwiseOutPortPosition_lt_last {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    (clockwiseOutPortPosition hm hn i).val + 1 <
      gridBoundaryLength (m + 2) (n + 2) := by
  rw [clockwiseOutPortPosition_val]
  have hi := i.isLt
  unfold clockwiseOutPortIndex gridBoundaryLength at *
  split_ifs <;> omega

/-- Strict order of clockwise distances from a base point depends only on the
cyclic order of the three distinct positions. -/
theorem cyclicForwardDistance_lt_iff_three_point_order {k : Nat} (hk : 0 < k)
    (s x y : Fin k) (hxs : x ≠ s) (hys : y ≠ s) :
    cyclicForwardDistance hk s x < cyclicForwardDistance hk s y ↔
      (s.val < x.val ∧ x.val < y.val) ∨
      (x.val < y.val ∧ y.val < s.val) ∨
      (y.val < s.val ∧ s.val < x.val) := by
  have hxs' : x.val ≠ s.val := fun h => hxs (Fin.ext h)
  have hys' : y.val ≠ s.val := fun h => hys (Fin.ext h)
  unfold cyclicForwardDistance
  split_ifs <;> omega

/-- The coordinate definition of `outerEdgeAtPosition` is the offset-zero edge
of its outgoing collar port. -/
theorem outerEdgeAtPosition_primalSym2 {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    (outerEdgeAtPosition hm hn i).primalSym2 =
      gridBoundaryOffsetEdge (by omega) (by omega)
        (clockwiseOutPortPosition hm hn i) 0 := by
  exact congrArg Subtype.val
    ((GridEdge.equivGridGraphEdgeSet (m + 2) (n + 2)).apply_symm_apply _)

theorem outerEdgeAtPosition_eq_gridBoundaryCoordinateEdge {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    outerEdgeAtPosition hm hn i =
      gridBoundaryCoordinateEdge (by omega) (by omega)
        (clockwiseOutPortPosition hm hn i) := by
  apply GridEdge.primalSym2_injective
  rw [outerEdgeAtPosition_primalSym2,
    gridBoundaryCoordinateEdge_primalSym2_eq_gridBoundaryOffsetEdge_zero]

/-- The bounded collar face incident to the outer-frame edge at an original
boundary position. -/
noncomputable def outerEdgeInnerFace {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : GridFace (m + 2) (n + 2) :=
  gridBoundaryEdgeInnerFace (by omega) (by omega)
    (clockwiseOutPortPosition hm hn i)

theorem outerEdgeInnerFace_eq_top {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) (htop : i.val < n - 1) :
    outerEdgeInnerFace hm hn i =
      .cell ⟨0, by omega⟩ ⟨i.val + 1, by omega⟩ := by
  simp [outerEdgeInnerFace, gridBoundaryEdgeInnerFace,
    clockwiseOutPortIndex, htop, gridBoundaryLength]
  split_ifs <;> simp_all <;> omega

theorem outerEdgeInnerFace_eq_right {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) (htop : ¬i.val < n - 1)
    (hright : i.val < n + m - 2) :
    outerEdgeInnerFace hm hn i =
      .cell ⟨i.val + 2 - n, by omega⟩ ⟨n, by omega⟩ := by
  have hbottom : i.val < m + 2 * n - 3 := by omega
  have hi := i.isLt
  unfold gridBoundaryLength at hi
  have hK : gridBoundaryLength m n = m + 2 * n - 3 + (m - 1) := by
    unfold gridBoundaryLength
    omega
  have hp : (clockwiseOutPortPosition hm hn i).val = i.val + 3 := by
    simp [clockwiseOutPortIndex, htop, hright]
  unfold outerEdgeInnerFace gridBoundaryEdgeInnerFace
  simp only [hp]
  have hK' : gridBoundaryLength (m + 2) (n + 2) =
      (m + 2 * n - 3) + (m - 1) + 8 := by
    unfold gridBoundaryLength
    omega
  split_ifs <;> simp_all [gridBoundaryLength, Fin.ext_iff] <;> omega

theorem outerEdgeInnerFace_eq_bottom {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) (hright : ¬i.val < n + m - 2)
    (hbottom : i.val < m + 2 * n - 3) :
    outerEdgeInnerFace hm hn i =
      .cell ⟨m, by omega⟩ ⟨m + 2 * n - 3 - i.val, by omega⟩ := by
  have htop : ¬i.val < n - 1 := by omega
  simp [outerEdgeInnerFace, gridBoundaryEdgeInnerFace,
    clockwiseOutPortIndex, htop, hright, hbottom, gridBoundaryLength]
  split_ifs <;> simp_all <;> omega

theorem outerEdgeInnerFace_eq_left {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) (hbottom : ¬i.val < m + 2 * n - 3) :
    outerEdgeInnerFace hm hn i =
      .cell ⟨gridBoundaryLength m n - i.val, by
        unfold gridBoundaryLength at *
        omega⟩ ⟨0, by omega⟩ := by
  have htop : ¬i.val < n - 1 := by omega
  have hright : ¬i.val < n + m - 2 := by omega
  simp [outerEdgeInnerFace, gridBoundaryEdgeInnerFace,
    clockwiseOutPortIndex, htop, hright, hbottom, gridBoundaryLength]
  split_ifs <;> simp_all <;> omega

/-- The outer-frame edge at a boundary position has `out` and its named collar
face as dual endpoints. -/
theorem outerEdgeAtPosition_hasDualEndpoints_out_innerFace {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    HasDualEndpoints (outerEdgeAtPosition hm hn i).dualEndpoints GridFace.out
      (outerEdgeInnerFace hm hn i) := by
  rw [outerEdgeAtPosition_eq_gridBoundaryCoordinateEdge]
  exact gridBoundaryCoordinateEdge_hasDualEndpoints_out_innerFace
    (by omega) (by omega) (clockwiseOutPortPosition hm hn i)

/-- An outer-frame edge cannot be a spoke or any other edge incident to an
embedded original-grid vertex. -/
theorem outerEdgeAtPosition_ne_edge_incident_collarEmbedding {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n)
    (x : GridVertex m n) (y : GridVertex (m + 2) (n + 2)) :
    (outerEdgeAtPosition hm hn i).primalSym2 ≠
      s(gridCollarEmbedding m n x, y) := by
  intro h
  rw [outerEdgeAtPosition_primalSym2, gridBoundaryOffsetEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · exact gridCollarEmbedding_not_boundary x
      (h.1 ▸ gridBoundaryVertex_isBoundary (by omega) (by omega)
        (cyclicOffset (gridBoundaryLength_pos (by omega) (by omega))
          (clockwiseOutPortPosition hm hn i) 0))
  · exact gridCollarEmbedding_not_boundary x
      (h.2 ▸ gridBoundaryVertex_isBoundary (by omega) (by omega)
        (cyclicOffset (gridBoundaryLength_pos (by omega) (by omega))
          (clockwiseOutPortPosition hm hn i) 1))

/-- Strict forward-distance order is preserved when original positions are
sent to outgoing collar ports and the upper endpoint is sent to its incoming
port. -/
theorem clockwisePort_forwardDistance_lt_iff {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (start finish i : GridBoundaryPosition m n)
    (hsf : start ≠ finish) (his : i ≠ start) (hif : i ≠ finish) :
    cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
        (clockwiseOutPortPosition hm hn start)
        (clockwiseOutPortPosition hm hn i) <
      cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
        (clockwiseOutPortPosition hm hn start)
        (clockwiseInPortPosition hm hn finish) ↔
      cyclicForwardDistance (gridBoundaryLength_pos hm hn) start i <
        cyclicForwardDistance (gridBoundaryLength_pos hm hn) start finish := by
  have hxi : clockwiseOutPortPosition hm hn i ≠
      clockwiseOutPortPosition hm hn start := fun h =>
    his (clockwiseOutPortPosition_injective hm hn h)
  have hsfv : start.val ≠ finish.val := fun h => hsf (Fin.ext h)
  have hisv : i.val ≠ start.val := fun h => his (Fin.ext h)
  have hifv : i.val ≠ finish.val := fun h => hif (Fin.ext h)
  by_cases hf0 : finish.val = 0
  · have hinval : (clockwiseInPortPosition hm hn finish).val =
        gridBoundaryLength (m + 2) (n + 2) - 1 := by
      rw [clockwiseInPortPosition_val]
      simp [clockwiseInPortIndex, hf0, gridBoundaryLength]
      omega
    have hys : clockwiseInPortPosition hm hn finish ≠
        clockwiseOutPortPosition hm hn start := by
      intro h
      have := congrArg Fin.val h
      rw [hinval] at this
      have hslt := clockwiseOutPortPosition_lt_last hm hn start
      omega
    rw [cyclicForwardDistance_lt_iff_three_point_order _ _ _ _ hxi hys,
      cyclicForwardDistance_lt_iff_three_point_order _ _ _ _ his hsf.symm]
    rw [hinval]
    have hilt := clockwiseOutPortPosition_lt_last hm hn i
    have hslt := clockwiseOutPortPosition_lt_last hm hn start
    rw [clockwiseOutPortPosition_lt_iff hm hn start i]
    omega
  · have hys : clockwiseInPortPosition hm hn finish ≠
        clockwiseOutPortPosition hm hn start := by
      intro h
      have hv := congrArg Fin.val h
      by_cases hlt : finish.val < start.val
      · have := (clockwiseInPortPosition_lt_outPortPosition_iff
          hm hn finish start hf0 hsf.symm).2 hlt
        omega
      · have hlt' : start.val < finish.val := by omega
        have := (clockwiseOutPortPosition_lt_inPortPosition_iff
          hm hn start finish hf0 hsf).2 hlt'
        omega
    rw [cyclicForwardDistance_lt_iff_three_point_order _ _ _ _ hxi hys,
      cyclicForwardDistance_lt_iff_three_point_order _ _ _ _ his hsf.symm]
    simp only [clockwiseOutPortPosition_lt_iff hm hn,
      clockwiseOutPortPosition_lt_inPortPosition_iff hm hn i finish hf0 hif,
      clockwiseInPortPosition_lt_outPortPosition_iff hm hn finish start hf0 hsf.symm]

/-- The canonical clockwise outer-frame arc corresponding to the cyclic
boundary interval from `i` to `j`. -/
noncomputable def clockwiseOuterArc {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) :
    (gridGraph (m + 2) (n + 2)).Walk
      (clockwiseOutPort hm hn i) (clockwiseInPort hm hn j) :=
  let hk := gridBoundaryLength_pos (show 2 ≤ m + 2 by omega) (show 2 ≤ n + 2 by omega)
  let s := clockwiseOutPortPosition hm hn i
  let e := clockwiseInPortPosition hm hn j
  (gridBoundaryForwardWalk (by omega) (by omega) s
    (cyclicForwardDistance hk s e)).copy
      (boundaryVertex_clockwiseOutPortPosition hm hn i) (by
        rw [cyclicOffset_forwardDistance]
        exact boundaryVertex_clockwiseInPortPosition hm hn j)

/-- Exact edge list of the canonical clockwise collar arc. -/
@[simp] theorem edges_clockwiseOuterArc {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n) :
    (clockwiseOuterArc hm hn i j).edges =
      (List.range (cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
        (clockwiseOutPortPosition hm hn i) (clockwiseInPortPosition hm hn j))).map
        (gridBoundaryOffsetEdge (by omega) (by omega)
          (clockwiseOutPortPosition hm hn i)) := by
  unfold clockwiseOuterArc
  simp

/-- Membership of a named outer-frame edge in the canonical clockwise arc. -/
theorem mem_edges_clockwiseOuterArc_iff {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n) {t : Nat}
    (ht : t < gridBoundaryLength (m + 2) (n + 2)) :
    gridBoundaryOffsetEdge (by omega) (by omega)
        (clockwiseOutPortPosition hm hn i) t ∈
        (clockwiseOuterArc hm hn i j).edges ↔
      t < cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
        (clockwiseOutPortPosition hm hn i) (clockwiseInPortPosition hm hn j) := by
  unfold clockwiseOuterArc
  rw [Walk.edges_copy]
  exact mem_edges_gridBoundaryForwardWalk_iff (by omega) (by omega)
    (clockwiseOutPortPosition hm hn i)
    (hd := Nat.le_of_lt (cyclicForwardDistance_lt _ _ _)) ht

private theorem gridBoundaryOffsetEdge_forwardDistance {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (a b : GridBoundaryPosition m n) :
    gridBoundaryOffsetEdge hm hn a
        (cyclicForwardDistance (gridBoundaryLength_pos hm hn) a b) =
      gridBoundaryOffsetEdge hm hn b 0 := by
  unfold gridBoundaryOffsetEdge
  let hk := gridBoundaryLength_pos hm hn
  let d := cyclicForwardDistance hk a b
  have hpos : cyclicOffset hk a d = b := cyclicOffset_forwardDistance hk a b
  change s(gridBoundaryVertex hm hn (cyclicOffset hk a d),
      gridBoundaryVertex hm hn (cyclicOffset hk a (d + 1))) = _
  rw [hpos]
  rw [show cyclicOffset (gridBoundaryLength_pos hm hn) b 0 = b by
    apply Fin.ext
    simp [cyclicOffset, Nat.mod_eq_of_lt b.isLt]]
  rw [Sym2.eq_iff]
  left
  refine ⟨rfl, congrArg (gridBoundaryVertex hm hn) ?_⟩
  rw [← hpos]
  apply Fin.ext
  change (a.val + (d + 1)) % gridBoundaryLength m n =
    ((a.val + d) % gridBoundaryLength m n + 1) % gridBoundaryLength m n
  rw [show a.val + (d + 1) = (a.val + d) + 1 by omega, Nat.add_mod]
  simp

/-- The outer edge attached to a non-endpoint original boundary position is in
the canonical clockwise outer arc exactly on the corresponding open original
sector. -/
theorem outerEdgeAtPosition_mem_clockwiseOuterArc_iff_openCyclicSector
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (start finish i : GridBoundaryPosition m n)
    (hsf : start ≠ finish) (his : i ≠ start) (hif : i ≠ finish) :
    (outerEdgeAtPosition hm hn i).primalSym2 ∈
        (clockwiseOuterArc hm hn start finish).edges ↔
      OpenCyclicSector (gridBoundaryLength_pos hm hn) start finish i := by
  let t := cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
    (clockwiseOutPortPosition hm hn start) (clockwiseOutPortPosition hm hn i)
  have ht : t < gridBoundaryLength (m + 2) (n + 2) :=
    cyclicForwardDistance_lt _ _ _
  have hedge : (outerEdgeAtPosition hm hn i).primalSym2 =
      gridBoundaryOffsetEdge (by omega) (by omega)
        (clockwiseOutPortPosition hm hn start) t := by
    rw [outerEdgeAtPosition_primalSym2]
    exact (gridBoundaryOffsetEdge_forwardDistance (by omega) (by omega)
      (clockwiseOutPortPosition hm hn start)
      (clockwiseOutPortPosition hm hn i)).symm
  rw [hedge, mem_edges_clockwiseOuterArc_iff hm hn start finish ht]
  rw [clockwisePort_forwardDistance_lt_iff hm hn start finish i hsf his hif]
  unfold OpenCyclicSector
  have hpos := cyclicForwardDistance_pos_of_ne (gridBoundaryLength_pos hm hn) his.symm
  tauto


/-- The counterclockwise outer-frame arc, defined as the reverse of the
clockwise complementary interval. -/
noncomputable def counterclockwiseOuterArc {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) :
    (gridGraph (m + 2) (n + 2)).Walk
      (clockwiseInPort hm hn i) (clockwiseOutPort hm hn j) :=
  (clockwiseOuterArc hm hn j i).reverse

theorem clockwiseOuterArc_isPath {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) : (clockwiseOuterArc hm hn i j).IsPath := by
  unfold clockwiseOuterArc
  rw [Walk.isPath_copy]
  apply gridBoundaryForwardWalk_isPath
  apply cyclicForwardDistance_lt

theorem counterclockwiseOuterArc_isPath {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) :
    (counterclockwiseOuterArc hm hn i j).IsPath :=
  (clockwiseOuterArc_isPath hm hn j i).reverse

theorem clockwiseOuterArc_on_boundary {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) {x : GridVertex (m + 2) (n + 2)}
    (hx : x ∈ (clockwiseOuterArc hm hn i j).support) : IsGridBoundary x := by
  unfold clockwiseOuterArc at hx
  rw [Walk.support_copy, mem_support_gridBoundaryForwardWalk_iff] at hx
  obtain ⟨t, -, rfl⟩ := hx
  apply gridBoundaryVertex_isBoundary

theorem counterclockwiseOuterArc_on_boundary {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n)
    {x : GridVertex (m + 2) (n + 2)}
    (hx : x ∈ (counterclockwiseOuterArc hm hn i j).support) : IsGridBoundary x := by
  unfold counterclockwiseOuterArc at hx
  rw [Walk.support_reverse, List.mem_reverse] at hx
  exact clockwiseOuterArc_on_boundary hm hn j i hx

/-- A selected perimeter arc in the collar.  At a corner, `startPort` and
`endPort` record which of the two outward radial edges was selected. -/
structure GridCollarArc {m n : Nat} (a b : GridVertex m n) where
  startPort : GridVertex (m + 2) (n + 2)
  endPort : GridVertex (m + 2) (n + 2)
  arc : (gridGraph (m + 2) (n + 2)).Walk startPort endPort
  start_spoke : (gridGraph (m + 2) (n + 2)).Adj
    (gridCollarEmbedding m n a) startPort
  end_spoke : (gridGraph (m + 2) (n + 2)).Adj
    (gridCollarEmbedding m n b) endPort
  arc_isPath : arc.IsPath
  arc_on_outer_frame : ∀ x ∈ arc.support, IsGridBoundary x

namespace GridCollarArc

variable {m n : Nat} {a b : GridVertex m n}

/-- Canonical collar arc following the clockwise cyclic boundary interval. -/
noncomputable def clockwise {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) :
    GridCollarArc (gridBoundaryVertex hm hn i) (gridBoundaryVertex hm hn j) where
  startPort := clockwiseOutPort hm hn i
  endPort := clockwiseInPort hm hn j
  arc := clockwiseOuterArc hm hn i j
  start_spoke := clockwiseOutPort_spoke hm hn i
  end_spoke := clockwiseInPort_spoke hm hn j
  arc_isPath := clockwiseOuterArc_isPath hm hn i j
  arc_on_outer_frame := fun _ hx => clockwiseOuterArc_on_boundary hm hn i j hx

/-- Canonical collar arc following the counterclockwise cyclic boundary
interval. -/
noncomputable def counterclockwise {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) :
    GridCollarArc (gridBoundaryVertex hm hn i) (gridBoundaryVertex hm hn j) where
  startPort := clockwiseInPort hm hn i
  endPort := clockwiseOutPort hm hn j
  arc := counterclockwiseOuterArc hm hn i j
  start_spoke := clockwiseInPort_spoke hm hn i
  end_spoke := clockwiseOutPort_spoke hm hn j
  arc_isPath := counterclockwiseOuterArc_isPath hm hn i j
  arc_on_outer_frame := fun _ hx => counterclockwiseOuterArc_on_boundary hm hn i j hx

/-- Either canonical cyclic interval between two boundary positions. -/
inductive CanonicalChoice where
  | clockwise
  | counterclockwise
  deriving DecidableEq

/-- Select one of the two canonical outer-frame intervals. -/
noncomputable def canonical (choice : CanonicalChoice) {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n) :
    GridCollarArc (gridBoundaryVertex hm hn i) (gridBoundaryVertex hm hn j) :=
  match choice with
  | .clockwise => clockwise hm hn i j
  | .counterclockwise => counterclockwise hm hn i j

/-- No vertex of the outer arc belongs to the embedded original grid. -/
theorem embedded_not_mem_arc (A : GridCollarArc a b) (v : GridVertex m n) :
    gridCollarEmbedding m n v ∉ A.arc.support := by
  intro hv
  exact gridCollarEmbedding_not_boundary v (A.arc_on_outer_frame _ hv)

/-- Exact cyclic-interval support of the canonical clockwise arc. -/
theorem mem_clockwise_arc_iff {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) (x : GridVertex (m + 2) (n + 2)) :
    x ∈ (clockwise hm hn i j).arc.support ↔
      ∃ t ≤ cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
          (clockwiseOutPortPosition hm hn i) (clockwiseInPortPosition hm hn j),
        x = gridBoundaryVertex (by omega) (by omega)
          (cyclicOffset (gridBoundaryLength_pos (by omega) (by omega))
            (clockwiseOutPortPosition hm hn i) t) := by
  unfold clockwise clockwiseOuterArc
  rw [Walk.support_copy, mem_support_gridBoundaryForwardWalk_iff]

/-- Counterclockwise support is the complementary clockwise cyclic interval,
with its order reversed. -/
theorem mem_counterclockwise_arc_iff {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) (x : GridVertex (m + 2) (n + 2)) :
    x ∈ (counterclockwise hm hn i j).arc.support ↔
      ∃ t ≤ cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
          (clockwiseOutPortPosition hm hn j) (clockwiseInPortPosition hm hn i),
        x = gridBoundaryVertex (by omega) (by omega)
          (cyclicOffset (gridBoundaryLength_pos (by omega) (by omega))
            (clockwiseOutPortPosition hm hn j) t) := by
  unfold counterclockwise counterclockwiseOuterArc
  rw [Walk.support_reverse, List.mem_reverse]
  exact mem_clockwise_arc_iff hm hn j i x

/-- The cyclic interval represented by a canonical choice. -/
def CanonicalInterval (choice : CanonicalChoice) {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n)
    (x : GridVertex (m + 2) (n + 2)) : Prop :=
  match choice with
  | .clockwise =>
      ∃ t ≤ cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
          (clockwiseOutPortPosition hm hn i) (clockwiseInPortPosition hm hn j),
        x = gridBoundaryVertex (by omega) (by omega)
          (cyclicOffset (gridBoundaryLength_pos (by omega) (by omega))
            (clockwiseOutPortPosition hm hn i) t)
  | .counterclockwise =>
      ∃ t ≤ cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
          (clockwiseOutPortPosition hm hn j) (clockwiseInPortPosition hm hn i),
        x = gridBoundaryVertex (by omega) (by omega)
          (cyclicOffset (gridBoundaryLength_pos (by omega) (by omega))
            (clockwiseOutPortPosition hm hn j) t)

/-- Selecting a canonical arc selects exactly the corresponding cyclic
boundary interval. -/
theorem mem_canonical_arc_iff (choice : CanonicalChoice) {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n)
    (x : GridVertex (m + 2) (n + 2)) :
    x ∈ (canonical choice hm hn i j).arc.support ↔
      CanonicalInterval choice hm hn i j x := by
  cases choice
  · exact mem_clockwise_arc_iff hm hn i j x
  · exact mem_counterclockwise_arc_iff hm hn i j x

theorem clockwise_arc_disjoint_embedded_grid {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n)
    (v : GridVertex m n) :
    gridCollarEmbedding m n v ∉ (clockwise hm hn i j).arc.support :=
  (clockwise hm hn i j).embedded_not_mem_arc v

theorem counterclockwise_arc_disjoint_embedded_grid {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n)
    (v : GridVertex m n) :
    gridCollarEmbedding m n v ∉ (counterclockwise hm hn i j).arc.support :=
  (counterclockwise hm hn i j).embedded_not_mem_arc v

/-- The route from the translated end of the crosscut back to its translated
start: radial edge, selected outer arc in reverse, radial edge. -/
def closingWalk (A : GridCollarArc a b) :
    (gridGraph (m + 2) (n + 2)).Walk
      (gridCollarEmbedding m n b) (gridCollarEmbedding m n a) :=
  (Walk.cons A.end_spoke A.arc.reverse).concat A.start_spoke.symm

/-- Exact edge decomposition of the route through the collar. -/
@[simp] theorem edges_closingWalk (A : GridCollarArc a b) :
    A.closingWalk.edges =
      s(gridCollarEmbedding m n b, A.endPort) ::
        A.arc.edges.reverse ++ [s(A.startPort, gridCollarEmbedding m n a)] := by
  simp [closingWalk]

@[simp] theorem mem_support_closingWalk_iff (A : GridCollarArc a b)
    (x : GridVertex (m + 2) (n + 2)) :
    x ∈ A.closingWalk.support ↔
      x = gridCollarEmbedding m n b ∨ x ∈ A.arc.support ∨
        x = gridCollarEmbedding m n a := by
  simp [closingWalk]

/-- Apart from its two endpoints, the closing route is entirely on the outer
frame. -/
theorem boundary_of_mem_closingWalk_of_ne_endpoints (A : GridCollarArc a b)
    {x : GridVertex (m + 2) (n + 2)} (hx : x ∈ A.closingWalk.support)
    (hxb : x ≠ gridCollarEmbedding m n b)
    (hxa : x ≠ gridCollarEmbedding m n a) : IsGridBoundary x := by
  rw [mem_support_closingWalk_iff] at hx
  rcases hx with h | h | h
  · exact (hxb h).elim
  · exact A.arc_on_outer_frame x h
  · exact (hxa h).elim

/-- Every vertex of the selected arc has a position in the clockwise boundary
numbering of the collar. -/
theorem exists_boundaryPosition_of_mem_arc (A : GridCollarArc a b)
    {x : GridVertex (m + 2) (n + 2)} (hx : x ∈ A.arc.support) :
    ∃ i : GridBoundaryPosition (m + 2) (n + 2),
      gridBoundaryVertex (by omega) (by omega) i = x :=
  exists_gridBoundaryPosition (by omega) (by omega) x
    (A.arc_on_outer_frame x hx)

/-- The radial edges and a simple outer arc form a simple closing path when
the crosscut endpoints are distinct. -/
theorem closingWalk_isPath (A : GridCollarArc a b) (hab : a ≠ b) :
    A.closingWalk.IsPath := by
  rw [closingWalk, Walk.concat_isPath_iff, Walk.cons_isPath_iff]
  refine ⟨⟨A.arc_isPath.reverse, ?_⟩, ?_⟩
  · intro hb
    rw [Walk.support_reverse] at hb
    exact gridCollarEmbedding_not_boundary b
      (A.arc_on_outer_frame _ (by simpa using hb))
  · intro ha
    simp only [Walk.support_cons, List.mem_cons, Walk.support_reverse,
      List.mem_reverse] at ha
    rcases ha with heq | ha
    · apply hab
      exact (gridCollarEmbedding m n).injective heq
    · exact gridCollarEmbedding_not_boundary a (A.arc_on_outer_frame _ ha)

/-- Translate a walk in the original grid into the collar. -/
def mapWalk {u v : GridVertex m n} (p : (gridGraph m n).Walk u v) :
    (gridGraph (m + 2) (n + 2)).Walk
      (gridCollarEmbedding m n u) (gridCollarEmbedding m n v) :=
  p.map (gridCollarGraphEmbedding m n).toHom

/-- An outer-frame edge is not used by a walk mapped from the central grid. -/
theorem outerEdgeAtPosition_not_mem_edges_mapWalk {u v : GridVertex m n}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n)
    (p : (gridGraph m n).Walk u v) :
    (outerEdgeAtPosition hm hn i).primalSym2 ∉ (mapWalk p).edges := by
  intro he
  change (outerEdgeAtPosition hm hn i).primalSym2 ∈
    (p.map (gridCollarGraphEmbedding m n).toHom).edges at he
  rw [Walk.edges_map, List.mem_map] at he
  obtain ⟨e, -, he⟩ := he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [Sym2.map_mk] at he
      exact outerEdgeAtPosition_ne_edge_incident_collarEmbedding hm hn i x
        (gridCollarEmbedding m n y) he.symm

@[simp] theorem support_mapWalk {u v : GridVertex m n}
    (p : (gridGraph m n).Walk u v) :
    (mapWalk p).support = p.support.map (gridCollarEmbedding m n) := by
  change (p.map (gridCollarGraphEmbedding m n).toHom).support = _
  exact Walk.support_map _ _

/-- The translated crosscut and its closing route meet only at their two
common endpoints. -/
theorem mem_support_mapWalk_and_closingWalk_iff
    (A : GridCollarArc a b) (p : (gridGraph m n).Walk a b)
    (x : GridVertex (m + 2) (n + 2)) :
    x ∈ (mapWalk p).support ∧ x ∈ A.closingWalk.support ↔
      x = gridCollarEmbedding m n a ∨ x = gridCollarEmbedding m n b := by
  constructor
  · rintro ⟨hp, hq⟩
    rw [mem_support_closingWalk_iff] at hq
    rcases hq with rfl | houter | rfl
    · exact Or.inr rfl
    · rw [support_mapWalk, List.mem_map] at hp
      obtain ⟨v, -, rfl⟩ := hp
      exact (gridCollarEmbedding_not_boundary v
        (A.arc_on_outer_frame _ houter)).elim
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · refine ⟨?_, by simp⟩
      rw [support_mapWalk, List.mem_map]
      exact ⟨a, p.start_mem_support, rfl⟩
    · refine ⟨?_, by simp⟩
      rw [support_mapWalk, List.mem_map]
      exact ⟨b, p.end_mem_support, rfl⟩

/-- Closed walk obtained by following the translated crosscut and then the
selected route through the outer collar. -/
def cycleWalk (A : GridCollarArc a b) (p : (gridGraph m n).Walk a b) :
    (gridGraph (m + 2) (n + 2)).Walk
      (gridCollarEmbedding m n b) (gridCollarEmbedding m n b) :=
  A.closingWalk.append (mapWalk p)

/-- Exact edge decomposition of a collar-closed walk. -/
@[simp] theorem edges_cycleWalk (A : GridCollarArc a b)
    (p : (gridGraph m n).Walk a b) :
    (A.cycleWalk p).edges =
      s(gridCollarEmbedding m n b, A.endPort) ::
        A.arc.edges.reverse ++
          [s(A.startPort, gridCollarEmbedding m n a)] ++ (mapWalk p).edges := by
  simp [cycleWalk]

/-- A named outer-frame edge belongs to a collar closure exactly when it
belongs to the selected outer arc. -/
theorem outerEdgeAtPosition_mem_edges_cycleWalk_iff
    (A : GridCollarArc a b) (p : (gridGraph m n).Walk a b)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    (outerEdgeAtPosition hm hn i).primalSym2 ∈ (A.cycleWalk p).edges ↔
      (outerEdgeAtPosition hm hn i).primalSym2 ∈ A.arc.edges := by
  have hend := outerEdgeAtPosition_ne_edge_incident_collarEmbedding hm hn i b A.endPort
  have hstart := outerEdgeAtPosition_ne_edge_incident_collarEmbedding hm hn i a A.startPort
  have hstart' : (outerEdgeAtPosition hm hn i).primalSym2 ≠
      s(A.startPort, gridCollarEmbedding m n a) := by
    intro h
    apply hstart
    rw [h, Sym2.eq_iff]
    exact Or.inr ⟨rfl, rfl⟩
  have hmap := outerEdgeAtPosition_not_mem_edges_mapWalk hm hn i p
  rw [edges_cycleWalk]
  simp [hend, hstart', hmap]

/-- The collar closure of a simple crosscut is a simple cycle.  The proof is
purely combinatorial: the translated path is internal, while the middle of the
closing path is on the outer frame. -/
theorem cycleWalk_isCycle (A : GridCollarArc a b)
    (p : (gridGraph m n).Walk a b) (hp : p.IsPath) (hab : a ≠ b) :
    (cycleWalk A p).IsCycle := by
  let r := A.arc.reverse.concat A.start_spoke.symm
  have hclose : A.closingWalk.IsPath := A.closingWalk_isPath hab
  have hr : r.IsPath := by
    exact hclose.of_cons
  have hmap : (mapWalk p).IsPath := by
    exact Walk.IsPath.map
      (gridCollarGraphEmbedding m n).injective hp
  have hrest : (r.append (mapWalk p)).IsPath := by
    rw [Walk.isPath_def, Walk.support_append]
    apply hr.support_nodup.append hmap.support_nodup.tail
    intro x hxr hxp
    have hxpa : x ≠ gridCollarEmbedding m n a := by
      intro hxa
      subst x
      have hn := hmap.support_nodup
      rw [← Walk.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 hxp
    have hxr' : x ∈ A.arc.support ∨ x = gridCollarEmbedding m n a := by
      simpa [r] using hxr
    rcases hxr' with houter | hxa
    · have hxpfull : x ∈ (mapWalk p).support := List.mem_of_mem_tail hxp
      rw [support_mapWalk, List.mem_map] at hxpfull
      obtain ⟨v, -, rfl⟩ := hxpfull
      exact gridCollarEmbedding_not_boundary v (A.arc_on_outer_frame _ houter)
    · exact hxpa hxa
  have hfirst_not_r :
      s(gridCollarEmbedding m n b, A.endPort) ∉ r.edges := by
    have ht := hclose.isTrail
    rw [closingWalk, Walk.concat_cons, Walk.isTrail_cons] at ht
    exact ht.2
  have hfirst_not_map :
      s(gridCollarEmbedding m n b, A.endPort) ∉ (mapWalk p).edges := by
    intro he
    have hport : A.endPort ∈ (mapWalk p).support :=
      (mapWalk p).snd_mem_support_of_mem_edges he
    rw [support_mapWalk, List.mem_map] at hport
    obtain ⟨v, -, hv⟩ := hport
    exact gridCollarEmbedding_ne_of_boundary v
      (A.arc_on_outer_frame A.endPort A.arc.end_mem_support) hv
  change (Walk.cons A.end_spoke (r.append (mapWalk p))).IsCycle
  rw [Walk.cons_isCycle_iff]
  refine ⟨hrest, ?_⟩
  simp only [Walk.edges_append, List.mem_append, not_or]
  exact ⟨hfirst_not_r, hfirst_not_map⟩

/-- Exact vertex support of the collar closure. -/
theorem mem_support_cycleWalk_iff (A : GridCollarArc a b)
    (p : (gridGraph m n).Walk a b) (x : GridVertex (m + 2) (n + 2)) :
    x ∈ (cycleWalk A p).support ↔
      (∃ v ∈ p.support, x = gridCollarEmbedding m n v) ∨ x ∈ A.arc.support := by
  rw [cycleWalk, Walk.mem_support_append_iff, mem_support_closingWalk_iff,
    support_mapWalk, List.mem_map]
  constructor
  · rintro ((rfl | hx | rfl) | ⟨v, hv, hvx⟩)
    · exact Or.inl ⟨b, p.end_mem_support, rfl⟩
    · exact Or.inr hx
    · exact Or.inl ⟨a, p.start_mem_support, rfl⟩
    · exact Or.inl ⟨v, hv, hvx.symm⟩
  · rintro (⟨v, hv, rfl⟩ | hx)
    · exact Or.inr ⟨v, hv, rfl⟩
    · exact Or.inl (Or.inr (Or.inl hx))

/-- A collar closure contains exactly the translated vertices of the original
grid that occur on the crosscut. -/
theorem mem_cycleWalk_and_collar_range_iff (A : GridCollarArc a b)
    (p : (gridGraph m n).Walk a b) (v : GridVertex m n) :
    gridCollarEmbedding m n v ∈ (cycleWalk A p).support ↔ v ∈ p.support := by
  rw [mem_support_cycleWalk_iff]
  constructor
  · rintro (⟨w, hw, heq⟩ | houter)
    · exact (gridCollarEmbedding m n).injective heq ▸ hw
    · exact (gridCollarEmbedding_not_boundary v
        (A.arc_on_outer_frame _ houter)).elim
  · intro hv
    exact Or.inl ⟨v, hv, rfl⟩

end GridCollarArc

/-- A simple grid path between distinct boundary vertices whose only boundary
contacts are its endpoints. -/
structure GridCrosscut (m n : Nat) where
  start : GridVertex m n
  finish : GridVertex m n
  path : (gridGraph m n).Walk start finish
  isPath : path.IsPath
  start_ne_finish : start ≠ finish
  start_boundary : IsGridBoundary start
  finish_boundary : IsGridBoundary finish
  boundary_contact : ∀ v ∈ path.support,
    IsGridBoundary v → v = start ∨ v = finish

namespace GridCrosscut

variable {m n : Nat}

/-- Boundary position of the initial endpoint of a crosscut. -/
noncomputable def startPosition (P : GridCrosscut m n) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    GridBoundaryPosition m n :=
  (gridBoundaryEquiv hm hn).symm ⟨P.start, P.start_boundary⟩

/-- Boundary position of the terminal endpoint of a crosscut. -/
noncomputable def finishPosition (P : GridCrosscut m n) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    GridBoundaryPosition m n :=
  (gridBoundaryEquiv hm hn).symm ⟨P.finish, P.finish_boundary⟩

@[simp] theorem boundaryVertex_startPosition (P : GridCrosscut m n)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    gridBoundaryVertex hm hn (P.startPosition hm hn) = P.start := by
  exact congrArg Subtype.val
    ((gridBoundaryEquiv hm hn).apply_symm_apply ⟨P.start, P.start_boundary⟩)

@[simp] theorem boundaryVertex_finishPosition (P : GridCrosscut m n)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    gridBoundaryVertex hm hn (P.finishPosition hm hn) = P.finish := by
  exact congrArg Subtype.val
    ((gridBoundaryEquiv hm hn).apply_symm_apply ⟨P.finish, P.finish_boundary⟩)

/-- The canonical clockwise collar arc of a crosscut. -/
noncomputable def clockwiseArc (P : GridCrosscut m n) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    GridCollarArc P.start P.finish where
  startPort := clockwiseOutPort hm hn (P.startPosition hm hn)
  endPort := clockwiseInPort hm hn (P.finishPosition hm hn)
  arc := clockwiseOuterArc hm hn (P.startPosition hm hn) (P.finishPosition hm hn)
  start_spoke := by
    rw [← P.boundaryVertex_startPosition hm hn]
    exact clockwiseOutPort_spoke hm hn (P.startPosition hm hn)
  end_spoke := by
    rw [← P.boundaryVertex_finishPosition hm hn]
    exact clockwiseInPort_spoke hm hn (P.finishPosition hm hn)
  arc_isPath := clockwiseOuterArc_isPath hm hn _ _
  arc_on_outer_frame := fun _ hx => clockwiseOuterArc_on_boundary hm hn _ _ hx

/-- The endpoint transports in `clockwiseArc` do not alter its outer arc. -/
@[simp] theorem edges_clockwiseArc (P : GridCrosscut m n)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (P.clockwiseArc hm hn).arc.edges =
      (clockwiseOuterArc hm hn (P.startPosition hm hn)
        (P.finishPosition hm hn)).edges := rfl

/-- The canonical counterclockwise collar arc of a crosscut. -/
noncomputable def counterclockwiseArc (P : GridCrosscut m n)
    (hm : 2 ≤ m) (hn : 2 ≤ n) : GridCollarArc P.start P.finish where
  startPort := clockwiseInPort hm hn (P.startPosition hm hn)
  endPort := clockwiseOutPort hm hn (P.finishPosition hm hn)
  arc := counterclockwiseOuterArc hm hn (P.startPosition hm hn) (P.finishPosition hm hn)
  start_spoke := by
    rw [← P.boundaryVertex_startPosition hm hn]
    exact clockwiseInPort_spoke hm hn (P.startPosition hm hn)
  end_spoke := by
    rw [← P.boundaryVertex_finishPosition hm hn]
    exact clockwiseOutPort_spoke hm hn (P.finishPosition hm hn)
  arc_isPath := counterclockwiseOuterArc_isPath hm hn _ _
  arc_on_outer_frame := fun _ hx => counterclockwiseOuterArc_on_boundary hm hn _ _ hx

/-- Select either canonical cyclic boundary interval without supplying an arc. -/
noncomputable def canonicalArc (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    GridCollarArc P.start P.finish :=
  match choice with
  | .clockwise => P.clockwiseArc hm hn
  | .counterclockwise => P.counterclockwiseArc hm hn

/-- Closed walk obtained from either canonical boundary interval. -/
noncomputable def canonicalClosedWalk (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (gridGraph (m + 2) (n + 2)).Walk
      (gridCollarEmbedding m n P.finish) (gridCollarEmbedding m n P.finish) :=
  (P.canonicalArc choice hm hn).cycleWalk P.path

/-- Exact edge decomposition of a canonical crosscut closure. -/
@[simp] theorem edges_canonicalClosedWalk (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (P.canonicalClosedWalk choice hm hn).edges =
      s(gridCollarEmbedding m n P.finish,
          (P.canonicalArc choice hm hn).endPort) ::
        (P.canonicalArc choice hm hn).arc.edges.reverse ++
          [s((P.canonicalArc choice hm hn).startPort,
            gridCollarEmbedding m n P.start)] ++
          (GridCollarArc.mapWalk P.path).edges := by
  simp [canonicalClosedWalk]

/-- For the clockwise choice, the canonical arc has exactly the underlying
clockwise outer-arc edges, without endpoint casts. -/
@[simp] theorem edges_canonicalArc_clockwise (P : GridCrosscut m n)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (P.canonicalArc .clockwise hm hn).arc.edges =
      (clockwiseOuterArc hm hn (P.startPosition hm hn)
        (P.finishPosition hm hn)).edges := by
  rfl

/-- Membership of a non-endpoint outer edge in the clockwise canonical closure
is exactly membership in the corresponding clockwise outer arc. -/
theorem outerEdgeAtPosition_mem_canonicalClosedWalk_clockwise_iff_outerArc
    (P : GridCrosscut m n) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) :
    (outerEdgeAtPosition hm hn i).primalSym2 ∈
        (P.canonicalClosedWalk .clockwise hm hn).edges ↔
      (outerEdgeAtPosition hm hn i).primalSym2 ∈
        (clockwiseOuterArc hm hn (P.startPosition hm hn)
          (P.finishPosition hm hn)).edges := by
  exact (P.canonicalArc .clockwise hm hn).outerEdgeAtPosition_mem_edges_cycleWalk_iff
    P.path hm hn i |>.trans (by rw [P.edges_canonicalArc_clockwise hm hn])

/-- Both canonical closures are simple cycles. -/
theorem canonicalClosedWalk_isCycle (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (P.canonicalClosedWalk choice hm hn).IsCycle :=
  (P.canonicalArc choice hm hn).cycleWalk_isCycle
    P.path P.isPath P.start_ne_finish

/-- A canonical closure intersects the embedded original grid exactly in the
given crosscut. -/
theorem mem_canonicalClosedWalk_collar_iff (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (v : GridVertex m n) :
    gridCollarEmbedding m n v ∈ (P.canonicalClosedWalk choice hm hn).support ↔
      v ∈ P.path.support :=
  (P.canonicalArc choice hm hn).mem_cycleWalk_and_collar_range_iff P.path v

/-- The no-internal-boundary-contact hypothesis gives exactly the two original
boundary contacts for either canonical closure. -/
theorem mem_canonicalClosedWalk_of_original_boundary_iff (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (v : GridVertex m n) (hv : IsGridBoundary v) :
    gridCollarEmbedding m n v ∈ (P.canonicalClosedWalk choice hm hn).support ↔
      v = P.start ∨ v = P.finish := by
  rw [P.mem_canonicalClosedWalk_collar_iff choice hm hn]
  constructor
  · intro h
    exact P.boundary_contact v h hv
  · rintro (rfl | rfl)
    · exact P.path.start_mem_support
    · exact P.path.end_mem_support

/-- The chosen canonical outer interval is internally disjoint from every
embedded original-grid vertex. -/
theorem canonicalArc_disjoint_embedded_grid (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (v : GridVertex m n) :
    gridCollarEmbedding m n v ∉ (P.canonicalArc choice hm hn).arc.support :=
  (P.canonicalArc choice hm hn).embedded_not_mem_arc v

/-- Close a crosscut using a selected arc of the outer collar. -/
def closedWalk (P : GridCrosscut m n) (A : GridCollarArc P.start P.finish) :
    (gridGraph (m + 2) (n + 2)).Walk
      (gridCollarEmbedding m n P.finish) (gridCollarEmbedding m n P.finish) :=
  A.cycleWalk P.path

/-- A crosscut closed along a selected simple perimeter arc is a simple cycle. -/
theorem closedWalk_isCycle (P : GridCrosscut m n)
    (A : GridCollarArc P.start P.finish) : (P.closedWalk A).IsCycle :=
  A.cycleWalk_isCycle P.path P.isPath P.start_ne_finish

/-- The closed cycle meets the translated original grid exactly in the
translated crosscut. -/
theorem mem_closedWalk_collar_iff (P : GridCrosscut m n)
    (A : GridCollarArc P.start P.finish) (v : GridVertex m n) :
    gridCollarEmbedding m n v ∈ (P.closedWalk A).support ↔ v ∈ P.path.support :=
  A.mem_cycleWalk_and_collar_range_iff P.path v

/-- Consequently, among translated vertices of the original boundary, the
cycle has exactly the two prescribed contacts. -/
theorem mem_closedWalk_of_original_boundary_iff (P : GridCrosscut m n)
    (A : GridCollarArc P.start P.finish) (v : GridVertex m n)
    (hv : IsGridBoundary v) :
    gridCollarEmbedding m n v ∈ (P.closedWalk A).support ↔
      v = P.start ∨ v = P.finish := by
  rw [P.mem_closedWalk_collar_iff A]
  constructor
  · intro h
    exact P.boundary_contact v h hv
  · rintro (rfl | rfl)
    · exact P.path.start_mem_support
    · exact P.path.end_mem_support

/-- Full support description: translated crosscut vertices together with the
chosen outer perimeter arc. -/
theorem mem_closedWalk_iff (P : GridCrosscut m n)
    (A : GridCollarArc P.start P.finish)
    (x : GridVertex (m + 2) (n + 2)) :
    x ∈ (P.closedWalk A).support ↔
      (∃ v ∈ P.path.support, x = gridCollarEmbedding m n v) ∨
        x ∈ A.arc.support :=
  A.mem_support_cycleWalk_iff P.path x

/-- Faces cut off from the unbounded face by the combinatorially constructed
cycle, using the dual reachability API.  No nonemptiness claim is made here. -/
def interiorFaces (P : GridCrosscut m n)
    (A : GridCollarArc P.start P.finish) : Finset (GridFace (m + 2) (n + 2)) :=
  cycleInteriorFaces (P.closedWalk A)

@[simp] theorem out_not_mem_interiorFaces (P : GridCrosscut m n)
    (A : GridCollarArc P.start P.finish) :
    GridFace.out ∉ P.interiorFaces A :=
  out_not_mem_cycleInteriorFaces (P.closedWalk A)

end GridCrosscut

end GridGraphs
